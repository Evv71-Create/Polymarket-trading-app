/**
 * Signal Engine
 * Fixes: Set-based dedup with TTL, dry run mode, audit trail integration
 */

const fs = require('fs');
const path = require('path');
const WAL = require('./wal');
const ApiCache = require('./api-cache'); // I3: API response caching
let SentimentEngine;
try { SentimentEngine = require('./sentiment'); } catch (e) {}

/**
 * Polymarket dynamic taker fee per share.
 * Crypto markets (Feb 2026+): fee = 0.25 × p² × (1-p)²  (peak ~1.56% at p=0.50)
 * Non-crypto markets: fee = 0.02 × min(p, 1-p)  (flat 2% rate)
 */
function calcTakerFee(price, isCrypto = false) {
  const p = Math.max(0.01, Math.min(0.99, price));
  if (isCrypto) {
    return 0.25 * p * p * (1 - p) * (1 - p);
  }
  return 0.02 * Math.min(p, 1 - p);
}

class SignalEngine {
  constructor(db, risk, notifier, audit) {
    this.db = db;
    this.risk = risk;
    this.notifier = notifier;
    this.audit = audit;
    this.walletTracker = null;  // set by server.js for smart position selection
    this.clobClient = null;     // set by server.js for live price checks
    this.executionCallback = null;
    this.evictionCallback = null;  // called when a position must be evicted to make room
    this.enabled = false;
    this.recentSignals = new Map();  // sig -> timestamp (for TTL expiry)
    this.DEDUP_TTL_MS = 60 * 60 * 1000; // 60 minute dedup window

    // WAL: write-ahead log for crash recovery
    let _walDataDir;
    try { const { app } = require('electron'); _walDataDir = app.getPath('userData'); } catch { _walDataDir = path.join(__dirname, 'data'); }
    try { this._wal = new WAL(_walDataDir); } catch { this._wal = null; }

    // I3: API response cache — avoids redundant CLOB calls on rapid signal evaluations
    this._apiCache = new ApiCache();

    // W4: Cross-wallet consensus tracking — marketKey → [{wallet, timestamp}]
    this._recentMarketEntries = new Map();

    // M3: Volume acceleration tracking — marketKey → [timestamps]
    this._marketVolumeTicks = new Map();

    // Z2: Sentiment engine — comment velocity and crowd analysis
    this._sentiment = SentimentEngine ? new SentimentEngine(null) : null;

    // X7: Spoof detection — tracks bestAsk snapshots per market in a rolling window
    // Uses simplified detection: bestAsk spike >5% that reverts within one snapshot cycle
    this._spoofTracker = new Map(); // market -> { lastBestAsk, spoofEvents: [{ts, ask}], lastTs }

    // In-memory ring buffer for recent signal decisions (accepted + rejected) — visible in UI
    // Seeded from DB so it survives restarts
    this._recentRejections = this.db?.getSetting('signal_activityLog', []) || [];
    this._MAX_REJECTIONS = 200;
    this._activityLogDirty = false;
    this._activityLogTimer = null;

    // Evaluate mutex — serialise concurrent evaluate() calls to prevent race conditions
    this._evaluateLock = Promise.resolve();

    // Periodic cleanup of stale map entries (every 10 min)
    this._cleanupInterval = setInterval(() => this._cleanStaleMapEntries(), 10 * 60 * 1000);
  }

  onExecute(callback) { this.executionCallback = callback; }
  onEvict(callback) { this.evictionCallback = callback; }
  enable()  { this.enabled = true;  this.log('info', 'Signal engine enabled'); }
  disable() { this.enabled = false; this.log('info', 'Signal engine disabled'); }
  shutdown() {
    this.disable();
    if (this._cleanupInterval) { clearInterval(this._cleanupInterval); this._cleanupInterval = null; }
    if (this._activityLogTimer) { clearTimeout(this._activityLogTimer); this._activityLogTimer = null; }
  }
  setFundingRates(rates) { this._fundingRates = rates; }

  async evaluate(walletTrade) {
    // Serialize concurrent evaluate() calls so position-count checks are consistent
    let release;
    this._evaluateLock = this._evaluateLock.then(() => new Promise(res => { release = res; }));
    try {
      return await this._evaluateInner(walletTrade);
    } finally {
      release();
    }
  }

  async _evaluateInner(walletTrade) {
    if (!this.enabled) return { action: 'skip', reason: 'Signal engine disabled' };

    // Halt new positions if API data is flagged as anomalous
    if (this.monitor?._apiAnomaly) {
      this.log('warn', 'API anomaly active — new positions halted', { market: walletTrade?.market });
      return { action: 'blocked', reason: 'API anomaly detected — market data corrupted' };
    }

    // ── BLACKLIST CHECK: permanently block known-bad wallets ──
    const blacklist = this.db?.getSetting('signal_walletBlacklist', []) || [];
    if (blacklist.length > 0) {
      const addr = (walletTrade.wallet_address || '').toLowerCase();
      if (blacklist.some(b => addr.startsWith(b.toLowerCase()))) {
        return { action: 'filtered', reason: 'Wallet blacklisted (proven loser)' };
      }
    }

    // ── PER-WALLET SESSION PNL CHECK: auto-block wallets losing >$5 this session ──
    const walletPnLThreshold = this.db?.getSetting('signal_walletLossThreshold', -5) || -5;
    const _walletAddrPnl = (walletTrade.wallet_address || '').toLowerCase();
    if (_walletAddrPnl && this.risk?.state?.strategyResults) {
      const walletResults = this.risk.state.strategyResults[_walletAddrPnl];
      if (walletResults && walletResults.totalPnL < walletPnLThreshold) {
        this.log('warn', `Wallet ${_walletAddrPnl.slice(0, 10)} auto-blocked: session PnL $${walletResults.totalPnL.toFixed(2)} < $${walletPnLThreshold} threshold`);
        return { action: 'filtered', reason: `Wallet auto-blocked: session PnL $${walletResults.totalPnL.toFixed(2)} below $${walletPnLThreshold}` };
      }
    }

    // ── STRATEGY HEALTH CHECK: block if the copy strategy is cold ──
    if (_walletAddrPnl && this.risk?.checkStrategyHealth) {
      const health = this.risk.checkStrategyHealth(_walletAddrPnl);
      if (!health.healthy) {
        this.log('warn', `Strategy circuit breaker: ${health.reason}`);
        return { action: 'filtered', reason: `Strategy circuit breaker: ${health.reason}` };
      }
    }

    // ── FOCUSED MODE: only copy from trusted wallets ──
    const focusedWallets = this.db?.getSetting('signal_focusedWallets', null);
    if (focusedWallets && Array.isArray(focusedWallets) && focusedWallets.length > 0) {
      const addr = (walletTrade.wallet_address || '').toLowerCase();
      const isTrusted = focusedWallets.some(fw => fw.toLowerCase() === addr);
      if (!isTrusted) {
        return { action: 'skip', reason: 'Not a focused wallet' };
      }
    }

    // W8: Poisoning flag check — block wallets flagged by behavior anomaly detection.
    // Focused wallets are pre-vetted via backtest and trusted by the user; skip W8 for them
    // to prevent a temporary WR dip or frequency spike from blocking all their signals.
    const _wAddr = (walletTrade.wallet_address || walletTrade.walletAddress || '').toLowerCase();
    const _focusedForW8 = this.db?.getSetting('signal_focusedWallets', null);
    const _isFocusedWallet = Array.isArray(_focusedForW8) && _focusedForW8.length > 0 &&
      _focusedForW8.some(fw => fw.toLowerCase() === _wAddr);
    if (!_isFocusedWallet) {
      const _wFlags = this.db?.getSetting('wallet_anomaly_flags', {});
      if (_wFlags && _wFlags[_wAddr]) {
        const _w8Reason = `W8: wallet ${_wAddr.slice(0, 10)} flagged — ${_wFlags[_wAddr].reason}`;
        this.log('warn', _w8Reason, { market: walletTrade.market });
        if (this.audit) this.audit.tradeSignal(walletTrade, { action: 'filtered', reason: _w8Reason });
        this._logRejectedSignal(walletTrade, _w8Reason);
        return { action: 'filtered', reason: 'W8: wallet behavior anomaly flagged' };
      }
    }

    // Dedup with TTL — same wallet+market+side within window is skipped
    const sig = `${walletTrade.wallet_address}:${walletTrade.market}:${walletTrade.side}`;
    this._cleanExpiredSignals();
    if (this.recentSignals.has(sig)) {
      return { action: 'skip', reason: 'Duplicate signal (within dedup window)' };
    }
    this.recentSignals.set(sig, Date.now());

    // Market-level dedup — prevent same market/side from multiple wallets
    const marketSig = `market:${walletTrade.market}:${walletTrade.side}`;
    if (this.recentSignals.has(marketSig)) {
      return { action: 'skip', reason: 'Duplicate signal - market already traded (within dedup window)' };
    }
    this.recentSignals.set(marketSig, Date.now());

    const cfg = this.getConfig();

    const filters = [
      this.filterMinSize(walletTrade, cfg),
      this.filterCategory(walletTrade, cfg),          // moved from #6 to #2
      this.filterWalletQuality(walletTrade, cfg),      // moved from #4 to #3
      this.filterMarketDuration(walletTrade, cfg),     // moved from #2 to #4
      this.filterMarketAge(walletTrade),               // M2: sweet spot age filter
      this.filterEntryRiskReward(walletTrade, cfg),    // moved from #3 to #5
      this.filterMarketWinRate(walletTrade, cfg),      // stayed at #5→#6
      this.filterMarketPrice(walletTrade, cfg)         // stayed at #7
    ];

    const blocked = filters.find(f => !f.pass);
    if (blocked) {
      this.log('info', `Signal filtered: ${blocked.reason}`, { market: walletTrade.market });
      if (this.audit) this.audit.tradeSignal(walletTrade, { action: 'filtered', reason: blocked.reason });
      this._logRejectedSignal(walletTrade, blocked.reason);
      return { action: 'filtered', reason: blocked.reason };
    }

    // ── Async filter: has the price already moved against us? ──
    const priceMoved = await this.filterPriceMoved(walletTrade);
    if (!priceMoved.pass) {
      this.log('info', `Price moved filter: ${priceMoved.reason}`, { market: walletTrade.market });
      if (this.audit) this.audit.tradeSignal(walletTrade, { action: 'filtered', reason: priceMoved.reason });
      this._logRejectedSignal(walletTrade, priceMoved.reason);
      return { action: 'filtered', reason: priceMoved.reason };
    }

    // M3: Volume acceleration filter — skip markets with decelerating interest
    if (!this._checkVolumeAccelerating(walletTrade.market)) {
      const m3Reason = 'M3: volume decelerating on this market';
      this.log('info', m3Reason, { market: walletTrade.market });
      if (this.audit) this.audit.tradeSignal(walletTrade, { action: 'filtered', reason: m3Reason });
      this._logRejectedSignal(walletTrade, m3Reason);
      return { action: 'filtered', reason: m3Reason };
    }

    // M4: Trend filter — reject trades that go against the recent resolution trend
    const trendCheck = this.filterRecentTrend(walletTrade);
    if (!trendCheck.pass) {
      this.log('info', `Trend filter: ${trendCheck.reason}`, { market: walletTrade.market });
      if (this.audit) this.audit.tradeSignal(walletTrade, { action: 'filtered', reason: trendCheck.reason });
      this._logRejectedSignal(walletTrade, trendCheck.reason);
      return { action: 'filtered', reason: trendCheck.reason };
    }

    const confidence = await this.calcConfidence(walletTrade, cfg);

    // Hard minimum confidence gate — reject low-confidence signals
    const minConfidence = this.db?.getSetting('signal_minConfidence', 25) || 25;
    if (confidence < minConfidence) {
      this.log('info', `Confidence gate: ${confidence} < min ${minConfidence}`, { market: walletTrade.market });
      if (this.audit) this.audit.tradeSignal(walletTrade, { action: 'filtered', reason: `Confidence ${confidence} < ${minConfidence}` });
      this._logRejectedSignal(walletTrade, `Confidence ${confidence} < min ${minConfidence}`);
      return { action: 'filtered', reason: `Confidence ${confidence} below minimum ${minConfidence}` };
    }

    const copySize = this.calcCopySize(walletTrade, cfg, confidence);
    const signal = {
      type: 'copy',
      market: walletTrade.market,
      side: walletTrade.side,
      price: walletTrade.price,
      size: copySize,
      copied_from: walletTrade.wallet_name,
      copied_from_address: walletTrade.wallet_address,
      copied_from_win_rate: walletTrade.win_rate,
      copied_from_volume: walletTrade.volume,
      original_size: walletTrade.size,
      conditionId: walletTrade.conditionId || walletTrade.raw?.conditionId || null,
      asset: walletTrade.raw?.asset || null,
      confidence,
      timestamp: new Date().toISOString(),
      strategyId: null
    };

    // Ensure side is always derived — outcomeIndex is authoritative
    if (!signal.side && walletTrade.outcomeIndex !== undefined) {
      signal.side = walletTrade.outcomeIndex === 0 ? 'YES' : 'NO';
    }

    // ── Strategy selection: tag this trade with the best-matching strategy ──
    if (this.strategyEngine) {
      const match = this.strategyEngine.selectForTrade(walletTrade);
      if (match) {
        signal.strategyId = match.id;
        // Apply strategy-specific sizing multiplier
        const mult = this.strategyEngine.getSizingMultiplier(match.id);
        if (mult !== 1.0) {
          signal.size = Math.max(1, +(signal.size * mult).toFixed(2));
          this.log('info', `Strategy ${match.id}: sizing ${mult.toFixed(2)}x → $${signal.size}`, { market: signal.market });
        }
      }
    }
    // R6: Compute EV AFTER strategy sizing so eviction comparison uses final size
    signal.originalEV = +(signal.confidence * signal.size).toFixed(4);

    // ── Entry timing optimization: wait, then verify price hasn't degraded ──
    if (cfg.copyDelayMs > 0) {
      const jitter = cfg.copyDelayMs * (0.5 + Math.random());
      this.log('info', `Entry timing: waiting ${Math.round(jitter)}ms before re-checking price`, { market: walletTrade.market });
      await new Promise(r => setTimeout(r, jitter));

      this.log('debug', 'Post-delay price check', { market: walletTrade.market, delayMs: Math.round(jitter) });

      // Z1: Whale confirmation check — detect if whale reversed position during delay
      try {
        const whaleActivity = await this._checkWhaleActivityDuringDelay(
          walletTrade.wallet_address, walletTrade.market, jitter + 1000
        );
        if (whaleActivity.reversedPosition) {
          const revReason = 'Whale reversed position during confirmation window — adverse selection detected';
          if (this.audit) this.audit.tradeSignal(walletTrade, { action: 'filtered', reason: revReason });
          this._logRejectedSignal(walletTrade, revReason);
          return { action: 'filtered', reason: revReason };
        }
        if (whaleActivity.addedMore) {
          signal.size = Math.min(signal.size * 1.2, cfg.maxCopySize || 50);
          this.log('info', 'Z1: Whale added more during delay — sizing up 20%', { market: walletTrade.market });
        }
      } catch (_z1Err) { /* non-blocking */ }

      // Re-check price after delay — if it moved against us, abort
      if (this.clobClient?.isReady()) {
        try {
          const tokens = await this.clobClient.resolveTokenIds(walletTrade.market);
          if (tokens) {
            const tokenId = walletTrade.side === 'YES' ? tokens.yesTokenId : tokens.noTokenId;
            const book = await this.clobClient.getOrderBook(tokenId);
            if (book?.asks?.length > 0) {
              const currentAsk = parseFloat(book.asks[0].price) || 0;
              const originalPrice = parseFloat(walletTrade.price) || 0;
              if (originalPrice > 0 && currentAsk > 0) {
                const drift = (currentAsk - originalPrice) / originalPrice;
                if (drift > 0.08) {
                  const driftReason = `Price drifted ${(drift * 100).toFixed(1)}% during ${Math.round(jitter)}ms delay`;
                  this.log('info', `Entry timing abort: price drifted ${(drift * 100).toFixed(1)}% during delay`, { market: walletTrade.market });
                  if (this.audit) this.audit.tradeSignal(walletTrade, { action: 'filtered', reason: `Price drifted ${(drift * 100).toFixed(1)}% during entry delay` });
                  this._logRejectedSignal(walletTrade, driftReason);
                  return { action: 'filtered', reason: driftReason };
                }
                // If price improved (dropped), update the signal price for better fill
                if (drift < -0.01) {
                  this.log('info', `Entry timing bonus: price improved ${(-drift * 100).toFixed(1)}% during delay`);
                  walletTrade._improvedPrice = currentAsk;
                }

                // Post-delay EV recheck with actual current price
                if (currentAsk > 0 && currentAsk < 1) {
                  const FEE_RATE = 0.02;
                  const postDelayReward = 1 - currentAsk - FEE_RATE;
                  if (postDelayReward <= 0) {
                    const reason = `Post-delay: price ${currentAsk.toFixed(3)} too high for positive EV after fees`;
                    this._logRejectedSignal(walletTrade, reason);
                    return { action: 'filtered', reason };
                  }
                  // Update signal price to current ask for accurate downstream sizing
                  signal.price = currentAsk;
                }
              }
            }
          }
        } catch (e) { /* best effort */ }
      }
    }

    // Risk check
    if (this.risk) {
      const riskCheck = this.risk.checkTrade(signal);
      if (!riskCheck.allowed) {
        // Smart position selection: when at max, check if this wallet is outperforming
        if (riskCheck.atMax && this.walletTracker) {
          const evictResult = await this._trySmartEviction(signal);
          if (!evictResult.success) {
            if (this.notifier) this.notifier.tradeBlocked(riskCheck.reason);
            if (this.audit) this.audit.tradeSignal(signal, { action: 'blocked', reason: riskCheck.reason });
            this._logRejectedSignal(walletTrade, riskCheck.reason);
            return { action: 'blocked', reason: riskCheck.reason };
          }
          // Eviction succeeded — position slot freed, re-check risk
          const recheck = this.risk.checkTrade(signal);
          if (!recheck.allowed) {
            return { action: 'blocked', reason: recheck.reason };
          }
          if (recheck.adjustSize) signal.size = recheck.adjustSize;
        } else {
          if (this.notifier) this.notifier.tradeBlocked(riskCheck.reason);
          if (this.audit) this.audit.tradeSignal(signal, { action: 'blocked', reason: riskCheck.reason });
          this._logRejectedSignal(walletTrade, riskCheck.reason);
          return { action: 'blocked', reason: riskCheck.reason };
        }
      }
      if (riskCheck.adjustSize) signal.size = riskCheck.adjustSize;
    }

    // ── R2 + R5: Directional concentration + portfolio correlation checks ──
    // Derive category once, shared by both checks
    const _cfg2 = this.getConfig();
    const _mktLower = (signal.market || '').toLowerCase();
    const _matchedCat = (_cfg2.allowedCategories || []).find(c => _mktLower.includes(c.toLowerCase())) || 'unknown';

    if (this.risk?.checkDirectionalConcentration) {
      const _dirSide = signal.side || (walletTrade.outcomeIndex === 0 ? 'YES' : 'NO');
      const _bankroll = this.db?.getSetting('risk_bankroll', 500) || 500;
      const dirCheck = this.risk.checkDirectionalConcentration(_dirSide, _matchedCat, signal.size, _bankroll);
      if (dirCheck && !dirCheck.allowed) {
        this.log('info', `R2 directional check: ${dirCheck.reason}`, { market: signal.market });
        if (this.audit) this.audit.tradeSignal(signal, { action: 'blocked', reason: dirCheck.reason });
        this._logRejectedSignal(walletTrade, dirCheck.reason);
        return { action: 'blocked', reason: dirCheck.reason };
      }
    }

    // ── R5: Portfolio correlation check ──
    if (this.risk?.checkPortfolioCorrelation) {
      const _corrCat = _matchedCat;
      const _corrSide = signal.side || (walletTrade.outcomeIndex === 0 ? 'YES' : 'NO');
      const corrCheck = this.risk.checkPortfolioCorrelation({
        category: _corrCat,
        side: _corrSide
      });
      if (corrCheck && !corrCheck.allowed) {
        this.log('info', `R5 correlation check: ${corrCheck.reason}`, { market: signal.market });
        if (this.audit) this.audit.tradeSignal(signal, { action: 'blocked', reason: corrCheck.reason });
        this._logRejectedSignal(walletTrade, corrCheck.reason);
        return { action: 'blocked', reason: corrCheck.reason };
      }
    }

    // ── Market time-to-close check ──
    if (this.clobClient?.isReady()) {
      const timeCheck = await this._checkMarketTimeRemaining(signal);
      if (!timeCheck.pass) {
        this.log('info', `Time check: ${timeCheck.reason}`, { market: signal.market });
        if (this.audit) this.audit.tradeSignal(signal, { action: 'filtered', reason: timeCheck.reason });
        this._logRejectedSignal(walletTrade, timeCheck.reason);
        return { action: 'filtered', reason: timeCheck.reason };
      }
    }

    // ── Live price validation + slippage guard ──
    let liqResult = null;
    if (this.clobClient?.isReady()) {
      const slippageResult = await this._checkSlippage(signal, walletTrade);
      if (!slippageResult.pass) {
        this.log('info', `Slippage guard: ${slippageResult.reason}`, { market: signal.market });
        if (this.audit) this.audit.tradeSignal(signal, { action: 'filtered', reason: slippageResult.reason });
        this._logRejectedSignal(walletTrade, slippageResult.reason);
        return { action: 'filtered', reason: slippageResult.reason };
      }
      // Update signal price to live price for better fills
      if (slippageResult.livePrice) signal.price = slippageResult.livePrice;

      // Liquidity check
      liqResult = await this._checkLiquidity(signal, walletTrade);
      if (!liqResult.pass) {
        this.log('info', `Liquidity check: ${liqResult.reason}`, { market: signal.market });
        if (this.audit) this.audit.tradeSignal(signal, { action: 'filtered', reason: liqResult.reason });
        this._logRejectedSignal(walletTrade, liqResult.reason);
        return { action: 'filtered', reason: liqResult.reason };
      }
      if (liqResult.adjustSize) signal.size = liqResult.adjustSize;
    }

    // ── Expected value gate ──
    const evResult = this._checkExpectedValue(signal, walletTrade, liqResult?.liquidity || null);
    if (!evResult.pass) {
      this.log('info', `EV gate: ${evResult.reason}`, { market: signal.market });
      if (this.audit) this.audit.tradeSignal(signal, { action: 'filtered', reason: evResult.reason });
      this._logRejectedSignal(walletTrade, evResult.reason);
      return { action: 'filtered', reason: evResult.reason };
    }

    // Dry run mode — log everything but don't actually trade
    const globalDry = this.risk?.getConfig()?.dryRun;
    let dryRun;
    if (globalDry !== false) {
      dryRun = true;
    } else {
      const liveStrategies = this.db?.getSetting('live_strategies', []) || [];
      if (!liveStrategies.includes('copy')) {
        if (!this._loggedForcedPaper) { this.log('info', '[Signal] Forced paper mode — not in live_strategies whitelist'); this._loggedForcedPaper = true; }
        dryRun = true;
      } else {
        dryRun = false;
      }
    }
    if (dryRun) {
      this.log('info', `[DRY RUN] Would copy: ${signal.side} $${signal.size} on ${signal.market}`);
      if (this.audit) this.audit.dryRun(signal, { action: 'dry_run' });
      if (this.notifier) this.notifier.send(
        'Dry Run Trade',
        `${signal.side} $${signal.size} on ${signal.market}`,
        { type: 'info', priority: 'low' }
      );

      // Log to DB as dry run
      let tradeId = null;
      if (this.db) {
        try {
          const r = this.db.logTrade({
            market: signal.market, side: signal.side, price: signal.price,
            size: signal.size, copied_from: signal.copied_from,
            status: 'dry_run', dry_run: true
          });
          tradeId = r?.id;
        } catch (e) {}
      }

      // Register dry-run position with risk engine for resolution tracking
      if (this.risk && tradeId) {
        try {
          // Use conditionId from the trade data (from data API) — most reliable
          let conditionId = signal.conditionId || null;

          // Fallback: query Gamma API by title (strict match only)
          if (!conditionId) {
            try {
              const axios = require('axios');
              const searchTitle = signal.market.replace(/[^a-zA-Z0-9 ]/g, ' ').slice(0, 60).trim();
              const gammaR = await axios.get('https://gamma-api.polymarket.com/markets', {
                params: { title: searchTitle, limit: 5 }, timeout: 5000
              });
              const titleLower = signal.market.toLowerCase().trim();
              const match = (gammaR.data || []).find(m =>
                (m.question || '').toLowerCase().trim() === titleLower
              );
              if (match) conditionId = match.condition_id;
            } catch (e) { /* best effort */ }
          }

          const dryId = `dry_${tradeId}`;
          this.risk.openPosition({
            id: dryId, tradeId, market: signal.market, side: signal.side,
            size: signal.size, price: signal.price,
            conditionId,
            tokenId: signal.asset || null,
            copied_from: signal.copied_from,
            copied_from_address: signal.copied_from_address,
            strategyId: signal.strategyId || null,
            dryRun: true
          });
          this.log('info', '[DRY RUN] Position registered for resolution tracking', {
            dryId, market: signal.market, conditionId: conditionId || null
          });
        } catch (e) {
          this.log('warn', '[DRY RUN] Failed to register position', { error: e.message });
        }
      }

      // Write journal entry for dry_run so the Trade Journal page shows activity
      if (this.db?.logJournalEntry) {
        try {
          this.db.logJournalEntry({
            action: 'dry_run',
            market: signal.market,
            side: signal.side,
            price: signal.price,
            size: signal.size,
            confidence: signal.confidence,
            tradeId,
            whale: {
              name: signal.copied_from,
              address: signal.copied_from_address,
              originalSize: signal.original_size,
              whalePrice: walletTrade.price
            }
          });
        } catch (e) {}
      }

      // Record accepted signal in activity feed
      this._recentRejections.push({
        timestamp: Date.now(),
        market: signal.market,
        side: signal.side,
        size: signal.size,
        marketPrice: signal.price,
        walletAddress: signal.copied_from_address,
        walletName: signal.copied_from,
        confidence: signal.confidence,
        action: 'dry_run'
      });
      if (this._recentRejections.length > this._MAX_REJECTIONS) this._recentRejections.shift();
      this._persistActivityLog();

      return { action: 'dry_run', signal };
    }

    // Size randomization: makes order sizes harder to fingerprint
    // (Size randomization moved above journal entry — Bug #21)
    signal.size = signal.size * (0.97 + Math.random() * 0.06);
    signal.size = Math.max(1, +signal.size.toFixed(2));

    // ── Trade journal: record full reasoning ──
    const journalEntry = {
      action: 'execute', // Bug #15 fix: was incorrectly using dryRun ternary (dry_run already returned above)
      market: signal.market,
      side: signal.side,
      price: signal.price,
      size: signal.size,
      confidence: signal.confidence,
      whale: {
        name: signal.copied_from,
        address: signal.copied_from_address,
        originalSize: signal.original_size,
        whalePrice: walletTrade.price
      },
      checks: {
        slippagePassed: true,
        liquidityPassed: true,
        evPassed: true,
        ev: evResult.ev ? +(evResult.ev * 100).toFixed(1) + '¢/share' : null,
        evPerDollar: evResult.evPerDollar ? +evResult.evPerDollar.toFixed(4) : null,
        timeRemainingOk: true,
        confidenceFactors: this._lastConfidenceFactors || null
      },
      walletStats: null,
      sizing: {
        mode: cfg.sizingMode,
        kellySizing: true,
        bankroll: this._getBankroll()
      }
    };
    // Add wallet tracker stats if available
    if (this.walletTracker && walletTrade.wallet_address) {
      const stats = this.walletTracker.getWalletStats(walletTrade.wallet_address);
      if (stats) {
        journalEntry.walletStats = {
          d3WinRate: stats.d3.winRate, d7WinRate: stats.d7.winRate,
          d3Trades: stats.d3.resolvedTrades, d7Trades: stats.d7.resolvedTrades
        };
      }
    }
    if (this.db?.logJournalEntry) {
      try { this.db.logJournalEntry(journalEntry); } catch (e) {}
    }

    // (Size randomization moved above journal entry — Bug #21)

    // X1: Price impact check — reduce or reject if our order would move the market
    if (this.clobClient?.isReady()) {
      try {
        const _side = signal.side || (walletTrade.outcomeIndex === 0 ? 'YES' : 'NO');
        const impact = await this._estimatePriceImpact(signal.market, _side, signal.size);
        if (impact.priceImpactPct > 8) {
          const impactReason = `X1: price impact ${impact.priceImpactPct.toFixed(1)}% exceeds 8%`;
          if (this.audit) this.audit.tradeSignal(signal, { action: 'filtered', reason: impactReason });
          this._logRejectedSignal(walletTrade, impactReason);
          return { execute: false, reason: impactReason };
        }
        if (impact.shouldReduce && signal.size > 10) {
          signal.size = +(signal.size * 0.6).toFixed(2);
          this.log('info', `[Signal] X1 impact ${impact.priceImpactPct.toFixed(1)}% — size reduced to $${signal.size}`);
        }
      } catch (_impactErr) { /* non-blocking */ }
    }

    // Execute
    this.log('info', 'Executing copy signal', { market: signal.market, side: signal.side, size: signal.size, confidence: signal.confidence });
    if (this.notifier) this.notifier.tradeCopied(signal.market, signal.side, signal.size, signal.price);
    if (this.audit) this.audit.tradeSignal(signal, { action: 'execute' });

    if (this.executionCallback) {
      try {
        const result = await this._executeWithRetry(signal, async (sig) => {
          return await this._splitAndExecute(sig, this.executionCallback);
        });
        // Track executed trade in activity feed
        this._recentRejections.push({
          timestamp: Date.now(),
          market: signal.market, side: signal.side, size: signal.size,
          marketPrice: signal.price, walletAddress: signal.copied_from_address,
          walletName: signal.copied_from, confidence: signal.confidence,
          action: 'executed'
        });
        if (this._recentRejections.length > this._MAX_REJECTIONS) this._recentRejections.shift();
        return { action: 'executed', signal, result };
      } catch (e) {
        this.log('error', 'Signal execution failed', { error: e.message });
        return { action: 'error', reason: e.message };
      }
    }

    return { action: 'queued', signal };
  }

  // ── Dedup cleanup ─────────────────────────────────────────────────

  _cleanExpiredSignals() {
    const now = Date.now();
    for (const [key, ts] of this.recentSignals) {
      if (now - ts > this.DEDUP_TTL_MS) this.recentSignals.delete(key);
    }
    // Hard cap on recentSignals Map
    if (this.recentSignals.size > 5000) {
      const iter = this.recentSignals.keys();
      while (this.recentSignals.size > 3000) this.recentSignals.delete(iter.next().value);
    }
  }

  /** Purge stale entries from tracking maps to prevent unbounded memory growth. */
  _cleanStaleMapEntries() {
    const TWO_HOURS = 2 * 60 * 60 * 1000;
    const MAX_ENTRIES_PER_MAP = 500;
    const now = Date.now();

    // W4: cross-wallet consensus entries
    for (const [key, entries] of this._recentMarketEntries) {
      const fresh = entries.filter(e => now - e.timestamp < TWO_HOURS);
      if (fresh.length === 0) this._recentMarketEntries.delete(key);
      else this._recentMarketEntries.set(key, fresh);
    }
    // Hard cap: evict oldest markets if map grows too large
    if (this._recentMarketEntries.size > MAX_ENTRIES_PER_MAP) {
      const keys = [...this._recentMarketEntries.keys()];
      for (let i = 0; i < keys.length - MAX_ENTRIES_PER_MAP; i++) {
        this._recentMarketEntries.delete(keys[i]);
      }
    }

    // M3: volume tick timestamps
    for (const [key, ticks] of this._marketVolumeTicks) {
      const fresh = ticks.filter(ts => now - ts < TWO_HOURS);
      if (fresh.length === 0) this._marketVolumeTicks.delete(key);
      else this._marketVolumeTicks.set(key, fresh);
    }
    if (this._marketVolumeTicks.size > MAX_ENTRIES_PER_MAP) {
      const keys = [...this._marketVolumeTicks.keys()];
      for (let i = 0; i < keys.length - MAX_ENTRIES_PER_MAP; i++) {
        this._marketVolumeTicks.delete(keys[i]);
      }
    }

    // X7: spoof tracker — prune stale entries
    for (const [key, tracker] of this._spoofTracker) {
      if (now - (tracker.lastTs || 0) > TWO_HOURS) {
        this._spoofTracker.delete(key);
      } else if (tracker.spoofEvents?.length > 50) {
        tracker.spoofEvents = tracker.spoofEvents.slice(-20);
      }
    }
    if (this._spoofTracker.size > MAX_ENTRIES_PER_MAP) {
      const keys = [...this._spoofTracker.keys()];
      for (let i = 0; i < keys.length - MAX_ENTRIES_PER_MAP; i++) {
        this._spoofTracker.delete(keys[i]);
      }
    }
  }

  // ── Filters ───────────────────────────────────────────────────────

  filterMinSize(trade, cfg) {
    if (trade.size < cfg.minOriginalSize) return { pass: false, reason: `Original position $${trade.size} below minimum $${cfg.minOriginalSize}` };
    return { pass: true };
  }

  filterWalletQuality(trade, cfg) {
    // Focused wallets are pre-vetted via backtest — skip live tracker WR gate for them
    const focusedWallets = this.db?.getSetting('signal_focusedWallets', null);
    if (focusedWallets && Array.isArray(focusedWallets) && focusedWallets.length > 0) {
      const addr = (trade.wallet_address || '').toLowerCase();
      if (focusedWallets.some(fw => fw.toLowerCase() === addr)) {
        // Safety net: even focused wallets must have ≥3 resolved trades and ≥40% WR
        if (this.walletTracker) {
          const stats = this.walletTracker.getWalletStats(addr);
          const best = this._bestWindow(stats);
          if (best && (best.wins + best.losses) >= 3 && best.winRate < 40) {
            return { pass: false, reason: `Focused wallet safety net: WR ${best.winRate.toFixed(0)}% < 40% (${best.wins + best.losses} trades)` };
          }
        }
        return { pass: true };
      }
    }

    // Prefer real-time win rate from wallet tracker over manually-set value
    let effectiveWinRate = trade.win_rate ? parseFloat(trade.win_rate) : null;

    if (this.walletTracker && trade.wallet_address) {
      const stats = this.walletTracker.getWalletStats(trade.wallet_address);
      if (stats) {
        // Use 7-day win rate if available (most reliable window), fall back to 3-day
        if (stats.d7.winRate !== null && stats.d7.resolvedTrades >= 5) {
          effectiveWinRate = stats.d7.winRate;
        } else if (stats.d3.winRate !== null && stats.d3.resolvedTrades >= 3) {
          effectiveWinRate = stats.d3.winRate;
        }
      }
    }

    // If effectiveWinRate is 0 and there are fewer than 5 resolved trades, treat as "no data" and allow
    if (effectiveWinRate === 0 && this.walletTracker && trade.wallet_address) {
      const stats = this.walletTracker.getWalletStats(trade.wallet_address);
      if (!stats || (stats.d7.resolvedTrades < 5 && stats.d3.resolvedTrades < 5)) {
        return { pass: true }; // Not enough data to judge — allow
      }
    }

    if (effectiveWinRate !== null && effectiveWinRate < cfg.minWinRate) {
      return { pass: false, reason: `Wallet win rate ${effectiveWinRate}% below minimum ${cfg.minWinRate}%` };
    }

    // Binomial significance test — reject wallets whose edge is not statistically real
    if (this.walletTracker && trade.wallet_address) {
      const stats = this.walletTracker.getWalletStats(trade.wallet_address);
      const best = this._bestWindow(stats);
      if (best && (best.wins + best.losses) >= 15) {
        const wins = best.wins;
        const total = best.wins + best.losses;
        const p = wins / total;
        const p0 = 0.50;
        const z = (p - p0) / Math.sqrt((p0 * (1 - p0)) / total);
        const absZ = Math.abs(z);
        const pValue = 0.5 * Math.exp(-0.717 * absZ - 0.416 * absZ * absZ);
        if (z <= 0 || pValue >= 0.05) {
          return {
            pass: false,
            reason: `Win rate not statistically significant (p=${pValue.toFixed(3)}, z=${z.toFixed(2)}, ${total} trades). Need p<0.05.`
          };
        }
      }
    }

    return { pass: true };
  }

  /**
   * Market-specific win rate filter: only copy a whale in markets where they perform well.
   * Uses the wallet tracker's per-market stats.
   * If we have enough data and the whale's win rate in this market type is below threshold, skip.
   */
  filterMarketWinRate(trade, cfg) {
    if (!this.walletTracker) return { pass: true }; // No tracker, can't filter

    const marketStats = this.walletTracker.getWalletMarketStats(
      trade.wallet_address,
      7 * 24 * 60 * 60 * 1000 // 7-day window
    );

    if (!marketStats || marketStats.length === 0) return { pass: true }; // No data yet

    // Find stats matching this market (normalize for fuzzy match)
    const targetNorm = this._normalizeMarketPattern(trade.market);
    const matchingStat = marketStats.find(m =>
      this._normalizeMarketPattern(m.market) === targetNorm
    );

    if (!matchingStat || matchingStat.resolved < 3) return { pass: true }; // Not enough data

    const minMarketWinRate = cfg.minWinRate || 60;
    if (matchingStat.winRate !== null && matchingStat.winRate < minMarketWinRate) {
      return {
        pass: false,
        reason: `Wallet ${trade.wallet_name} has ${matchingStat.winRate}% win rate in this market (need ${minMarketWinRate}%, based on ${matchingStat.resolved} resolved trades)`
      };
    }

    return { pass: true };
  }

  /**
   * Normalize market names for pattern matching.
   * "Bitcoin up or down (5 min)" and "Bitcoin 5m up or down" should match.
   */
  _normalizeMarketPattern(name) {
    return (name || '').toLowerCase()
      .replace(/[^a-z0-9]/g, ' ')
      .replace(/\s+/g, ' ')
      .trim();
  }

  filterCategory(trade, cfg) {
    if (!cfg.allowedCategories || cfg.allowedCategories.length === 0) return { pass: true };
    const mkt = (trade.market || '').toLowerCase();
    const match = cfg.allowedCategories.some(cat => mkt.includes(cat.toLowerCase()));
    if (!match) return { pass: false, reason: 'Market category not in allowed list' };
    return { pass: true };
  }

  /**
   * Filter by market duration — only allow short-term markets (≤ maxDurationMinutes).
   * Parses time range from market titles like "Bitcoin Up or Down - March 25, 1:30AM-1:45AM ET"
   * or detects duration keywords like "5m", "15m", "1h".
   */
  filterMarketDuration(trade, cfg) {
    const maxMinutes = cfg.maxMarketDurationMinutes || 1440; // default: 24 hours max
    const minMinutes = cfg.minMarketDurationMinutes || 0;    // use cfg so default applies correctly
    if (maxMinutes <= 0) return { pass: true }; // 0 = disabled

    const title = (trade.market || '').toLowerCase();
    const durationMin = SignalEngine.parseMarketDurationMinutes(title);

    if (durationMin === null) {
      // Can't determine duration — allow crypto markets (they're likely daily/weekly)
      // Block markets that are clearly non-crypto (but category filter should catch those first)
      return { pass: true };
    }

    if (durationMin < minMinutes) {
      return { pass: false, reason: `Market duration ${durationMin}min too short (min ${minMinutes}min) — entering 5-min markets after lag has negative EV` };
    }

    if (durationMin > maxMinutes) {
      return { pass: false, reason: `Market duration ${durationMin}min exceeds max ${maxMinutes}min` };
    }

    return { pass: true };
  }

  /**
   * M2: Market age sweet spot filter.
   * Prevents entering markets that are too early (wide spreads) or already closed.
   *
   * Thresholds by duration:
   *   < 30 min  — exempt from age filter entirely (poll lag makes age unreliable)
   *   30 min–1h — block if > 95% through (very close to expiry)
   *   > 1h      — block if > 80% through (original threshold for longer markets)
   *   > 100%    — always block (market has already closed)
   *
   * Uses the time-range parsed from the market title to determine age.
   */
  filterMarketAge(trade) {
    try {
      // Prefer explicit endDate from trade data (most reliable)
      const rawEnd = trade.raw?.endDate || trade.raw?.end_date_iso || trade.endDate;
      if (rawEnd) {
        const endDate = new Date(rawEnd);
        if (!isNaN(endDate.getTime())) {
          const now = new Date();
          if (now >= endDate) {
            return { pass: false, reason: 'M2: market already closed (past endDate)' };
          }
          const msLeft = endDate.getTime() - now.getTime();
          const minLeft = msLeft / 60000;
          // If less than 2 minutes remain, too late to enter
          if (minLeft < 2) {
            return { pass: false, reason: `M2: only ${minLeft.toFixed(1)} min left before close — too late` };
          }
          return { pass: true };
        }
      }

      // Fallback: parse from title
      const title = (trade.market || '').toLowerCase();
      const durationMin = SignalEngine.parseMarketDurationMinutes(title);
      if (durationMin === null) return { pass: true }; // can't determine — allow through

      // Exempt very short markets: poll lag makes age unreliable for <30 min markets
      if (durationMin < 30) return { pass: true };

      // Estimate when the market started from the title time range
      const rangeMatch = title.match(/(\d{1,2}):(\d{2})\s*(am|pm)\s*[-–]\s*(\d{1,2}):(\d{2})\s*(am|pm)/i);
      if (!rangeMatch) return { pass: true }; // no time range — allow through

      let [, h1, m1, p1] = rangeMatch;
      h1 = parseInt(h1); m1 = parseInt(m1);
      if (p1.toLowerCase() === 'pm' && h1 !== 12) h1 += 12;
      if (p1.toLowerCase() === 'am' && h1 === 12) h1 = 0;

      // Market times are always in ET (Eastern Time, UTC-4 EDT / UTC-5 EST)
      // Build the market start time in UTC, then compare to now in UTC
      const now = new Date();
      const etOffsetHours = SignalEngine._getETOffset();
      // Build a UTC date for "today in ET" at the market's start hour
      const todayET = new Date(now.toLocaleString('en-US', { timeZone: 'America/New_York' }));
      const marketStartUTC = new Date(Date.UTC(
        todayET.getFullYear(), todayET.getMonth(), todayET.getDate(),
        h1 - etOffsetHours, m1, 0, 0
      ));

      // Handle day boundary: if start is in the future, it was yesterday
      let elapsedMs = now.getTime() - marketStartUTC.getTime();
      if (elapsedMs < 0) elapsedMs += 24 * 60 * 60 * 1000;
      // Sanity: if elapsed is more than 24h, the date math is wrong — skip filter
      if (elapsedMs > 24 * 60 * 60 * 1000) return { pass: true };

      const elapsedMin = elapsedMs / 60000;
      const pctThrough = elapsedMin / durationMin;

      // Market has already closed — never enter a closed market
      if (pctThrough > 1.0) {
        return { pass: false, reason: `M2: market already closed (${(pctThrough*100).toFixed(0)}% through — past end time)` };
      }

      // Duration-based late-entry threshold
      // 30 min–1h: block at 95% (market is within last ~1.5–3 min of a very short window)
      // >1h: block at 80% (original threshold — plenty of duration left to protect)
      const maxPct = durationMin <= 60 ? 0.95 : 0.80;

      if (pctThrough > maxPct) {
        return { pass: false, reason: `M2: market ${(pctThrough*100).toFixed(0)}% through (max ${maxPct*100}% for ${durationMin}min market) — too late, edge priced in` };
      }
      return { pass: true };
    } catch (err) {
      return { pass: true }; // on error, allow through
    }
  }

  /**
   * Parse market duration in minutes from title.
   * Handles:
   *   "Bitcoin Up or Down - March 25, 1:30AM-1:45AM ET"  → 15
   *   "Bitcoin Up or Down - March 25, 1:00AM-2:00AM ET"  → 60
   *   "5m", "15m", "30m", "1h" keywords                  → 5, 15, 30, 60
   * Returns null if unparseable.
   */
  /**
   * Get the current ET (Eastern Time) offset from UTC in hours.
   * Handles EDT (UTC-4) and EST (UTC-5) automatically.
   */
  static _getETOffset() {
    // Robustly compute ET offset from UTC without depending on local timezone.
    // new Date(localeString) parses using the LOCAL timezone, so the old approach
    // produced wrong results on UTC+ machines (e.g. UTC+7 returned -18 instead of -4).
    const now = new Date();
    const etHour = parseInt(
      new Intl.DateTimeFormat('en-US', { timeZone: 'America/New_York', hour: 'numeric', hour12: false }).format(now),
      10
    );
    const utcHour = now.getUTCHours();
    let offset = etHour - utcHour;
    // Correct for day boundary (e.g. etHour=23, utcHour=4 → offset=19, should be -5)
    if (offset > 12) offset -= 24;
    if (offset < -12) offset += 24;
    return offset; // -4 for EDT, -5 for EST
  }

  static parseMarketDurationMinutes(title) {
    if (!title) return null;
    const t = title.toLowerCase();

    // Method 1: Explicit duration keywords
    const kwMatch = t.match(/(\d+)\s*m(?:in(?:ute)?s?)?(?:\s|$|,)/);
    if (kwMatch) return parseInt(kwMatch[1]);
    const hrMatch = t.match(/(\d+)\s*h(?:(?:ou)?rs?)?(?:\s|$|,)/);
    if (hrMatch) return parseInt(hrMatch[1]) * 60;

    // Method 2: Time range pattern "HH:MMAM-HH:MMPM" or "H:MMAM-H:MMPM"
    const rangeMatch = t.match(/(\d{1,2}):(\d{2})\s*(am|pm)\s*[-–]\s*(\d{1,2}):(\d{2})\s*(am|pm)/i);
    if (rangeMatch) {
      let [, h1, m1, p1, h2, m2, p2] = rangeMatch;
      h1 = parseInt(h1); m1 = parseInt(m1);
      h2 = parseInt(h2); m2 = parseInt(m2);
      if (p1.toLowerCase() === 'pm' && h1 !== 12) h1 += 12;
      if (p1.toLowerCase() === 'am' && h1 === 12) h1 = 0;
      if (p2.toLowerCase() === 'pm' && h2 !== 12) h2 += 12;
      if (p2.toLowerCase() === 'am' && h2 === 12) h2 = 0;
      const startMin = h1 * 60 + m1;
      const endMin = h2 * 60 + m2;
      const diff = endMin >= startMin ? endMin - startMin : (1440 - startMin + endMin);
      if (diff > 0 && diff <= 1440) return diff;
    }

    return null; // Can't determine
  }

  /**
   * Risk/reward filter — reject entries with terrible risk/reward ratios.
   * Buying at 0.95 means risking $0.95 to make $0.05 (19:1 risk/reward).
   * Buying at 0.50 means risking $0.50 to make $0.50 (1:1 — fair).
   * Buying at 0.20 means risking $0.20 to make $0.80 (1:4 — excellent).
   */
  filterEntryRiskReward(trade, cfg) {
    const price = parseFloat(trade.price);
    if (!price || price <= 0 || price >= 1) return { pass: true }; // Can't evaluate

    // Risk = price (what you lose if wrong), reward = 1 - price (what you gain if right)
    const risk = price;
    const reward = 1 - price;
    const ratio = reward / risk; // >1 = good, <0.2 = terrible

    // Reject if risk/reward ratio is terrible (buying at >0.67)
    // Allow profitable wallets to trade higher-conviction plays in the 0.50-0.67 range
    const minRatio = this.db?.getSetting('signal_minRiskRewardRatio', 0.5) || 0.5;
    if (ratio < minRatio) {
      return { pass: false, reason: `Bad risk/reward: paying $${price.toFixed(3)} for $${reward.toFixed(3)} upside (${ratio.toFixed(2)} ratio)` };
    }
    return { pass: true };
  }

  filterMarketPrice(trade, cfg) {
    const price = parseFloat(trade.price);
    if (price < cfg.minPrice) return { pass: false, reason: `Price ${price} below minimum ${cfg.minPrice}` };
    if (price > cfg.maxPrice) return { pass: false, reason: `Price ${price} above maximum ${cfg.maxPrice}` };
    return { pass: true };
  }

  /**
   * Price-moved check: if the market price has already moved significantly
   * since the whale's entry, we're getting a worse deal.
   * Uses CLOB client to get live price and compare to whale's fill price.
   */
  async filterPriceMoved(trade) {
    if (!this.clobClient?.isReady()) return { pass: true }; // Can't check, allow

    const whalePrice = parseFloat(trade.price) || 0;
    if (whalePrice <= 0 || whalePrice >= 1) return { pass: true };

    try {
      // I3: Cache token ID resolution for 5 minutes (market → tokenId almost never changes)
      const tokenCacheKey = `tokenIds:${trade.market}`;
      const tokens = await this._apiCache.get(
        tokenCacheKey,
        ApiCache.TTL.MARKET_METADATA,
        () => this.clobClient.resolveTokenIds(trade.market)
      );
      if (!tokens) return { pass: true };

      const tokenId = trade.side === 'YES' ? tokens.yesTokenId : tokens.noTokenId;
      // I3: Cache orderbook for 5 seconds (CLOB_ORDERBOOK TTL)
      const obCacheKey = `orderbook:${tokenId}`;
      const book = await this._apiCache.get(
        obCacheKey,
        ApiCache.TTL.CLOB_ORDERBOOK,
        () => this.clobClient.getOrderBook(tokenId)
      );
      if (!book || !book.asks || book.asks.length === 0) return { pass: true };

      // Best ask = price we'd actually pay
      const bestAsk = parseFloat(book.asks[0].price) || 0;
      if (bestAsk <= 0) return { pass: true };

      const slippage = (bestAsk - whalePrice) / whalePrice;
      const MAX_PRICE_MOVE = 0.05; // 5% move = we're too late

      if (slippage > MAX_PRICE_MOVE) {
        return {
          pass: false,
          reason: `Price moved ${(slippage * 100).toFixed(1)}% since whale entry ($${whalePrice.toFixed(3)} → $${bestAsk.toFixed(3)}). Too late.`
        };
      }

      // If price actually dropped (we'd get a better deal), that's fine
      return { pass: true, livePrice: bestAsk };
    } catch (e) {
      return { pass: true }; // Don't block on errors
    }
  }

  // ── M4: Recent-resolution trend filter ────────────────────────────────

  /**
   * Extract the asset name from an "Up or Down" market title.
   * E.g. "Bitcoin Up or Down - March 25, 1:30AM-1:35AM ET" → "bitcoin"
   *      "Ethereum 5m Up or Down"                          → "ethereum"
   * Returns null if the title doesn't match the pattern.
   */
  _extractUpDownAsset(title) {
    if (!title) return null;
    const m = title.match(/^(.+?)\s+(?:\d+m\s+)?up\s+or\s+down/i);
    return m ? m[1].toLowerCase().replace(/[^a-z0-9]/g, '').trim() : null;
  }

  /**
   * M4: Trend filter — prevents entering "Up or Down" markets against the
   * recent resolution trend.
   *
   * Logic: if the last N (default 3) resolutions of the same asset all went
   * AGAINST the side we're about to enter, reject the trade.
   *
   * "Against" means:
   *   - We want YES (Up) but last 3 resolved NO (Down) → blocked
   *   - We want NO (Down) but last 3 resolved YES (Up) → blocked
   *
   * Only applies to "Up or Down" binary markets. All other markets pass through.
   */
  filterRecentTrend(trade) {
    const title = trade.market || '';
    const asset = this._extractUpDownAsset(title);

    // Not an Up-or-Down market — pass through
    if (!asset) return { pass: true };

    const side = (trade.side || '').toUpperCase();
    if (!side) return { pass: true };

    const STREAK_THRESHOLD = 3;

    // Pull stored resolution history from DB
    const history = this.db?.getSetting('signal_recentResolutions', []) || [];

    // Also pull from wallet-tracker's resolvedMarkets if available (richer data)
    const wtResolutions = this._getWalletTrackerResolutions(asset);

    // Merge: use DB history first, then fill from wallet-tracker (deduplicated by ts)
    const allResolutions = [...history];
    const existingTs = new Set(allResolutions.map(r => r.ts));
    for (const r of wtResolutions) {
      if (!existingTs.has(r.ts)) allResolutions.push(r);
    }

    // Filter to matching asset and sort newest first
    const matching = allResolutions
      .filter(r => {
        const rAsset = this._extractUpDownAsset(r.market);
        return rAsset === asset;
      })
      .sort((a, b) => (b.ts || 0) - (a.ts || 0))
      .slice(0, STREAK_THRESHOLD);

    // Need at least STREAK_THRESHOLD resolutions to make a judgment
    if (matching.length < STREAK_THRESHOLD) return { pass: true };

    // Check if ALL recent resolutions went against our intended side
    const allAgainst = matching.every(r => {
      const resolved = (r.resolvedSide || '').toUpperCase();
      return resolved && resolved !== side;
    });

    if (allAgainst) {
      const oppositeWord = side === 'YES' ? 'Down/NO' : 'Up/YES';
      return {
        pass: false,
        reason: `Trend filter: last ${STREAK_THRESHOLD} ${asset} resolutions went ${oppositeWord} — betting ${side} goes against trend`
      };
    }

    return { pass: true };
  }

  /**
   * Pull recent resolutions for a given asset from the wallet-tracker's
   * resolvedMarkets Map. Returns an array in the same format as the DB store:
   *   [{market, resolvedSide, ts}]
   */
  _getWalletTrackerResolutions(targetAsset) {
    const results = [];
    if (!this.walletTracker?.resolvedMarkets) return results;

    for (const [, info] of this.walletTracker.resolvedMarkets) {
      const q = info.question || '';
      const rAsset = this._extractUpDownAsset(q);
      if (rAsset !== targetAsset) continue;

      results.push({
        market: q,
        resolvedSide: info.yesWins ? 'YES' : 'NO',
        ts: info.resolvedAt ? new Date(info.resolvedAt).getTime() : 0
      });
    }
    return results;
  }

  /**
   * Record a market resolution into the persistent DB store.
   * Called externally (e.g. from exit-engine or wallet-tracker) when a market resolves.
   *
   * @param {string} market  — full market title
   * @param {boolean} yesWins — true if YES won, false if NO won
   */
  recordResolution(market, yesWins) {
    try {
      const history = this.db?.getSetting('signal_recentResolutions', []) || [];
      history.push({
        market: (market || '').slice(0, 150),
        resolvedSide: yesWins ? 'YES' : 'NO',
        ts: Date.now()
      });
      // Keep only the last 50 entries
      const trimmed = history.slice(-50);
      this.db?.setSetting('signal_recentResolutions', trimmed);
    } catch (e) {
      this.log('warn', 'Failed to record resolution for trend filter', { error: e.message });
    }
  }

  /**
   * X1: Estimate price impact of our own order on the orderbook.
   * Returns { priceImpactPct, shouldReduce }
   */
  async _estimatePriceImpact(market, side, size) {
    try {
      const tokenCacheKey = `tokenIds:${market}`;
      const tokens = await this._apiCache.get(
        tokenCacheKey,
        ApiCache.TTL.MARKET_METADATA,
        () => this.clobClient.resolveTokenIds(market)
      );
      if (!tokens) return { priceImpactPct: 0, shouldReduce: false };

      const tokenId = side === 'YES' ? tokens.yesTokenId : tokens.noTokenId;
      const obCacheKey = `orderbook:${tokenId}`;
      const book = await this._apiCache.get(
        obCacheKey,
        ApiCache.TTL.CLOB_ORDERBOOK,
        () => this.clobClient.getOrderBook(tokenId)
      );
      if (!book?.asks?.length) return { priceImpactPct: 0, shouldReduce: false };

      const asks = book.asks
        .map(a => ({ price: parseFloat(a.price), size: parseFloat(a.size) }))
        .filter(a => a.price > 0 && a.size > 0)
        .sort((a, b) => a.price - b.price);

      if (!asks.length) return { priceImpactPct: 0, shouldReduce: false };

      const bestAsk = asks[0].price;
      let remaining = size / bestAsk;
      let weightedCost = 0;
      let sharesAcquired = 0;

      for (const level of asks) {
        if (remaining <= 0) break;
        const take = Math.min(remaining, level.size);
        weightedCost += take * level.price;
        sharesAcquired += take;
        remaining -= take;
      }

      const avgFill = sharesAcquired > 0 ? weightedCost / sharesAcquired : bestAsk;
      const priceImpactPct = ((avgFill - bestAsk) / bestAsk) * 100;

      return { priceImpactPct, shouldReduce: priceImpactPct > 3 };
    } catch (err) {
      return { priceImpactPct: 0, shouldReduce: false };
    }
  }

  /**
   * Kelly Criterion position sizing.
   *
   * Full Kelly: f* = (p * b - q) / b
   *   where p = win probability, q = 1-p, b = odds (reward/risk ratio)
   *
   * We use FRACTIONAL Kelly (25%) because:
   * - Full Kelly is too aggressive for uncertain edge estimates
   * - 25% Kelly gives ~75% of the growth rate with much lower variance
   * - Protects against win rate estimation errors
   */
  calcCopySize(trade, cfg, confidence = 50) {
    const bankroll = this._getBankroll();
    if (bankroll <= 0) return 1;

    const price = parseFloat(trade.price) || 0.5;
    const walletAddr = trade.wallet_address;

    // Get Wilson-adjusted win rate for Kelly calculation
    let winProb = 0.5;
    let _kellyBest = null; // saved for ST3 CI-width scaling
    if (this.walletTracker && walletAddr) {
      const stats = this.walletTracker.getWalletStats(walletAddr);
      _kellyBest = this._bestWindow(stats);
      if (_kellyBest) {
        winProb = this._wilsonLower(_kellyBest.wins, _kellyBest.wins + _kellyBest.losses);
      }
    }

    // Kelly formula for binary outcomes (fee-adjusted)
    const takerFee = calcTakerFee(price, false); // conservative: assume non-crypto default
    const reward = 1 - price - takerFee; // net payout after fee
    const risk = price;        // cost if lose
    const b = reward / risk;   // odds ratio (fee-adjusted)
    const q = 1 - winProb;

    let kellyFraction = (winProb * b - q) / b;

    // Clamp: never bet negative (no edge) or more than 25% (safety)
    kellyFraction = Math.max(0, Math.min(0.25, kellyFraction));

    // R1: Variance-based Kelly reduction — penalise high-variance wallets.
    // A wallet with std dev of return = 100% of avg win is max penalised (−50%).
    if (this.walletTracker && walletAddr && _kellyBest) {
      const vStats = this.walletTracker.getWalletStats(walletAddr);
      const returnVariance = vStats?.returnVariance || 0;
      if (returnVariance > 0) {
        const wins = _kellyBest.wins || 1;
        const resolved = (_kellyBest.wins || 0) + (_kellyBest.losses || 0);
        // Use _kellyBest.pnl (same time window as wins) to avoid window mismatch
        const avgWin = resolved > 0 && wins > 0 ? Math.abs(_kellyBest.pnl || 1) / wins : 1;
        const variancePenalty = Math.min(0.5, returnVariance / Math.max(0.01, avgWin * avgWin));
        kellyFraction = kellyFraction * (1 - variancePenalty);
      }
    }

    // Apply fractional Kelly (25% of full Kelly)
    const KELLY_FRACTION = 0.25;
    let size = bankroll * kellyFraction * KELLY_FRACTION;

    // Confidence scaling: scale Kelly size by confidence factor
    // Low confidence (30) = 40% of Kelly size, High confidence (90) = 150%
    const confScale = 0.2 + (confidence / 100) * 1.3; // range: 0.2 to 1.5
    size *= confScale;

    // Drawdown reduction: risk engine scales us down when portfolio is in drawdown
    const ddReduction = this.risk?.getDrawdownReduction?.() || 1.0;
    if (ddReduction < 1.0) {
      size *= ddReduction;
      this.log('info', `Drawdown reduction applied: ${(ddReduction * 100).toFixed(0)}%`);
    }

    // Combined loss streak reduction: use the WORSE of wallet streak vs system losses
    // (applying both independently caused double-counting — e.g. 0.50 × 0.50 = 0.25)
    const _streakStats = (this.walletTracker && walletAddr)
      ? this.walletTracker.getWalletStats(walletAddr)
      : null;
    const streak = _streakStats?.currentStreak || 0;
    const sysLosses = this.risk?.state?.consecutiveLosses || 0;
    const worstStreak = Math.max(Math.abs(Math.min(streak, 0)), sysLosses);
    let streakMult = 1.0;
    if (worstStreak >= 7) streakMult = 0.35;
    else if (worstStreak >= 5) streakMult = 0.50;
    else if (worstStreak >= 4) streakMult = 0.60;
    else if (worstStreak >= 3) streakMult = 0.75;
    else if (worstStreak >= 2) streakMult = 0.85;
    size *= streakMult;

    // System-level streak cooling: reduce size during hot streaks to preserve edge
    size *= (this.risk?.getStreakCoolingMultiplier?.() || 1.0);

    // Hard caps
    const maxFromBankroll = bankroll * (cfg.maxBankrollPct || 0.10);
    size = Math.min(size, maxFromBankroll, cfg.maxCopySize);

    // Model risk buffer: safety factor on Kelly sizing (0.90 = 10% reduction)
    size = size * (this.db?.getSetting('signal_modelRiskBuffer', 0.90) || 0.90);

    // ST3: Wilson CI width scaling — wide uncertainty intervals shrink position size.
    // A wallet with 5 trades has a wide CI (lots of uncertainty) → 50% Kelly cap.
    // A wallet with 50+ trades has a narrow CI (well-sampled) → full Kelly.
    if (_kellyBest) {
      const total = _kellyBest.wins + _kellyBest.losses;
      const wilsonLo = winProb; // already computed above
      const wilsonHi = this._wilsonUpper(_kellyBest.wins, total);
      const intervalWidth = wilsonHi - wilsonLo;
      const intervalMultiplier = Math.max(0.5, 1 - intervalWidth * 2);
      size *= intervalMultiplier;
    }

    // R3: Regime-switching Kelly cap
    const _regimeMult = this.risk?.getRegimeMultipliers?.(this._marketContext);
    if (_regimeMult && _regimeMult.kellyCapMultiplier !== 1.0) {
      const _bankroll = this.db?.getSetting('risk_bankroll', 500) || 500;
      const _regimeCap = (cfg.maxBankrollPct || 0.10) * _regimeMult.kellyCapMultiplier * _bankroll;
      size = Math.min(size, _regimeCap);
      if (_regimeMult.label !== 'normal') {
        console.log(`[Signal] R3 ${_regimeMult.label}: cap × ${_regimeMult.kellyCapMultiplier}`);
      }
    }

    // Minimum bet
    size = Math.max(1, +size.toFixed(2));

    // W4: Cross-wallet consensus multiplier — 1.5× if 3+ independent wallets entered same market within 60min
    const consensusMult = this._checkConsensus(trade.market, trade.wallet_address || trade.walletAddress);
    if (consensusMult > 1.0) {
      const maxFromBankrollCap = (cfg.maxBankrollPct || 0.10) * (this.db?.getSetting('risk_bankroll', 500) || 500);
      size = Math.min(size * consensusMult, maxFromBankrollCap);
      size = Math.max(1, +size.toFixed(2));
    }

    // W3: Wallet edge age decay
    // Edge deteriorates as more traders copy the same wallet.
    // After 30 days of sustained edge, apply a 1%/day decay floor at 0.70×.
    if (this.walletTracker && walletAddr) {
      const w3Stats = this.walletTracker.getWalletStats(walletAddr);
      const edgeStart = w3Stats?.edgeStartTimestamp;
      if (edgeStart) {
        const edgeAgeDays = (Date.now() - edgeStart) / (1000 * 60 * 60 * 24);
        if (edgeAgeDays > 30) {
          const decayFactor = Math.max(0.70, 1 - (edgeAgeDays - 30) * 0.01);
          size = size * decayFactor;
          if (decayFactor < 0.95) {
            this.log('info', `W3 edge decay: wallet ${(walletAddr || '?').slice(0, 10)} edge age ${edgeAgeDays.toFixed(0)}d → ${(decayFactor * 100).toFixed(0)}% size`);
          }
        }
      }
    }

    // T2: Pre-event volatility haircut
    const _eventHaircut = this._getPreEventHaircut(trade.market);
    if (_eventHaircut < 1.0) {
      size = size * _eventHaircut;
    }

    this.log('info', 'Kelly sizing', {
      winProb: +(winProb * 100).toFixed(1) + '%',
      odds: +b.toFixed(2),
      kellyFull: +(kellyFraction * 100).toFixed(2) + '%',
      kellyFractional: +(kellyFraction * KELLY_FRACTION * 100).toFixed(3) + '%',
      confidence,
      confScale: +confScale.toFixed(2),
      consensusMult,
      eventHaircut: _eventHaircut,
      size: '$' + size.toFixed(2),
      bankroll: '$' + bankroll.toFixed(2)
    });

    return size;
  }

  /**
   * T2: Pre-scheduled event volatility haircut.
   * Returns a size multiplier (0.40 = 60% reduction) if market resolves near a major event.
   * Uses known recurring event dates + hardcoded 2026 schedule.
   */
  _getPreEventHaircut(market) {
    try {
      const title = (market || '').toLowerCase();
      const now = new Date();

      // Known 2026 FOMC dates (approximate — 8 per year)
      const fomcDates2026 = [
        '2026-01-28', '2026-03-18', '2026-05-06', '2026-06-17',
        '2026-07-29', '2026-09-16', '2026-11-04', '2026-12-16'
      ].map(d => new Date(d));

      // CPI release: usually 2nd Tuesday of month at 8:30am ET
      // NFP: usually 1st Friday of month
      // We check if today or tomorrow is within 24h of any event

      const allEvents = [...fomcDates2026];

      // Add next CPI and NFP (rough approximation: check 2nd Tuesday and 1st Friday)
      const year = now.getFullYear();
      const month = now.getMonth();
      for (let m = month; m <= month + 2; m++) {
        // 2nd Tuesday (CPI)
        const d = new Date(year, m, 1);
        let tuesdays = 0;
        while (tuesdays < 2) { if (d.getDay() === 2) tuesdays++; if (tuesdays < 2) d.setDate(d.getDate() + 1); }
        allEvents.push(new Date(d));
        // 1st Friday (NFP)
        const f = new Date(year, m, 1);
        while (f.getDay() !== 5) f.setDate(f.getDate() + 1);
        allEvents.push(new Date(f));
      }

      const WINDOW_MS = 24 * 60 * 60 * 1000;
      const isNearEvent = allEvents.some(evt => Math.abs(evt - now) < WINDOW_MS);

      if (!isNearEvent) return 1.0;

      // Only apply to crypto markets (this system trades crypto only)
      const cryptoTerms = ['bitcoin', 'btc', 'ethereum', 'eth', 'crypto', 'solana', 'sol'];
      const isCrypto = cryptoTerms.some(t => title.includes(t));
      if (!isCrypto) return 1.0;

      console.log(`[Signal] T2 pre-event haircut: 40% size on "${title.slice(0, 40)}"`);
      return 0.40; // 60% reduction
    } catch (err) {
      return 1.0;
    }
  }

  /**
   * Proportional sizing: mirror the whale's conviction level.
   * If whale bets 5% of their estimated portfolio, user bets 5% of bankroll.
   *
   * Formula: user_bet = (whale_bet / whale_portfolio) * user_bankroll
   *
   * whale_portfolio is estimated from accumulated volume or manual override.
   * Falls back to flat ratio if whale portfolio estimate is unavailable.
   */
  _proportionalSize(trade, cfg) {
    const bankroll = this._getBankroll();
    const whalePortfolio = parseFloat(trade.wallet_portfolio || trade.volume) || 0;

    if (whalePortfolio <= 0 || bankroll <= 0) {
      // Fallback to flat ratio when we can't estimate the whale's portfolio
      this.log('info', 'Proportional sizing fallback — no portfolio estimate', {
        wallet: trade.wallet_name, volume: trade.volume
      });
      return Math.min(trade.size * cfg.copyRatio, cfg.maxCopySize);
    }

    // What fraction of their portfolio is this bet?
    const convictionPct = trade.size / whalePortfolio;

    // Apply conviction floor/ceiling to avoid tiny or huge bets from noisy estimates
    const minConviction = cfg.minConvictionPct || 0.005;  // 0.5% floor
    const maxConviction = cfg.maxConvictionPct || 0.20;    // 20% ceiling
    const clampedConviction = Math.max(minConviction, Math.min(maxConviction, convictionPct));

    // Mirror that conviction on user's bankroll
    const rawSize = clampedConviction * bankroll;

    // Hard cap: never bet more than maxBankrollPct of bankroll (default 10%)
    const maxBankrollBet = bankroll * (cfg.maxBankrollPct || 0.10);
    const finalSize = Math.min(rawSize, cfg.maxCopySize, maxBankrollBet);

    this.log('info', 'Proportional sizing', {
      wallet: trade.wallet_name,
      whaleBet: trade.size,
      whalePortfolio,
      convictionPct: (convictionPct * 100).toFixed(2) + '%',
      clampedPct: (clampedConviction * 100).toFixed(2) + '%',
      bankroll,
      maxBankrollBet: maxBankrollBet.toFixed(2),
      rawSize: rawSize.toFixed(2),
      finalSize: finalSize.toFixed(2)
    });

    return Math.max(1, +finalSize.toFixed(2)); // Minimum $1 bet
  }

  // ── Market time-to-close check ──────────────────────────────────────

  /**
   * Check if a market is too close to closing to enter safely.
   * For 5m markets: need at least 60 seconds remaining.
   * For longer markets: need at least 5 minutes remaining.
   */
  async _checkMarketTimeRemaining(signal) {
    try {
      const tokens = await this.clobClient.resolveTokenIds(signal.market);
      if (!tokens?.endDate) return { pass: true }; // No end date, proceed

      const endTime = new Date(tokens.endDate).getTime();
      const now = Date.now();
      const remainingMs = endTime - now;

      if (remainingMs <= 0) {
        return { pass: false, reason: 'Market has already ended' };
      }

      // Determine minimum time based on market duration
      const remainingSec = remainingMs / 1000;
      const MIN_SECONDS_5M = 60;   // 1 minute minimum for 5m markets
      const MIN_SECONDS_OTHER = 300; // 5 minutes for longer markets

      // Detect if this is a short-duration market (< 30 min)
      const is5mMarket = (signal.market || '').toLowerCase().match(/5\s*m|5\s*min/);
      const minSeconds = is5mMarket ? MIN_SECONDS_5M : MIN_SECONDS_OTHER;

      if (remainingSec < minSeconds) {
        return {
          pass: false,
          reason: `Only ${Math.round(remainingSec)}s remaining (need ${minSeconds}s min)`
        };
      }

      return { pass: true, remainingSeconds: Math.round(remainingSec) };
    } catch (e) {
      return { pass: true }; // On error don't block
    }
  }

  // ── Order splitting ─────────────────────────────────────────────────

  /**
   * Split large orders into smaller chunks to reduce market impact.
   * Orders above $50 get split into $20-30 chunks with slight delays between them.
   */
  async _splitAndExecute(signal, callback) {
    const CHUNK_MAX = 30; // Max $30 per chunk
    const CHUNK_MIN = 5;  // Don't split below $5
    const totalSize = parseFloat(signal.size) || 0;

    if (totalSize <= CHUNK_MAX || totalSize <= CHUNK_MIN) {
      // Small enough — single order
      return await callback(signal);
    }

    // Split into chunks
    const numChunks = Math.ceil(totalSize / CHUNK_MAX);
    const chunkSize = +(totalSize / numChunks).toFixed(2);
    const results = [];
    let filled = 0;

    this.log('info', `Order splitting: $${totalSize} → ${numChunks} × $${chunkSize}`, { market: signal.market });

    for (let i = 0; i < numChunks; i++) {
      const remaining = +(totalSize - filled).toFixed(2);
      const thisChunk = Math.min(chunkSize, remaining);
      if (thisChunk < CHUNK_MIN) break;

      const chunkSignal = { ...signal, size: thisChunk, chunk: i + 1, totalChunks: numChunks };

      try {
        const result = await callback(chunkSignal);
        results.push({ chunk: i + 1, size: thisChunk, success: true, result });
        filled += thisChunk;
      } catch (e) {
        this.log('warn', `Chunk ${i + 1}/${numChunks} failed: ${e.message}`);
        results.push({ chunk: i + 1, size: thisChunk, success: false, error: e.message });
        // Don't retry immediately — stop splitting if a chunk fails
        break;
      }

      // Small delay between chunks (200-500ms) to avoid detection
      if (i < numChunks - 1) {
        await new Promise(r => setTimeout(r, 200 + Math.random() * 300));
      }
    }

    return { split: true, totalSize, filled, chunks: results };
  }

  // ── Order type selection (X2) ──────────────────────────────────────

  /**
   * X2: Select between market and limit orders based on queue depth and signal age.
   *
   * Rules:
   *   - queueDepthAhead > 20 AND signalAge < 10s  → market order (speed priority)
   *   - queueDepthAhead < 5  AND signalAge < 30s  → limit at ask - 0.005 (price priority)
   *   - signalAge > 30s                           → limit at ask + 0.003 (fill certainty)
   *   - default                                   → market order
   *
   * @param {object} signal   - The signal object (uses signal.price as reference ask)
   * @param {number} signalAge - Milliseconds since signal was created
   * @param {number} [queueDepthAhead] - Number of ask levels at or below target price
   * @returns {{ orderType: 'market'|'limit', limitPrice: number|null, reason: string }}
   */
  _selectOrderType(signal, signalAge, queueDepthAhead = null) {
    const bestAsk = parseFloat(signal.price) || 0;
    const ageSeconds = signalAge / 1000;

    // queueDepthAhead unknown — fall through to age-only rules
    if (queueDepthAhead !== null) {
      if (queueDepthAhead > 20 && ageSeconds < 10) {
        return {
          orderType: 'market',
          limitPrice: null,
          reason: `X2: deep queue (${queueDepthAhead} levels) + fresh signal (${ageSeconds.toFixed(1)}s) → market order`
        };
      }
      if (queueDepthAhead < 5 && ageSeconds < 30) {
        const limitPrice = bestAsk > 0 ? +(bestAsk - 0.005).toFixed(4) : null;
        return {
          orderType: 'limit',
          limitPrice,
          reason: `X2: thin queue (${queueDepthAhead} levels) + fresh signal (${ageSeconds.toFixed(1)}s) → limit @ ${limitPrice}`
        };
      }
    }

    if (ageSeconds > 30) {
      const limitPrice = bestAsk > 0 ? +(bestAsk + 0.003).toFixed(4) : null;
      return {
        orderType: 'limit',
        limitPrice,
        reason: `X2: stale signal (${ageSeconds.toFixed(1)}s > 30s) → limit @ ${limitPrice} for fill certainty`
      };
    }

    return {
      orderType: 'market',
      limitPrice: null,
      reason: `X2: default → market order (age ${ageSeconds.toFixed(1)}s, queue unknown)`
    };
  }

  // ── Retry logic ────────────────────────────────────────────────────

  /**
   * Retry failed order execution with exponential backoff.
   * Max 2 retries, with price re-validation between attempts.
   * X2: selects market vs limit order based on queue depth and signal age.
   */
  async _executeWithRetry(signal, callback, maxRetries = 2) {
    const RETRY_TIMEOUT_MS = 15000;
    const retryStartTime = Date.now();
    let lastError = null;

    // X2: Determine order type before the first attempt.
    // signalAge is measured from signal.timestamp (ISO string set at signal creation).
    const _signalCreatedAt = signal.timestamp ? new Date(signal.timestamp).getTime() : Date.now();
    const _signalAge = Date.now() - _signalCreatedAt;

    let _queueDepthAhead = null;
    if (this.clobClient?.isReady()) {
      try {
        const tokenCacheKey = `tokenIds:${signal.market}`;
        const _tokens = await this._apiCache.get(
          tokenCacheKey,
          ApiCache.TTL.MARKET_METADATA,
          () => this.clobClient.resolveTokenIds(signal.market)
        );
        if (_tokens) {
          const _tokenId = signal.side === 'YES' ? _tokens.yesTokenId : _tokens.noTokenId;
          const obCacheKey = `orderbook:${_tokenId}`;
          const _book = await this._apiCache.get(
            obCacheKey,
            ApiCache.TTL.CLOB_ORDERBOOK,
            () => this.clobClient.getOrderBook(_tokenId)
          );
          if (_book?.asks?.length > 0) {
            // Count ask levels at or below the signal's target price (these are ahead of us)
            const _targetPrice = parseFloat(signal.price) || 0;
            _queueDepthAhead = _book.asks.filter(a => parseFloat(a.price) <= _targetPrice).length;
          }
        }
      } catch (_qErr) { /* non-blocking — fall back to null (age-only rules) */ }
    }

    const _orderTypeResult = this._selectOrderType(signal, _signalAge, _queueDepthAhead);
    signal.orderType = _orderTypeResult.orderType;
    signal.limitPrice = _orderTypeResult.limitPrice;

    this.log('info', _orderTypeResult.reason, { market: signal.market });
    if (this.audit) {
      try {
        this.audit.record('ORDER_TYPE_SELECTED', {
          market: signal.market,
          orderType: _orderTypeResult.orderType,
          limitPrice: _orderTypeResult.limitPrice,
          reason: _orderTypeResult.reason,
          signalAgeMs: _signalAge,
          queueDepth: _queueDepthAhead
        });
      } catch (_auditErr) { /* non-fatal */ }
    }

    for (let attempt = 0; attempt <= maxRetries; attempt++) {
      try {
        if (Date.now() - retryStartTime > RETRY_TIMEOUT_MS) {
          return { success: false, error: 'Retry timeout exceeded', attempts: attempt };
        }
        if (attempt > 0) {
          // Wait before retry: 1s, then 3s
          const delay = attempt * 2000;
          this.log('info', `Retry attempt ${attempt}/${maxRetries} after ${delay}ms`, { market: signal.market });
          await new Promise(r => setTimeout(r, delay));

          // Re-validate price before retry
          if (this.clobClient?.isReady()) {
            try {
              const tokens = await this.clobClient.resolveTokenIds(signal.market);
              if (tokens) {
                const tokenId = signal.side === 'YES' ? tokens.yesTokenId : tokens.noTokenId;
                const book = await this.clobClient.getOrderBook(tokenId);
                if (book?.asks?.length > 0) {
                  const currentAsk = parseFloat(book.asks[0].price) || 0;
                  const origPrice = parseFloat(signal.price) || 0;
                  if (origPrice > 0 && currentAsk > 0 && (currentAsk - origPrice) / origPrice > 0.10) {
                    this.log('info', 'Retry aborted: price moved too far during retries');
                    return { success: false, reason: 'Price moved during retry', attempts: attempt };
                  }
                  signal.price = currentAsk; // Update to current price
                  // X2: update limitPrice if we're using a limit order
                  if (signal.orderType === 'limit' && signal.limitPrice !== null) {
                    const wasAsk = signal.limitPrice > origPrice; // fill-certainty mode (ask + 0.003)
                    signal.limitPrice = wasAsk
                      ? +(currentAsk + 0.003).toFixed(4)
                      : +(currentAsk - 0.005).toFixed(4);
                  }
                }
              }
            } catch (e) { /* best effort */ }
          }
        }

        const expectedFillPrice = signal.price;
        // WAL: record intent before first execution attempt
        if (attempt === 0) {
          try { this._wal?.writeIntent({ id: signal.id || signal.market, market: signal.market, side: signal.side, size: signal.size, price: signal.price }); } catch {}
        }
        const result = await callback(signal);
        if (attempt > 0) {
          this.log('info', `Order succeeded on retry ${attempt}`, { market: signal.market });
        }
        // WAL: mark committed after successful execution
        try { this._wal?.markCommitted(signal.id || signal.market); } catch {}
        // Fill quality audit
        if (this.audit && attempt === 0) {
          try {
            const actualFillPrice = result?.filledPrice || result?.price || signal.price;
            this.audit.record('FILL_QUALITY', {
              market: signal.market,
              expectedPrice: expectedFillPrice,
              actualPrice: actualFillPrice,
              slippagePct: +((actualFillPrice - expectedFillPrice) / expectedFillPrice * 100).toFixed(3),
              orderSize: signal.size,
              orderType: signal.orderType || 'market',
              hourUTC: new Date().getUTCHours()
            });
          } catch (e) {}
        }
        return { success: true, result, attempts: attempt + 1 };
      } catch (e) {
        lastError = e;
        this.log('warn', `Order attempt ${attempt + 1} failed: ${e.message}`, { market: signal.market });

        // Classify error — don't retry permanent failures
        const status = e.status || e.statusCode || e.response?.status;
        const msg = (e.message || '').toLowerCase();
        const isNonRetryable = [400, 401, 403].includes(status)
          || msg.includes('duplicate') || msg.includes('insufficient')
          || msg.includes('unauthorized') || msg.includes('invalid order')
          || msg.includes('bad request') || msg.includes('cloudflare');
        if (isNonRetryable) {
          this.log('info', `Non-retryable error (${status || msg.slice(0, 40)}), aborting retries`, { market: signal.market });
          return { success: false, error: e.message, attempts: attempt + 1, nonRetryable: true };
        }
      }
    }

    return { success: false, error: lastError?.message, attempts: maxRetries + 1 };
  }

  // ── Slippage guard ──────────────────────────────────────────────────

  /**
   * Fetch live market price and compare to whale's entry.
   * Rejects if price has moved more than maxSlippagePct since the whale entered.
   */
  async _checkSlippage(signal, walletTrade) {
    const maxSlippage = this.risk?.getConfig()?.maxSlippagePct || 5;

    try {
      const tokens = await this.clobClient.resolveTokenIds(signal.market);
      if (!tokens) return { pass: true }; // Can't check, proceed

      // Check if market is still active
      if (tokens.active === false) {
        return { pass: false, reason: 'Market is closed/resolved' };
      }

      const tokenId = signal.side === 'YES' ? tokens.yesTokenId : tokens.noTokenId;
      const livePrice = await this.clobClient.getPrice(tokenId, 'BUY');
      if (!livePrice || livePrice <= 0) return { pass: true };

      const whalePrice = parseFloat(walletTrade.price) || 0;
      if (whalePrice <= 0) return { pass: true, livePrice };

      // Calculate slippage
      const slippagePct = ((livePrice - whalePrice) / whalePrice) * 100;

      if (slippagePct > maxSlippage) {
        return {
          pass: false,
          reason: `Price slipped ${slippagePct.toFixed(1)}% since whale entry ($${whalePrice.toFixed(3)} → $${livePrice.toFixed(3)}, max ${maxSlippage}%)`
        };
      }

      // If price actually improved (went down for a buy), that's fine
      return { pass: true, livePrice, slippagePct: +slippagePct.toFixed(2) };
    } catch (e) {
      this.log('warn', 'Slippage check failed', { error: e.message });
      return { pass: true }; // On error don't block
    }
  }

  // ── W4: Cross-wallet consensus multiplier ────────────────────────

  /**
   * W4: Cross-wallet consensus check.
   * Returns a size multiplier: 1.5 if 3+ independent wallets entered same market in last 60min.
   */
  _checkConsensus(market, wallet) {
    try {
      const WINDOW_MS = 60 * 60 * 1000; // 60 minutes
      const now = Date.now();
      const key = (market || '').toLowerCase().slice(0, 60);
      if (!key) return 1.0;

      // Clean up old entries
      const entries = (this._recentMarketEntries.get(key) || [])
        .filter(e => now - e.timestamp < WINDOW_MS);

      // Count distinct wallets already seen (excluding current)
      const distinctWallets = new Set(entries.map(e => e.wallet));
      distinctWallets.delete(wallet);

      // Record this wallet's entry
      entries.push({ wallet, timestamp: now });
      this._recentMarketEntries.set(key, entries);

      // Clean old keys to prevent memory leak (keep only last 500 markets)
      if (this._recentMarketEntries.size > 500) {
        const oldestKey = this._recentMarketEntries.keys().next().value;
        this._recentMarketEntries.delete(oldestKey);
      }

      // 3+ distinct wallets (including current) = consensus
      const totalDistinct = distinctWallets.size + 1;
      if (totalDistinct >= 3) {
        this.log('info', `W4 consensus: ${totalDistinct} wallets on "${key.slice(0, 40)}" → 1.5× size`);
        return 1.5;
      }
      return 1.0;
    } catch (err) {
      this.log('warn', '_checkConsensus error: ' + err.message);
      return 1.0;
    }
  }

  // ── M3: Volume acceleration filter ───────────────────────────────

  /**
   * M3: Record a volume tick for a market. Called by monitor when any trade is seen.
   */
  recordVolumeTick(market) {
    const key = (market || '').toLowerCase().slice(0, 60);
    if (!key) return;
    const ticks = this._marketVolumeTicks.get(key) || [];
    ticks.push(Date.now());
    // Keep only last 2 hours of ticks
    const cutoff = Date.now() - 2 * 60 * 60 * 1000;
    this._marketVolumeTicks.set(key, ticks.filter(t => t > cutoff));
  }

  /**
   * M3: Check if volume is accelerating for a market.
   * Compares recent 15min volume vs prior 15-45min volume.
   * Returns false (skip) if recent volume is <50% of prior volume.
   */
  _checkVolumeAccelerating(market) {
    try {
      const key = (market || '').toLowerCase().slice(0, 60);
      const ticks = this._marketVolumeTicks.get(key) || [];
      const now = Date.now();
      const recent = ticks.filter(t => now - t < 15 * 60 * 1000).length;
      const prior = ticks.filter(t => {
        const age = now - t;
        return age >= 15 * 60 * 1000 && age < 45 * 60 * 1000;
      }).length;

      // Need at least 3 prior ticks to have a meaningful baseline
      if (prior < 3) return true; // not enough data — allow through
      if (recent < prior * 0.5) {
        this.log('info', `M3 volume decel: market "${key.slice(0, 40)}" recent=${recent} prior=${prior} — skipping`);
        return false;
      }
      return true;
    } catch (err) {
      return true; // on error, allow through
    }
  }

  // ── Expected value gate ────────────────────────────────────────────

  /**
   * Calculate expected value of the trade.
   * EV = (winRate * profit_if_win) - (lossRate * cost_if_loss)
   * For binary markets: profit = (1 - price) * size, loss = price * size
   * Reject if EV < 0 or below minimum threshold.
   */
  _checkExpectedValue(signal, walletTrade, liq = null) {
    const walletAddr = walletTrade.wallet_address;

    // Use Wilson-adjusted win rate (conservative estimate)
    let winRate = null;
    if (this.walletTracker && walletAddr) {
      const stats = this.walletTracker.getWalletStats(walletAddr);
      const best = this._bestWindow(stats);
      if (best) {
        winRate = this._wilsonLower(best.wins, best.wins + best.losses);
      }
    }

    if (winRate === null) return { pass: true }; // Not enough data

    const price = parseFloat(signal.price) || 0;
    if (price <= 0 || price >= 1) return { pass: true };

    // True all-in cost: account for spread and price impact
    const spreadCost = liq ? (liq.bestAsk - liq.bestBid) / 2 : 0;
    const impactCost = liq ? (signal.size / (liq.askLiquidity * 0.3 || 1000)) * price : 0;
    const allInPrice = Math.min(0.99, price + spreadCost + impactCost);

    const calibratedPrice = this._calibrateMarketPrice(allInPrice);
    const takerFeeEv = calcTakerFee(calibratedPrice, false); // conservative: assume non-crypto default
    const profitIfWin = 1 - calibratedPrice - takerFeeEv;
    const costIfLoss = calibratedPrice;
    let ev = (winRate * profitIfWin) - ((1 - winRate) * costIfLoss);
    const evPerDollar = ev / price;

    // Dynamic EV threshold: require at least 1 cent EV per share
    // But for high-confidence wallets with 20+ resolved trades, accept 0.5 cents
    const stats = this.walletTracker?.getWalletStats(walletAddr);
    const best = this._bestWindow(stats);
    const sampleSize = best?.resolvedTrades || 0;
    const minEV = sampleSize >= 20 ? 0.02 : 0.03;

    // M5: Creator quality EV haircut
    const _creatorMult = this._getCreatorQualityMultiplier(signal?.market);
    if (_creatorMult < 1.0) {
      ev = ev * _creatorMult;
      console.log(`[Signal] M5 creator quality ${_creatorMult}× applied to EV`);
    }

    if (ev < minEV) {
      return {
        pass: false,
        reason: `Low EV: ${(ev * 100).toFixed(1)}¢/share (adj WR ${(winRate * 100).toFixed(0)}% × $${profitIfWin.toFixed(2)} - ${((1 - winRate) * 100).toFixed(0)}% × $${costIfLoss.toFixed(2)}). Need ${(minEV * 100).toFixed(1)}¢+`,
        ev
      };
    }

    this.log('info', 'EV check passed', {
      ev: (ev * 100).toFixed(1) + '¢/share',
      adjWinRate: (winRate * 100).toFixed(0) + '%',
      price: price.toFixed(3),
      evPerDollar: evPerDollar.toFixed(3)
    });

    return { pass: true, ev, evPerDollar };
  }

  // ── M5: Market creator track record ─────────────────────────────────

  /**
   * M5: Market creator track record multiplier.
   * Returns 0.85 for creators with poor dispute history, 1.0 for good creators.
   */
  _getCreatorQualityMultiplier(market) {
    try {
      const stats = this.db?.getSetting('market_creator_stats', {});
      if (!stats || Object.keys(stats).length === 0) return 1.0;

      // Key by first 30 chars of market title (lowercased)
      const marketKey = (market || '').toLowerCase().slice(0, 30);
      const creatorStat = stats[marketKey];
      if (!creatorStat) return 1.0;

      const disputeRate = creatorStat.disputes / Math.max(creatorStat.total, 1);
      if (disputeRate > 0.20) return 0.85;
      if (disputeRate > 0.10) return 0.92;
      return 1.0;
    } catch (err) {
      return 1.0;
    }
  }

  // ── Liquidity check ─────────────────────────────────────────────────

  // ── X7: Spoof Detection ─────────────────────────────────────────────────────

  /**
   * Record a bestAsk snapshot for a market. Detects spoofing by looking for
   * bestAsk price spikes (>5%) that revert within one snapshot cycle — a pattern
   * consistent with large ask orders placed and cancelled to create false liquidity.
   * Uses bestAsk (from checkLiquidity) rather than raw order levels, since the
   * CLOB checkLiquidity helper does not return individual order entries.
   */
  _recordOrderbookSnapshot(market, liq) {
    if (!market || !liq || liq.bestAsk == null) return;
    const now = Date.now();
    const WINDOW_MS = 5 * 60 * 1000; // 5-minute rolling window

    if (!this._spoofTracker.has(market)) {
      this._spoofTracker.set(market, { lastBestAsk: liq.bestAsk, spoofEvents: [], lastTs: now });
      return; // Nothing to compare on the first snapshot
    }

    const state = this._spoofTracker.get(market);
    const prev = state.lastBestAsk;
    const curr = liq.bestAsk;

    // A spoof pattern: prev ask was significantly higher than current ask
    // (large phantom ask appeared last cycle at high price, now gone → price snapped back)
    // Also catches: prev ask was low, it spiked up and back: covered by the reverse
    if (prev > 0 && curr > 0) {
      const change = (prev - curr) / curr; // positive = ask dropped (previous high ask vanished)
      if (change > 0.05) {
        // Best ask dropped >5% from last snapshot — a large high ask vanished without a trade
        state.spoofEvents.push({ ts: now, prevAsk: prev, currAsk: curr });
        this.log('debug', `X7 Spoof event on ${market}: bestAsk dropped ${(change * 100).toFixed(1)}% (${prev.toFixed(3)} → ${curr.toFixed(3)}) — possible ask cancellation`);
      }
    }

    // Prune events outside the rolling window
    state.spoofEvents = state.spoofEvents.filter(e => now - e.ts < WINDOW_MS);

    // Update snapshot
    state.lastBestAsk = curr;
    state.lastTs = now;
  }

  /**
   * Returns a sizing multiplier based on recent spoof activity for a market.
   *   0 events  → 1.0  (normal)
   *   1-2 events → 0.8  (minor reduction)
   *   3-4 events → 0.5  (major reduction, log SPOOFING_DETECTED)
   *   5+ events  → 0.0  (skip entirely)
   */
  _getSpoofSizingMultiplier(market) {
    if (!market) return 1.0;
    const state = this._spoofTracker.get(market);
    if (!state) return 1.0;
    const count = state.spoofEvents.length;
    if (count >= 5) return 0.0;   // Skip entirely
    if (count >= 3) return 0.5;   // Cut size by half — SPOOFING_DETECTED
    if (count >= 1) return 0.8;   // Minor reduction
    return 1.0;
  }

  // ── End X7 ──────────────────────────────────────────────────────────────────

  async _checkLiquidity(signal, walletTrade = null) {
    if (!this.clobClient?.isReady()) return { pass: true };
    try {
      // I3: Cache token ID resolution (5-minute TTL — token IDs don't change)
      const tokenCacheKey = `tokenIds:${signal.market}`;
      const tokens = await this._apiCache.get(
        tokenCacheKey,
        ApiCache.TTL.MARKET_METADATA,
        () => this.clobClient.resolveTokenIds(signal.market)
      );
      if (!tokens) return { pass: true };
      const tokenId = signal.side === 'YES' ? tokens.yesTokenId : tokens.noTokenId;
      const liq = await this.clobClient.checkLiquidity(tokenId, 500);
      if (!liq.sufficient) {
        return {
          pass: false,
          reason: `Low liquidity: bids $${liq.bidLiquidity}, asks $${liq.askLiquidity} (need $500+)`
        };
      }
      // Also reject if spread is too wide (>3%)
      if (liq.spread > 3) {
        return {
          pass: false,
          reason: `Spread too wide: ${liq.spread}% (bid $${liq.bestBid} / ask $${liq.bestAsk})`
        };
      }
      // Orderbook consumption check: if whale consumed more than the available liquidity,
      // our fill price will be severely degraded
      if (walletTrade) {
        const whaleSize = parseFloat(walletTrade.size) || 0;
        if (whaleSize > 0 && liq.askLiquidity > 0) {
          const consumptionRatio = whaleSize / liq.askLiquidity;
          if (consumptionRatio > 1.5) {
            const degradedPrice = signal.price * (1 + consumptionRatio * 0.03);
            const conservativeWR = 0.55;
            const adjustedEV = (conservativeWR * (1 - degradedPrice)) - ((1 - conservativeWR) * degradedPrice);
            if (adjustedEV < 0.005) {
              return { pass: false, reason: `Ask liquidity consumed by whale — est. fill at ${(degradedPrice*100).toFixed(1)}¢ eliminates edge` };
            }
            // Reduce our size proportionally but still allow entry
            return { pass: true, liquidity: liq, adjustSize: Math.max(1, +(signal.size / consumptionRatio).toFixed(2)) };
          }
        }
      }
      return { pass: true, liquidity: liq };
    } catch (e) {
      return { pass: true };
    }
  }

  /**
   * Smart eviction: when at max positions, check if the new signal's wallet
   * has been performing better than any existing position's wallet over the last 3 days.
   * If so, evict the worst-performing position to make room.
   */
  async _trySmartEviction(signal) {
    if (!this.walletTracker || !this.risk) return { success: false };

    // R6: Use EV (confidence × size) as the comparison metric instead of raw win rate.
    // This means we only evict a position if the new signal is clearly better EV.
    const newSignalEV = signal.originalEV || (signal.confidence * signal.size);

    // Find the weakest open position by its stored EV (or fall back to win rate proxy)
    const positions = this.risk.state?.openPositions || [];
    if (positions.length === 0) return { success: false };

    let worstPos = null;
    let worstEV = Infinity;

    for (const pos of positions) {
      if (!pos.copied_from_address) continue;
      // Use stored originalEV if available; otherwise estimate from confidence × size
      const posEV = pos.originalEV != null
        ? pos.originalEV
        : (pos.confidence || 50) * (parseFloat(pos.size || pos.amount) || 1);
      if (posEV < worstEV) {
        worstEV = posEV;
        worstPos = pos;
      }
    }

    // Only evict if new signal EV is >30% higher than the weakest position
    if (!worstPos || newSignalEV <= worstEV * 1.30) {
      this.log('info', 'Smart eviction (R6): new signal EV not sufficiently better', {
        newSignalEV: +newSignalEV.toFixed(2), worstEV: +worstEV.toFixed(2),
        worstWallet: worstPos?.copied_from
      });
      return { success: false };
    }

    this.log('info', 'Smart eviction (R6): replacing weakest-EV position', {
      evicting: worstPos.copied_from, evictedEV: +worstEV.toFixed(2),
      newWallet: signal.copied_from, newSignalEV: +newSignalEV.toFixed(2),
      market: worstPos.market
    });

    // Evict the position
    if (this.evictionCallback) {
      try {
        await this.evictionCallback(worstPos, 'smart_eviction');
      } catch (e) {
        this.log('warn', 'Eviction callback failed', { error: e.message });
        return { success: false };
      }
    } else {
      // Fallback: just remove from risk engine directly
      this.risk.recordResult(worstPos.id, 0);
    }

    return { success: true, evicted: worstPos };
  }

  _getBankroll() {
    // In dry run: always act as if we have $50 — unlimited virtual budget
    const dryRun = this.risk?.getConfig()?.dryRun || false;
    if (dryRun) return 50;

    if (this.risk) {
      try { return this.risk.getConfig().bankroll || 500; } catch (e) {}
    }
    if (this.db) {
      return this.db.getSetting('risk_bankroll', 500);
    }
    return 500;
  }

  /**
   * Calculate confidence score using Wilson Score interval for win rate,
   * combined with EV, timing, and market context signals.
   * Returns 0-100 score that drives position sizing via Kelly.
   */
  async calcConfidence(trade, cfg) {
    let score = 0;
    const factors = {};

    const price = parseFloat(trade.price) || 0.5;
    const walletAddr = trade.wallet_address;

    // ── Factor 1: Win rate with sample-size adjustment (Wilson Score) ──
    // Raw WR of 100% on 3 trades != 100% on 50 trades
    let adjWinRate = 0.5; // prior: assume 50% with no data
    if (this.walletTracker && walletAddr) {
      const stats = this.walletTracker.getWalletStats(walletAddr);
      const best = this._bestWindow(stats);
      if (best) {
        adjWinRate = this._wilsonLower(best.wins, best.wins + best.losses);
        factors.rawWR = best.winRate;
        factors.adjWR = +(adjWinRate * 100).toFixed(1);
        factors.sampleSize = best.resolvedTrades;
      }
    }
    // Survival bias correction: small samples overstate edge due to selection
    const sampleSize = this.walletTracker && walletAddr ? (() => {
      const stats = this.walletTracker.getWalletStats(walletAddr);
      const best = this._bestWindow(stats);
      return best?.resolvedTrades || 0;
    })() : 0;
    const survivalCorrection = sampleSize < 30 ? 0.88 : sampleSize < 100 ? 0.93 : 0.97;
    adjWinRate = adjWinRate * survivalCorrection;

    // Wilson-adjusted WR drives 40% of confidence
    score += (adjWinRate - 0.5) * 80; // 50% WR = 0 pts, 75% = +20, 90% = +32

    // Calibrated price for EV calculation (favorite-longshot bias correction)
    const rawPrice = parseFloat(trade.price) || 0.5;
    const calibratedConfPrice = this._calibrateMarketPrice(rawPrice);
    factors.calibratedPrice = +calibratedConfPrice.toFixed(3);

    // ── Factor 2: Expected Value per dollar risked ──
    const reward = 1 - calibratedConfPrice;
    const cost = calibratedConfPrice;
    const ev = (adjWinRate * reward) - ((1 - adjWinRate) * cost);
    const evPerDollar = calibratedConfPrice > 0 ? ev / calibratedConfPrice : 0;
    factors.ev = +(ev * 100).toFixed(2);
    factors.evPerDollar = +evPerDollar.toFixed(4);
    // EV drives 25% of confidence
    score += Math.min(25, Math.max(-25, evPerDollar * 50));

    // ── Factor 3: Entry price sweet spot ──
    // Best entries are 0.15-0.50 (high reward/risk). Penalize extremes.
    if (price >= 0.15 && price <= 0.50) {
      score += 15; // Sweet spot: great risk/reward
      factors.priceZone = 'sweet_spot';
    } else if (price > 0.50 && price <= 0.70) {
      score += 5;
      factors.priceZone = 'moderate';
    } else if (price > 0.70) {
      score -= 10;
      factors.priceZone = 'expensive';
    } else {
      score += 8; // Very cheap, decent r/r but might be noise
      factors.priceZone = 'cheap';
    }

    // ── Factor 4: Wallet momentum (3d vs 7d trend) ──
    if (this.walletTracker && walletAddr) {
      const stats = this.walletTracker.getWalletStats(walletAddr);
      if (stats?.d3?.winRate !== null && stats?.d7?.winRate !== null &&
          stats.d3.resolvedTrades >= 3 && stats.d7.resolvedTrades >= 5) {
        const momentum = stats.d3.winRate - stats.d7.winRate;
        if (momentum > 5) { score += 8; factors.momentum = 'improving'; }
        else if (momentum < -10) { score -= 12; factors.momentum = 'declining'; }
        else { factors.momentum = 'stable'; }
      }
    }

    // ── Factor 5: Trade size conviction (z-score vs wallet's historical bet sizes) ──
    const tradeSize = parseFloat(trade.size) || 0;
    const walletBetStats = this.walletTracker?.getWalletStats(walletAddr);
    const betSizeMean = walletBetStats?.betSizeMean || tradeSize;
    const betSizeStd = walletBetStats?.betSizeStd || 1;
    const betSizeZScore = (tradeSize - betSizeMean) / Math.max(betSizeStd, 1);
    if (betSizeZScore > 2) { score += 12; factors.whaleConviction = 'very_high_zscore'; }
    else if (betSizeZScore > 1) { score += 6; factors.whaleConviction = 'high_zscore'; }
    else if (betSizeZScore < -1) { score -= 5; factors.whaleConviction = 'below_avg'; }
    else { factors.whaleConviction = 'normal'; }
    factors.betSizeZScore = +betSizeZScore.toFixed(2);

    // ── Factor 6: Wallet P&L health ──
    if (this.walletTracker && walletAddr) {
      const stats = this.walletTracker.getWalletStats(walletAddr);
      if (stats?.d7?.pnl !== undefined) {
        if (stats.d7.pnl > 500) { score += 5; factors.walletPnL = 'profitable'; }
        else if (stats.d7.pnl < -200) { score -= 10; factors.walletPnL = 'losing'; }
      }
    }

    // ── Factor 7: Market context awareness ──
    if (this._marketContext) {
      const ctx = this._marketContext;
      if (ctx.regime === 'high_volatility') {
        score -= 10;
        factors.marketRegime = 'high_vol (-10)';
      } else if (ctx.regime === 'low_volatility' && ctx.volumeLevel !== 'low') {
        score += 5;
        factors.marketRegime = 'calm (+5)';
      }
      if (ctx.activityTrend > 2.0) {
        score += 3;
        factors.activityTrend = 'accelerating (+3)';
      } else if (ctx.activityTrend < 0.3) {
        score -= 5;
        factors.activityTrend = 'decelerating (-5)';
      }
    }

    // ── Factor 8: Learning adjustment from post-trade outcomes ──
    const confAdj = this.getWalletConfidenceAdj(walletAddr);
    if (confAdj !== 0) {
      score += confAdj;
      factors.learningAdj = confAdj;
    }

    // ── Factor 9: Hour-of-day performance prior ──
    const hourlyData = this.db?.getSetting('analytics_hourlyWinRate', null);
    const currentHour = new Date().getUTCHours();
    if (hourlyData?.[currentHour]?.trades >= 10) {
      const hourWR = hourlyData[currentHour].wins / hourlyData[currentHour].trades;
      score += (hourWR - 0.55) * 30; // +/- up to ~15 pts
      factors.hourOfDay = `${currentHour}UTC (${(hourWR*100).toFixed(0)}%WR)`;
    } else {
      // Hard-coded crypto priors until enough data accumulates
      const cat = (trade.market || '').toLowerCase();
      if (/bitcoin|btc|eth|crypto|solana/.test(cat)) {
        if (currentHour >= 13 && currentHour <= 21) { score += 5; factors.hourOfDay = 'us_hours (+5)'; }
        else if (currentHour >= 22 || currentHour <= 6) { score -= 7; factors.hourOfDay = 'asia_night (-7)'; }
      }
    }

    // ── Factor 10: Funding rate sentiment for crypto markets ──
    const mktLower = (trade.market || '').toLowerCase();
    if (this._fundingRates && /bitcoin|btc|eth|ethereum|crypto|solana/.test(mktLower)) {
      const rate = this._fundingRates.BTC || 0;
      if (rate > 0.0005) { score += 5; factors.fundingRate = 'bullish (+5)'; }
      else if (rate < -0.0002) { score -= 8; factors.fundingRate = 'bearish (-8)'; }
      else { factors.fundingRate = 'neutral'; }
    }

    // ── Factor 11: Category-specific Bayesian prior (ST1) ──
    // If the wallet has a proven track record in THIS specific market category
    // (crypto / politics / sports), use that category-specific WR as an
    // additional signal rather than relying solely on their overall WR.
    if (this.walletTracker && walletAddr) {
      const stats = this.walletTracker.getWalletStats(walletAddr);
      const catStats = stats?.categoryStats;
      if (catStats) {
        let detectedCat = null;
        if (/bitcoin|btc|ethereum|eth|crypto|solana/.test(mktLower)) detectedCat = 'crypto';
        else if (/nba|nfl|mlb|playoff|championship|spread|moneyline/.test(mktLower)) detectedCat = 'sports';
        else if (/election|president|senate|congress|vote/.test(mktLower)) detectedCat = 'politics';

        if (detectedCat && catStats[detectedCat] && catStats[detectedCat].total >= 10) {
          const catWilson = catStats[detectedCat].wilsonLower;
          const overallWilson = adjWinRate; // already computed above
          const categoryDelta = catWilson - overallWilson;
          // Bonus/penalty: up to ±10 pts based on how the wallet specialises (or struggles)
          const catBonus = Math.max(-10, Math.min(10, Math.round(categoryDelta * 40)));
          if (catBonus !== 0) {
            score += catBonus;
            factors.categoryPrior = `${detectedCat} ${catBonus > 0 ? '+' : ''}${catBonus} (n=${catStats[detectedCat].total})`;
          }
        }
      }
    }

    // ── Factor 12: Day-of-week performance prior (T1) ──
    // Crypto markets have been shown to behave differently across the week.
    // If the wallet has ≥5 trades on today's day of week in this category,
    // apply a ±5 multiplier based on whether this is historically a good or
    // bad day for that wallet/category combination.
    if (this.walletTracker && walletAddr) {
      const dow = new Date().getDay(); // 0=Sun, 6=Sat
      const dowStats = this.walletTracker.getWalletStats(walletAddr)?.dowWinRate;
      if (dowStats) {
        let detectedCatDow = 'other';
        if (/bitcoin|btc|ethereum|eth|crypto|solana/.test(mktLower)) detectedCatDow = 'crypto';
        else if (/nba|nfl|mlb|playoff|championship/.test(mktLower)) detectedCatDow = 'sports';
        else if (/election|president|senate|congress|vote/.test(mktLower)) detectedCatDow = 'politics';

        const dowKey = `${detectedCatDow}_${dow}`;
        const dowWR = dowStats[dowKey]; // null if insufficient data
        if (dowWR !== null && dowWR !== undefined) {
          // Overall win rate for this category (use adjWinRate as proxy)
          const dowMultiplier = Math.max(0.75, Math.min(1.25, dowWR / Math.max(0.01, adjWinRate)));
          // Map multiplier to score delta: 1.25 → +5, 0.75 → -5
          const dowDelta = Math.round((dowMultiplier - 1) * 20);
          if (dowDelta !== 0) {
            score += dowDelta;
            factors.dayOfWeekPrior = `dow${dow} ${dowDelta > 0 ? '+' : ''}${dowDelta} (wr=${(dowWR * 100).toFixed(0)}%)`;
          }
        }
      }
    }

    // M4: Ambiguity penalty
    const ambiguityPenalty = this._calcAmbiguityPenalty(trade.market);
    if (ambiguityPenalty < 0) {
      score += ambiguityPenalty;
      factors.ambiguityPenalty = ambiguityPenalty;
    }

    // ── Factor W2: Entry timing relative to market lifespan ──
    // Wallets that consistently enter in the first 20% of a market's lifespan
    // have informational edge (they act before the crowd prices it in).
    // Require at least 15 total trades before applying the bonus/penalty.
    if (this.walletTracker && walletAddr) {
      const w2Stats = this.walletTracker.getWalletStats(walletAddr);
      const w2Total = w2Stats?.totalTrades || 0;
      if (w2Total >= 15) {
        const earlyRatio = (w2Stats.earlyEntries || 0) / w2Total;
        const lateRatio  = (w2Stats.lateEntries  || 0) / w2Total;
        if (earlyRatio > 0.50) {
          score += 8;
          factors.entryTiming = `early_${(earlyRatio * 100).toFixed(0)}pct (+8)`;
        } else if (lateRatio > 0.60) {
          score -= 5;
          factors.entryTiming = `late_${(lateRatio * 100).toFixed(0)}pct (-5)`;
        } else {
          factors.entryTiming = 'neutral';
        }
      } else {
        factors.entryTiming = 'insufficient_data';
      }
    }

    // ── Factor ST4: Autocorrelation momentum/fade bonus ──
    // Requires > 30 resolved trades and a non-null AC1 value on wallet stats.
    // Streaky wallets (AC1 > 0.15) get a bonus during win streaks.
    // Mean-reverting wallets (AC1 < -0.15) get a fade bonus during loss streaks
    // (the wallet statistically tends to recover after a run of losses).
    // Gate: only when resolvedAll-time trades > 30 (proxy: d30.resolvedTrades).
    if (this.walletTracker && walletAddr) {
      const ac1Stats = this.walletTracker.getWalletStats(walletAddr);
      const ac1 = ac1Stats?.ac1;
      const streak = ac1Stats?.currentStreak ?? 0;
      const enoughData = (ac1Stats?.d30?.resolvedTrades || 0) > 30;

      if (enoughData && ac1 !== null && ac1 !== undefined) {
        if (ac1 > 0.15 && streak > 1) {
          // Streaky wallet currently on a win streak — momentum favours continuation
          const bonus = Math.min(8, ac1 * 40);
          score += bonus;
          factors.autocorr = `streaky_bonus_+${bonus.toFixed(1)}`;
        } else if (ac1 < -0.15 && streak < -1) {
          // Mean-reverting wallet currently on a loss streak — fade signal: recovery likely
          const bonus = Math.min(5, Math.abs(ac1) * 25);
          score += bonus;
          factors.autocorr = `meanrev_fade_bonus_+${bonus.toFixed(1)}`;
        } else {
          factors.autocorr = ac1 !== null ? `ac1_${ac1.toFixed(3)}_no_signal` : 'ac1_null';
        }
      } else {
        factors.autocorr = enoughData ? 'ac1_null' : 'ac1_insufficient_data';
      }
    }

    // ── Factor Z2: Sentiment velocity and crowd analysis ──
    if (this._sentiment && trade.conditionId) {
      try {
        const sentiment = await this._sentiment.scoreMarket(trade.conditionId);
        const adj = this._sentiment.computeConfidenceAdjustment(sentiment, trade.side || 'YES');
        if (adj.delta !== 0) {
          score += adj.delta;
          factors.sentimentAdj = adj.reason;
          factors.sentimentScore = sentiment.score;
          factors.sentimentVelocity = sentiment.velocity;
        }
      } catch (_sentErr) { /* non-blocking */ }
    }

    const finalScore = Math.max(0, Math.min(100, Math.round(30 + score)));
    factors.finalScore = finalScore;
    this._lastConfidenceFactors = factors; // Store for explainability
    return finalScore;
  }

  /**
   * M4: Resolution ambiguity scoring.
   * Returns a confidence penalty (0 to -20) based on ambiguous words in the market title.
   * Called during calcConfidence, not as a hard filter.
   */
  _calcAmbiguityPenalty(market) {
    if (!market) return 0;
    const title = market.toLowerCase();
    const ambiguousTerms = [
      'approximately', 'roughly', 'about', 'around', 'likely', 'probably',
      'expected', 'estimated', 'projected', 'forecast', 'predicted',
      'sufficient', 'adequate', 'significant', 'notable', 'substantial',
      'major', 'minor', 'most', 'many', 'few', 'some'
    ];
    let penalty = 0;
    for (const term of ambiguousTerms) {
      if (title.includes(term)) {
        penalty -= 5;
        if (penalty <= -20) break; // cap at -20
      }
    }
    return penalty;
  }

  /**
   * Log a rejected signal to rejected-signals.jsonl for opportunity cost analysis.
   */
  _logRejectedSignal(walletTrade, reason) {
    try {
      const entry = {
        timestamp: Date.now(),
        conditionId: walletTrade.conditionId || null,
        market: walletTrade.market,
        rejectReason: reason,
        marketPrice: walletTrade.price,
        walletAddress: walletTrade.wallet_address,
        walletName: walletTrade.wallet_name || null,
        side: walletTrade.side,
        size: walletTrade.size || null,
        action: 'rejected'
      };
      // In-memory ring buffer (visible to UI via /api/signal/rejections)
      this._recentRejections.push(entry);
      if (this._recentRejections.length > this._MAX_REJECTIONS) {
        this._recentRejections.shift();
      }
      this._persistActivityLog();
    } catch (e) { /* non-fatal */ }
  }

  getRecentRejections(limit = 50) {
    return this._recentRejections.slice(-Math.min(limit, this._MAX_REJECTIONS)).reverse();
  }

  _persistActivityLog() {
    if (!this.db || this._activityLogTimer) return;
    this._activityLogTimer = setTimeout(() => {
      this._activityLogTimer = null;
      // Keep last 200 entries in DB
      const toSave = this._recentRejections.slice(-this._MAX_REJECTIONS);
      try { this.db.setSetting('signal_activityLog', toSave); } catch (e) { /* non-blocking */ }
    }, 2000);
  }

  /**
   * Favorite-longshot bias calibration: adjusts raw market prices for systematic
   * over/under-pricing of favorites (high p) and longshots (low p).
   */
  _calibrateMarketPrice(rawPrice) {
    if (rawPrice > 0.85) return rawPrice * 0.92 + 0.05;
    if (rawPrice < 0.15) return rawPrice * 1.10;
    return rawPrice * 0.97 + 0.015;
  }

  /**
   * Wilson Score lower bound — conservative win rate estimate that accounts for sample size.
   * With 3 wins out of 3, this returns ~0.44 (not 1.0). With 30 wins out of 30, returns ~0.89.
   * z = 1.96 for 95% confidence interval.
   */
  _wilsonLower(wins, total) {
    if (total === 0) return 0.5;
    const z = 1.96;
    const p = wins / total;
    const denominator = 1 + (z * z) / total;
    const centre = p + (z * z) / (2 * total);
    const spread = z * Math.sqrt((p * (1 - p) + (z * z) / (4 * total)) / total);
    return Math.max(0, (centre - spread) / denominator);
  }

  // ST3: Wilson upper confidence bound (mirrors _wilsonLower)
  _wilsonUpper(wins, total) {
    if (total === 0) return 0.5;
    const z = 1.96;
    const p = wins / total;
    const denominator = 1 + (z * z) / total;
    const centre = p + (z * z) / (2 * total);
    const spread = z * Math.sqrt((p * (1 - p) + (z * z) / (4 * total)) / total);
    return Math.min(1, (centre + spread) / denominator);
  }

  /**
   * Pick the best time window that has enough data.
   * Prefers d7 if enough trades, falls back to d3, then d30.
   */
  _bestWindow(stats) {
    if (!stats) return null;
    if (stats.d7.resolvedTrades >= 5) return stats.d7;
    if (stats.d3.resolvedTrades >= 3) return stats.d3;
    if (stats.d30.resolvedTrades >= 10) return stats.d30;
    return null;
  }

  // ── Config ────────────────────────────────────────────────────────

  getConfig() {
    if (!this.db) return this.defaults();
    return {
      minOriginalSize:   this.db.getSetting('signal_minOriginalSize', 5),
      minWinRate:        this.db.getSetting('signal_minWinRate', 53),
      maxCopySize:       this.db.getSetting('signal_maxCopySize', 25),
      copyRatio:         this.db.getSetting('signal_copyRatio', 0.05),
      copyDelayMs:       this.db.getSetting('signal_copyDelayMs', 2000),
      minPrice:          this.db.getSetting('signal_minPrice', 0.05),
      maxPrice:          this.db.getSetting('signal_maxPrice', 0.99),
      allowedCategories: this.db.getSetting('signal_allowedCategories', []),
      // Proportional sizing
      sizingMode:        this.db.getSetting('signal_sizingMode', 'proportional'),
      minConvictionPct:  this.db.getSetting('signal_minConvictionPct', 0.005),
      maxConvictionPct:  this.db.getSetting('signal_maxConvictionPct', 0.10),
      maxBankrollPct:    this.db.getSetting('signal_maxBankrollPct', 0.10),
      maxMarketDurationMinutes: this.db.getSetting('signal_maxMarketDurationMinutes', 1440),
      minMarketDurationMinutes: this.db.getSetting('signal_minMarketDurationMinutes', 1),
      // Phase 3: assume maker fee (lower) instead of taker fee
      assume_maker_fee: this.db.getSetting('assume_maker_fee', false) ?? false,
    };
  }

  defaults() {
    return {
      minOriginalSize: 5, minWinRate: 53, maxCopySize: 25, copyRatio: 0.05,
      copyDelayMs: 2000, minPrice: 0.05, maxPrice: 0.99, allowedCategories: [],
      sizingMode: 'proportional', minConvictionPct: 0.005, maxConvictionPct: 0.10,
      maxBankrollPct: 0.10, maxMarketDurationMinutes: 1440, minMarketDurationMinutes: 1
    };
  }

  // ── Trade Learning Engine ─────────────────────────────────────────
  /**
   * Analyze closed trades to learn what's winning and what's losing.
   * Returns actionable insights about patterns in wins vs losses.
   */
  analyzeTradePatterns() {
    if (!this.db) return null;
    const trades = this.db.getTradeHistory(200) || [];
    const closed = trades.filter(t => (t.status === 'closed' || t.status === 'won' || t.status === 'lost') && t.pnl !== null);
    if (closed.length < 3) return { message: 'Not enough closed trades to analyze', trades: closed.length };

    const wins = closed.filter(t => t.pnl > 0);
    const losses = closed.filter(t => t.pnl <= 0);

    const analysis = {
      totalTrades: closed.length,
      wins: wins.length,
      losses: losses.length,
      winRate: +((wins.length / closed.length) * 100).toFixed(1),
      totalPnL: +closed.reduce((s, t) => s + t.pnl, 0).toFixed(2),
      avgWinPnL: wins.length > 0 ? +(wins.reduce((s, t) => s + t.pnl, 0) / wins.length).toFixed(2) : 0,
      avgLossPnL: losses.length > 0 ? +(losses.reduce((s, t) => s + t.pnl, 0) / losses.length).toFixed(2) : 0,
      patterns: {},
      insights: []
    };

    // Pattern: entry price ranges
    const priceRanges = { low: { w: 0, l: 0 }, mid: { w: 0, l: 0 }, high: { w: 0, l: 0 } };
    for (const t of closed) {
      const p = parseFloat(t.price) || 0;
      const bucket = p < 0.35 ? 'low' : p < 0.65 ? 'mid' : 'high';
      if (t.pnl > 0) priceRanges[bucket].w++; else priceRanges[bucket].l++;
    }
    analysis.patterns.byEntryPrice = {};
    for (const [k, v] of Object.entries(priceRanges)) {
      const total = v.w + v.l;
      if (total > 0) analysis.patterns.byEntryPrice[k] = { wins: v.w, losses: v.l, winRate: +((v.w / total) * 100).toFixed(0), count: total };
    }

    // Pattern: by side (YES vs NO)
    const bySide = { YES: { w: 0, l: 0 }, NO: { w: 0, l: 0 } };
    for (const t of closed) {
      const side = (t.side || 'YES').toUpperCase();
      if (bySide[side]) { if (t.pnl > 0) bySide[side].w++; else bySide[side].l++; }
    }
    analysis.patterns.bySide = {};
    for (const [k, v] of Object.entries(bySide)) {
      const total = v.w + v.l;
      if (total > 0) analysis.patterns.bySide[k] = { wins: v.w, losses: v.l, winRate: +((v.w / total) * 100).toFixed(0), count: total };
    }

    // Pattern: by wallet copied from
    const byWallet = {};
    for (const t of closed) {
      const key = t.copied_from || 'unknown';
      if (!byWallet[key]) byWallet[key] = { w: 0, l: 0, pnl: 0 };
      if (t.pnl > 0) byWallet[key].w++; else byWallet[key].l++;
      byWallet[key].pnl += t.pnl;
    }
    analysis.patterns.byWallet = {};
    for (const [k, v] of Object.entries(byWallet)) {
      const total = v.w + v.l;
      analysis.patterns.byWallet[k] = { wins: v.w, losses: v.l, winRate: +((v.w / total) * 100).toFixed(0), pnl: +v.pnl.toFixed(2), count: total };
    }

    // Pattern: by market type
    const byType = {};
    for (const t of closed) {
      const m = (t.market || '').toLowerCase();
      const type = m.includes('bitcoin') ? 'BTC' : m.includes('ethereum') ? 'ETH' : m.includes('solana') ? 'SOL' : 'Other';
      if (!byType[type]) byType[type] = { w: 0, l: 0, pnl: 0 };
      if (t.pnl > 0) byType[type].w++; else byType[type].l++;
      byType[type].pnl += t.pnl;
    }
    analysis.patterns.byMarketType = {};
    for (const [k, v] of Object.entries(byType)) {
      const total = v.w + v.l;
      analysis.patterns.byMarketType[k] = { wins: v.w, losses: v.l, winRate: +((v.w / total) * 100).toFixed(0), pnl: +v.pnl.toFixed(2), count: total };
    }

    // Generate insights
    // Best price range
    const bestPrice = Object.entries(analysis.patterns.byEntryPrice).sort((a, b) => b[1].winRate - a[1].winRate)[0];
    if (bestPrice && bestPrice[1].count >= 3) {
      analysis.insights.push(`Best entry price range: ${bestPrice[0]} (${bestPrice[1].winRate}% win rate, ${bestPrice[1].count} trades)`);
    }

    // Best wallet
    const bestWallet = Object.entries(analysis.patterns.byWallet).sort((a, b) => b[1].pnl - a[1].pnl)[0];
    if (bestWallet) {
      analysis.insights.push(`Most profitable wallet: ${bestWallet[0]} (${bestWallet[1].winRate}% WR, $${bestWallet[1].pnl} P&L)`);
    }
    const worstWallet = Object.entries(analysis.patterns.byWallet).sort((a, b) => a[1].pnl - b[1].pnl)[0];
    if (worstWallet && worstWallet[1].pnl < 0) {
      analysis.insights.push(`Worst wallet: ${worstWallet[0]} (${worstWallet[1].winRate}% WR, $${worstWallet[1].pnl} P&L) — consider removing`);
    }

    // Risk/reward observation
    if (analysis.avgLossPnL !== 0 && Math.abs(analysis.avgLossPnL) > analysis.avgWinPnL * 2) {
      analysis.insights.push(`Losses are ${(Math.abs(analysis.avgLossPnL) / (analysis.avgWinPnL || 1)).toFixed(1)}x larger than wins — need better risk/reward entries`);
    }

    return analysis;
  }

  /**
   * Auto-discover the best wallets based on tracker data.
   * Prioritizes win rate and P&L over volume.
   * Returns up to `count` wallets with full stats.
   */
  findTrustedWallets(count = 3) {
    if (!this.walletTracker) return [];

    const candidates = [];
    for (const [addr] of this.walletTracker.walletTrades) {
      const stats = this.walletTracker.getWalletStats(addr);
      if (!stats) continue;

      // Need at least some resolved trades
      const resolved = Math.max(stats.d3.resolvedTrades, stats.d7.resolvedTrades);
      if (resolved < 5) continue;

      const wr = stats.d7.resolvedTrades >= 5 ? stats.d7.winRate :
                 stats.d3.resolvedTrades >= 3 ? stats.d3.winRate : null;
      if (wr === null || wr < 60) continue;

      const pnl = stats.d7.pnl;
      const avgSize = stats.d7.avgSize;

      // Score: win rate is king (60%), P&L profitability (25%), consistency via Sharpe (15%)
      let score = (wr / 100) * 60;
      if (pnl > 0) score += Math.min(25, (pnl / 500) * 25); // cap at $500+ P&L
      const sharpe = this.walletTracker.getSharpeRatio(addr);
      if (sharpe !== null && sharpe > 0) score += Math.min(15, sharpe * 10);

      // Penalty for buying at extreme prices (bad risk/reward)
      const trades = this.walletTracker.walletTrades.get(addr) || [];
      const recentBuys = trades.filter(t => t.action === 'BUY' && t.resolved).slice(-20);
      const avgPrice = recentBuys.length > 0
        ? recentBuys.reduce((s, t) => s + (t.price || 0), 0) / recentBuys.length
        : 0.5;
      if (avgPrice > 0.85) score -= 20; // Buys near $1 = terrible risk/reward
      if (avgPrice < 0.40) score += 5;  // Low entry prices = good risk/reward

      // Penalty for negative P&L despite high win rate (means bad risk/reward)
      if (pnl < 0 && wr > 70) score -= 15;

      candidates.push({
        address: addr,
        score: +score.toFixed(2),
        winRate: wr,
        pnl: +pnl.toFixed(2),
        resolved,
        avgSize: +avgSize.toFixed(2),
        avgEntryPrice: +avgPrice.toFixed(3),
        sharpe,
        stats
      });
    }

    return candidates
      .sort((a, b) => b.score - a.score)
      .slice(0, count);
  }

  static ALLOWED_SETTINGS = [
    'minOriginalSize', 'minWinRate', 'maxCopySize', 'copyRatio',
    'copyDelayMs', 'minPrice', 'maxPrice', 'allowedCategories',
    'sizingMode', 'minConvictionPct', 'maxConvictionPct', 'maxBankrollPct',
    'maxMarketDurationMinutes', 'minMarketDurationMinutes', 'focusedWallets', 'minRiskRewardRatio', 'modelRiskBuffer'
  ];

  setSetting(key, value) {
    if (!SignalEngine.ALLOWED_SETTINGS.includes(key)) {
      this.log('warn', `Rejected unknown signal setting: ${key}`);
      return false;
    }
    if (this.db) this.db.setSetting('signal_' + key, value);
    return true;
  }

  // ── Post-Trade Learning Loop ───────────────────────────────────────
  /**
   * Called after every trade closes (win or loss).
   * Updates wallet confidence scores and learns from the outcome.
   * This is the continuous learning loop from the spec.
   */
  postTradeUpdate(tradeResult) {
    if (!tradeResult || !this.walletTracker) return;

    const { wallet_address, pnl, entryPrice, side, market, maeUsd } = tradeResult;
    if (!wallet_address) return;

    // ── R4: Record Max Adverse Excursion (MAE) ──
    // maeUsd is the most-negative unrealized P&L seen during the trade's life.
    // Aggregating this across trades reveals which wallets have high intra-trade
    // volatility — they need smaller Kelly fractions to survive the swings.
    if (maeUsd !== undefined && maeUsd !== null && this.db) {
      try {
        const maeHistory = this.db.getSetting('signal_maeHistory', {}) || {};
        if (!maeHistory[wallet_address]) maeHistory[wallet_address] = [];
        const size = parseFloat(tradeResult.size) || 1;
        const entry = parseFloat(entryPrice) || 0.5;
        const maeFraction = (entry * size) > 0 ? Math.abs(maeUsd) / (entry * size) : 0;
        maeHistory[wallet_address].push({ ts: Date.now(), maeUsd, maeFraction });
        if (maeHistory[wallet_address].length > 50) {
          maeHistory[wallet_address] = maeHistory[wallet_address].slice(-50);
        }
        this.db.setSetting('signal_maeHistory', maeHistory);
      } catch (e) { /* non-fatal */ }
    }

    // Update per-wallet confidence adjustments
    if (!this._walletConfidenceAdj) this._walletConfidenceAdj = {};
    if (!this._walletConfidenceAdj[wallet_address]) {
      this._walletConfidenceAdj[wallet_address] = 0;
    }

    // Bayesian-ish update: wins boost confidence slightly, losses reduce it more
    // This creates a natural "trust decay" that requires consistent performance
    if (pnl > 0) {
      this._walletConfidenceAdj[wallet_address] = Math.min(15,
        this._walletConfidenceAdj[wallet_address] + 2);
    } else {
      this._walletConfidenceAdj[wallet_address] = Math.max(-20,
        this._walletConfidenceAdj[wallet_address] - 4);
    }

    // Learn from entry price patterns
    const price = parseFloat(entryPrice) || 0;
    if (!this._priceZoneResults) this._priceZoneResults = { cheap: { w: 0, l: 0 }, sweet: { w: 0, l: 0 }, moderate: { w: 0, l: 0 }, expensive: { w: 0, l: 0 } };
    const zone = price < 0.15 ? 'cheap' : price <= 0.50 ? 'sweet' : price <= 0.70 ? 'moderate' : 'expensive';
    if (pnl > 0) this._priceZoneResults[zone].w++; else this._priceZoneResults[zone].l++;

    this.log('info', 'Post-trade learning update', {
      wallet: wallet_address.slice(0, 10) + '...',
      pnl: pnl > 0 ? '+$' + pnl.toFixed(2) : '-$' + Math.abs(pnl).toFixed(2),
      confAdj: this._walletConfidenceAdj[wallet_address],
      priceZone: zone,
      zoneRecord: this._priceZoneResults[zone]
    });

    // Update strategy engine (multi-armed bandit)
    if (this.strategyEngine && tradeResult.strategyId) {
      this.strategyEngine.recordOutcome(tradeResult.strategyId, pnl);
    }

    // Cap walletConfidenceAdj at 2000 entries
    const adjKeys = Object.keys(this._walletConfidenceAdj);
    if (adjKeys.length > 2000) {
      for (let i = 0; i < adjKeys.length - 1500; i++) delete this._walletConfidenceAdj[adjKeys[i]];
    }

    // Persist learning state
    if (this.db) {
      try {
        this.db.setSetting('signal_walletConfAdj', this._walletConfidenceAdj);
        this.db.setSetting('signal_priceZoneResults', this._priceZoneResults);
      } catch (e) {}
    }
  }

  /**
   * Load persisted learning state on startup.
   */
  loadLearningState() {
    if (!this.db) return;
    try {
      this._walletConfidenceAdj = this.db.getSetting('signal_walletConfAdj', {}) || {};
      this._priceZoneResults = this.db.getSetting('signal_priceZoneResults', null) ||
        { cheap: { w: 0, l: 0 }, sweet: { w: 0, l: 0 }, moderate: { w: 0, l: 0 }, expensive: { w: 0, l: 0 } };
    } catch (e) {}
  }

  /**
   * Bootstrap the learning state from all resolved wallet-tracker history.
   * Called on startup when the learning state is empty (or undersized) relative
   * to how many resolved trades the tracker already knows about.
   *
   * This seeds _walletConfidenceAdj and _priceZoneResults so the signal engine
   * immediately benefits from 5000+ historical resolved trades instead of
   * starting blind and learning over months.
   *
   * Safe to call multiple times — exits early if the state is already rich.
   */
  bootstrapLearningState() {
    if (!this.walletTracker) return;

    const walletTrades = this.walletTracker.walletTrades; // Map<addr, trade[]>
    if (!walletTrades || walletTrades.size === 0) return;

    // Count total resolved trades already reflected in price zone results
    const existingTotal = Object.values(this._priceZoneResults || {})
      .reduce((s, z) => s + (z.w || 0) + (z.l || 0), 0);

    // Count resolved trades available from tracker
    let availableResolved = 0;
    for (const trades of walletTrades.values()) {
      availableResolved += trades.filter(t => t.resolved && t.won !== null && t.action === 'BUY').length;
    }

    // If learning state already reflects >80% of available data, skip
    if (existingTotal >= availableResolved * 0.8) {
      this.log('info', 'Learning state already populated — skipping bootstrap', {
        existingTotal, availableResolved
      });
      return;
    }

    this.log('info', 'Bootstrapping learning state from tracker history', {
      wallets: walletTrades.size, availableResolved, existingTotal
    });

    // ── 1. Recompute price zone results from scratch ──
    const zones = { cheap: { w: 0, l: 0 }, sweet: { w: 0, l: 0 }, moderate: { w: 0, l: 0 }, expensive: { w: 0, l: 0 } };

    // ── 2. Compute wallet-level adjustments ──
    const newAdj = {};
    const BREAKEVEN_WR = 0.667; // equilibrium of the +2/-4 asymmetric scheme

    for (const [addr, trades] of walletTrades) {
      const resolved = trades.filter(t => t.action === 'BUY' && t.resolved && t.won !== null);
      if (resolved.length < 5) continue; // too few trades to be meaningful

      // Tally wins and losses for price zones
      for (const t of resolved) {
        const p = parseFloat(t.price) || 0.5;
        const zone = p < 0.15 ? 'cheap' : p <= 0.50 ? 'sweet' : p <= 0.70 ? 'moderate' : 'expensive';
        if (t.won) zones[zone].w++; else zones[zone].l++;
      }

      // Wallet-level confidence adjustment using Wilson lower bound
      const wins = resolved.filter(t => t.won).length;
      const total = resolved.length;
      const wilsonLower = this._wilsonLower(wins, total);

      // Map Wilson WR → confidence adjustment:
      //   WR >= 0.667 → scales 0 to +15
      //   WR <  0.667 → scales 0 to -20
      // Dampen by sample size so small wallets don't get full adjustment
      const sampleDamp = Math.min(1, total / 30); // full weight at 30+ trades
      let adj;
      if (wilsonLower >= BREAKEVEN_WR) {
        adj = Math.round((wilsonLower - BREAKEVEN_WR) / (1 - BREAKEVEN_WR) * 15 * sampleDamp);
      } else {
        adj = Math.round((wilsonLower - BREAKEVEN_WR) / BREAKEVEN_WR * 20 * sampleDamp);
      }
      newAdj[addr] = Math.max(-20, Math.min(15, adj));
    }

    // Only update wallets not yet in the live learning state
    // (live postTradeUpdate results take priority if they already exist)
    let updated = 0;
    for (const [addr, adj] of Object.entries(newAdj)) {
      if (!(addr in this._walletConfidenceAdj)) {
        this._walletConfidenceAdj[addr] = adj;
        updated++;
      }
    }

    // Replace price zone results wholesale if we have richer data
    if (availableResolved > existingTotal) {
      this._priceZoneResults = zones;
    }

    this.log('info', 'Bootstrap complete', {
      walletsSeeded: updated,
      priceZones: zones,
      topWallets: Object.entries(newAdj)
        .sort((a, b) => b[1] - a[1])
        .slice(0, 5)
        .map(([a, v]) => `${a.slice(0, 10)}:${v > 0 ? '+' : ''}${v}`)
    });

    // Persist immediately
    if (this.db) {
      try {
        this.db.setSetting('signal_walletConfAdj', this._walletConfidenceAdj);
        this.db.setSetting('signal_priceZoneResults', this._priceZoneResults);
      } catch (e) {}
    }
  }

  /**
   * Get the learning-adjusted confidence bonus for a wallet.
   */
  getWalletConfidenceAdj(walletAddr) {
    return this._walletConfidenceAdj?.[walletAddr] || 0;
  }

  /**
   * Generate a human-readable explanation of WHY a trade would be taken.
   * Called by the dashboard to show reasoning for recent/pending signals.
   */
  explainTrade(walletTrade) {
    const factors = [];
    const price = parseFloat(walletTrade.price) || 0.5;
    const walletAddr = walletTrade.wallet_address;

    // Win rate analysis
    if (this.walletTracker && walletAddr) {
      const stats = this.walletTracker.getWalletStats(walletAddr);
      const best = this._bestWindow(stats);
      if (best) {
        const rawWR = best.winRate;
        const adjWR = +(this._wilsonLower(best.wins, best.wins + best.losses) * 100).toFixed(1);
        factors.push(`Win rate: ${rawWR}% raw → ${adjWR}% adjusted (${best.resolvedTrades} trades)`);
      }
    }

    // EV
    const reward = 1 - price;
    const cost = price;
    let winProb = 0.5;
    if (this.walletTracker && walletAddr) {
      const stats = this.walletTracker.getWalletStats(walletAddr);
      const best = this._bestWindow(stats);
      if (best) winProb = this._wilsonLower(best.wins, best.wins + best.losses);
    }
    const ev = (winProb * reward) - ((1 - winProb) * cost);
    factors.push(`Expected value: ${(ev * 100).toFixed(1)}¢/share (${ev > 0 ? 'positive edge' : 'no edge'})`);

    // Kelly sizing
    const b = reward / cost;
    const kelly = Math.max(0, (winProb * b - (1 - winProb)) / b);
    factors.push(`Kelly fraction: ${(kelly * 100).toFixed(2)}% of bankroll`);

    // Price zone
    const zone = price < 0.15 ? 'very cheap (high variance)' : price <= 0.50 ? 'sweet spot (good r/r)' : price <= 0.70 ? 'moderate' : 'expensive (bad r/r)';
    factors.push(`Entry price: $${price.toFixed(3)} — ${zone}`);

    // Learning adjustment
    const confAdj = this.getWalletConfidenceAdj(walletAddr);
    if (confAdj !== 0) {
      factors.push(`Learning adjustment: ${confAdj > 0 ? '+' : ''}${confAdj} (from past trade outcomes)`);
    }

    return {
      decision: ev > 0.01 ? 'COPY' : ev > 0 ? 'MARGINAL' : 'SKIP',
      factors,
      metrics: { ev: +(ev * 100).toFixed(2), kelly: +(kelly * 100).toFixed(2), adjWinRate: +(winProb * 100).toFixed(1), price }
    };
  }

  async findBestOpenOpportunity(availableCapital) {
    if (!this.walletTracker || !this.risk) return;
    try {
      const openPositionMarkets = new Set(
        (this.risk.state?.openPositions || []).map(p => p.market)
      );
      const cfg = this.getConfig();
      const focusedWallets = cfg.focusedWallets || [];
      const now = Date.now();
      const windowMs = 60 * 60 * 1000; // look back 60 minutes

      let best = null;
      let bestScore = -Infinity;

      for (const walletAddr of focusedWallets) {
        const trades = this.walletTracker.walletTrades?.get(walletAddr) || [];
        const recent = trades.filter(t =>
          t.action === 'BUY' &&
          !t.resolved &&
          now - new Date(t.timestamp).getTime() < windowMs &&
          !openPositionMarkets.has(t.market)
        );
        for (const t of recent) {
          const score = this._lastConfidenceFactors?.finalScore ||
            await this._quickScore(walletAddr, t).catch(() => 50);
          const size = Math.min(availableCapital * 0.5, this.calcCopySize(t, cfg, score));
          if (size >= 1 && score > bestScore) {
            bestScore = score;
            best = { trade: t, size, score };
          }
        }
      }

      if (best && bestScore >= 55) {
        this.log('info', 'Capital rotation: deploying freed capital', {
          market: best.trade.market, size: best.size, score: best.score
        });
        if (this.audit) this.audit.record('PROFIT_RECYCLED', {
          market: best.trade.market, size: best.size, score: best.score, availableCapital
        });
        await this.evaluate(best.trade);
      }
    } catch (e) {
      this.log('warn', 'findBestOpenOpportunity failed', { error: e.message });
    }
  }

  async _quickScore(walletAddr, trade) {
    if (!this.walletTracker) return 50;
    const stats = this.walletTracker.getWalletStats(walletAddr);
    const best = this._bestWindow(stats);
    if (!best || (best.wins + best.losses) < 5) return 50;
    const wr = this._wilsonLower(best.wins, best.wins + best.losses);
    return Math.round(50 + (wr - 0.5) * 60);
  }

  getStatus() {
    return {
      enabled: this.enabled,
      recentSignals: this.recentSignals.size,
      config: this.getConfig(),
      learningState: {
        walletAdjustments: Object.keys(this._walletConfidenceAdj || {}).length,
        priceZoneResults: this._priceZoneResults || null
      }
    };
  }

  /**
   * Z1: Whale confirmation check — query the wallet tracker for activity in this
   * market during the copy-delay window.
   *
   * @param {string} walletAddress  - Whale wallet being copied
   * @param {string} market         - Market title to match against
   * @param {number} windowMs       - Look-back window in ms (typically jitter + 1000)
   * @returns {{ addedMore: boolean, reversedPosition: boolean }}
   */
  async _checkWhaleActivityDuringDelay(walletAddress, market, windowMs) {
    const empty = { addedMore: false, reversedPosition: false };
    if (!walletAddress || !market) return empty;

    // Primary source: walletTracker (persisted trade history, keyed by address)
    const tracker = this.walletTracker;
    if (!tracker) return empty;

    const trades = tracker.walletTrades?.get(walletAddress);
    if (!Array.isArray(trades) || trades.length === 0) return empty;

    const windowStart = Date.now() - windowMs;
    const inWindow = trades.filter(t => {
      if (t.market !== market) return false;
      const ts = new Date(t.timestamp).getTime();
      return ts > windowStart;
    });

    if (inWindow.length === 0) return empty;

    const reversedPosition = inWindow.some(t => t.action === 'SELL');
    const addedMore = inWindow.some(t => t.action === 'BUY');

    return { addedMore, reversedPosition };
  }

  log(level, message, data) {
    console.log(`[Signal] [${level}] ${message}`, data || '');
    if (this.db) { try { this.db.logEvent(level, '[Signal] ' + message, data); } catch (e) {} }
  }
}

module.exports = SignalEngine;
module.exports.calcTakerFee = calcTakerFee;
