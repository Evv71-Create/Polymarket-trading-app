/**
 * Up/Down Strategy — trades Polymarket 5-minute "Bitcoin/Ethereum/Solana Up or Down" markets.
 *
 * Core insight: 3-4 minutes into a 5-minute candle, the direction is usually locked in.
 * We compare real-time Binance spot price to the candle open price, and bet the direction
 * when the move is large enough that Chainlink/Binance discrepancy won't flip the outcome.
 *
 * Resolution rules (Chainlink):
 *   - If BTC price at END >= price at START → "Up" wins
 *   - If BTC price at END < price at START  → "Down" wins
 *   - Ties go to Up
 *
 * Fee: Dynamic taker ~1.56% at p=0.50 (Feb 2026+). Need >50.8% WR at mid-price.
 * Tick size: $0.01. Prices range $0.01-$0.99.
 *
 * Supports: Bitcoin (BTCUSDT), Ethereum (ETHUSDT), Solana (SOLUSDT)
 *
 * All trades go through risk.checkTrade(). Dry-run mode is respected throughout.
 * Never modifies signal.js, risk.js, exit-engine.js, or wallet-tracker.js.
 */
'use strict';

/** Polymarket dynamic crypto taker fee per share (Feb 2026+) */
function _cryptoTakerFee(price) {
  const p = Math.max(0.01, Math.min(0.99, price));
  return 0.25 * p * p * (1 - p) * (1 - p);
}

const axios = require('axios');

const GAMMA = 'https://gamma-api.polymarket.com';

const BINANCE_TICKER = 'https://api.binance.com/api/v3/ticker/price';
const BINANCE_KLINES = 'https://api.binance.com/api/v3/klines';

// Map title keywords to Binance symbol
const ASSET_MAP = {
  bitcoin:  'BTCUSDT',
  ethereum: 'ETHUSDT',
  solana:   'SOLUSDT',
  bnb:      'BNBUSDT',
  xrp:      'XRPUSDT',
  dogecoin: 'DOGEUSDT',
  doge:     'DOGEUSDT',
};

const DEFAULTS = {
  updown_enabled:         true,
  updown_minMagnitudePct: 0.08,   // minimum price move % — higher = more confident directional signal
  updown_maxEntryPrice:   0.60,   // skip if market already priced >60% (stay in profitable zone)
  updown_scanIntervalMs:  15000,  // 15 seconds
  updown_maxSize:         10,     // $ max per trade (conservative until WR proven)
  updown_minSize:         3,      // $ min per trade (matches maxLossPerTrade)
  updown_minMinutesLeft:  1,      // earliest entry (1 min before close — enough for order fill)
  updown_maxMinutesLeft:  14,     // latest entry (14 min before close — covers 5min and 15min candles)
  // Per-duration window filter (Option B)
  updown_enabledWindows:          [5, 15],        // allowed candle durations in minutes; exclude 240 by default (too few markets)
  updown_maxMinutesLeftByWindow:  { 5: 4, 15: 6, 240: 30 },  // per-window max entry time (late-candle lock-in)
  updown_sizingMultiplierByWindow: { 5: 1.3, 15: 0.8, 240: 0.5 }  // per-window sizing multiplier; 15-min and 240-min are unproven
};

class UpDownStrategy {
  constructor({ db, risk, clob, audit, log, ws, rateLimiter, telegram, notifier }) {
    this.db    = db;
    this.risk  = risk;
    this.clob  = clob;
    this.audit = audit;
    this.ws    = ws || null;  // Polymarket WebSocket for cached market prices
    this.rateLimiter = rateLimiter || null;
    this.telegram = telegram || null;
    this.notifier = notifier || null;

    // Allow injecting a custom logger, otherwise use console
    this._customLog = log || null;

    // Runtime state
    this._interval     = null;
    this._tradedIds    = new Set();   // conditionIds already traded this session (dedup)
    this._tradedIdsTTL = new Map();   // conditionId -> expiry timestamp for auto-cleanup
    // In-flight entry reservation counter. Increments before `clob.placeOrder` and
    // decrements in finally. Prevents a single scan cycle (100+ markets evaluated
    // in parallel-ish sequence) from racing past `updown_maxConcurrentPositions`
    // while previous placeOrder calls are still awaiting a response. In-memory only.
    this._inflightEntries = 0;

    // Stats
    this._stats = {
      scans:         0,
      marketsFound:  0,
      tradesEntered: 0,
      tradesFailed:  0,
      skippedTiming: 0,
      skippedMag:    0,
      skippedPrice:  0,
      skippedDedup:  0,
      skippedWindowDuration: 0,  // markets skipped because their window duration is not in enabledWindows
      lastScan:      null,
      lastTrade:     null,
      pnlEstimate:   0,
      // Per-duration performance tracking (Option B). Keyed by window duration in minutes.
      // Each bucket: { trades, wins, losses, pnl, skipped }
      byDuration:    {},
      // M4: REST fallback tracking. Node 22+ has built-in WebSocket so this
      // path should basically never activate. If these counters are non-zero in
      // production, the WS feed isn't working and spot prices are coming from
      // Binance REST polling — which is much slower and rate-limited.
      restFallbackActive:   false,  // true if we're polling REST instead of WS
      restFallbackRequests: 0,       // total REST spot fetches attempted
      restFallbackFailures: 0        // REST spot fetches that returned null
    };

    // Win rate tracking for auto-disable
    const savedWR = this.db?.getSetting('updown_winRateStats', null);
    this._wrStats = savedWR || { wins: 0, losses: 0, totalPnL: 0 };
    this._paused = false;

    // Per-asset adaptive learning stats
    this._assetStats = this.db?.getSetting('updown_assetStats', null) || this._emptyAssetStats();
    // Per-asset auto-disable state
    this._disabledAssets = this.db?.getSetting('updown_autoDisabledAssets', {}) || {};

    // H1: live-trade entry metadata map (tradeId → { magnitudeBucket, openedAt }).
    // risk.openPosition strips unknown fields, so we can't stash updown-specific
    // context on the position itself. We keep a side-map that survives restarts so
    // handleLiveExit() can look up the entry bucket when exit-engine fires onExit.
    // asset and direction are derivable from pos.market/pos.side and don't need storage.
    const savedEntryMeta = this.db?.getSetting('updown_liveEntryMetadata', {}) || {};
    this._liveEntryMetadata = new Map(Object.entries(savedEntryMeta));

    // Binance rate limiting — minimum 200ms between calls
    this._lastBinanceCall = 0;

    // Gamma rate limiting — minimum 2s between calls
    this._lastGammaCall = 0;

    // Real-time Binance WebSocket price feed
    this._binanceWs = null;
    this._spotPrices = {};  // { BTCUSDT: 67155.50, ETHUSDT: 3200.10, ... }
    this._binanceReconnectTimer = null;

    // Known active markets cache (refreshed by discovery loop)
    this._activeMarkets = [];
    this._marketsRefreshedAt = 0;

    // Recent events ring buffer for the UI Signal Activity Feed.
    // Each entry matches the shape used by signal.js getRecentRejections so
    // server.js /api/signal/activity can merge them without UI changes.
    this._recentEvents = [];
    this._MAX_RECENT_EVENTS = 200;

    this._log('info', 'UpDownStrategy initialised');
  }

  // ── Recent events feed ────────────────────────────────────────────────

  _recordEvent(ev) {
    // Push then trim to max length. Cheap O(1) amortized.
    this._recentEvents.push({
      timestamp: Date.now(),
      walletAddress: 'updown_strategy',
      walletName: 'UpDown Strategy',
      ...ev
    });
    if (this._recentEvents.length > this._MAX_RECENT_EVENTS) {
      this._recentEvents.shift();
    }
  }

  getRecentEvents(limit = 100) {
    const n = Math.min(Math.max(1, limit), this._MAX_RECENT_EVENTS);
    return this._recentEvents.slice(-n).reverse();
  }

  // ── Configuration ─────────────────────────────────────────────────────

  getConfig() {
    const cfg = {};
    for (const [key, def] of Object.entries(DEFAULTS)) {
      cfg[key] = this.db ? this.db.getSetting(key, def) : def;
    }
    return cfg;
  }

  // ── Lifecycle ──────────────────────────────────────────────────────────

  start() {
    const cfg = this.getConfig();
    if (!cfg.updown_enabled) {
      this._log('info', 'UpDownStrategy not starting — updown_enabled is false');
      return;
    }

    if (this._interval) {
      this._log('warn', 'UpDownStrategy already running — call stop() first');
      return;
    }

    // 0. Bootstrap per-asset learning from historical trades
    this.bootstrapLearning();

    // 1. Connect Binance WebSocket for real-time spot prices
    this._connectBinanceWs();

    // 2. Market discovery loop — polls wallet trades every 15s for faster detection
    this._discoveryInterval = setInterval(() => this._safeRun('discovery', () => this._refreshMarkets()), 15000);
    this._safeRun('discovery', () => this._refreshMarkets());

    // 3. Fast evaluation loop (every 3s — checks timing + spot vs open on known markets)
    this._interval = setInterval(() => this._safeRun('evaluate', () => this._evaluateMarkets()), 3000);

    // 4. Resolution checker — resolves pending dry-run trades when candle closes
    // Restore from DB to survive restarts
    this._pendingResolutions = this.db?.getSetting('updown_pendingResolutions', []) || [];
    if (this._pendingResolutions.length > 0) {
      // Reconstitute Date objects from serialized data
      this._pendingResolutions.forEach(r => {
        if (r.window) {
          r.window.startTime = new Date(r.window.startTime);
          r.window.endTime = new Date(r.window.endTime);
        }
      });
      this._log('info', `Restored ${this._pendingResolutions.length} pending trade resolutions from DB`);
    }
    this._resolutionInterval = setInterval(() => this._safeRun('resolve', () => this._resolvePendingTrades()), 10000);

    // Dedup cleanup every 10 minutes
    this._cleanupInterval = setInterval(() => this._cleanupTradedIds(), 10 * 60 * 1000);

    // 5. Startup catchup — resolve any unresolved UpDown trades from DB via Binance
    setTimeout(() => this._resolveStaleDbTrades(), 30000); // 30s after startup

    this._log('info', 'UpDownStrategy started — WS spot feed + 3s eval loop + 30s discovery');
  }

  stop() {
    if (this._interval) { clearInterval(this._interval); this._interval = null; }
    if (this._discoveryInterval) { clearInterval(this._discoveryInterval); this._discoveryInterval = null; }
    if (this._resolutionInterval) { clearInterval(this._resolutionInterval); this._resolutionInterval = null; }
    if (this._cleanupInterval) { clearInterval(this._cleanupInterval); this._cleanupInterval = null; }
    if (this._binanceWs) {
      try { this._binanceWs.close(1000); } catch (_) {}
      this._binanceWs = null;
    }
    if (this._binanceReconnectTimer) { clearTimeout(this._binanceReconnectTimer); this._binanceReconnectTimer = null; }
    // Persist win rate stats
    if (this.db) this.db.setSetting('updown_winRateStats', this._wrStats);
    this._log('info', 'UpDownStrategy stopped');
  }

  // Record trade result for WR tracking (called externally by exit-engine or risk engine)
  // Optional: asset (bitcoin/ethereum/solana), direction (Up/Down), magnitudeBucket (small/medium/large)
  // Optional: windowMins (5/15/240) for per-duration performance tracking (Option B)
  recordTradeResult(pnl, asset, direction, magnitudeBucket, windowMins) {
    if (pnl > 0) this._wrStats.wins++;
    else this._wrStats.losses++;
    this._wrStats.totalPnL += pnl;
    if (this.db) this.db.setSetting('updown_winRateStats', this._wrStats);
    const total = this._wrStats.wins + this._wrStats.losses;
    const wr = total > 0 ? (this._wrStats.wins / total * 100).toFixed(1) : '0.0';
    this._log('info', `UpDown result: ${pnl > 0 ? 'WIN' : 'LOSS'} $${pnl.toFixed(2)} | WR: ${wr}% (${total} trades, PnL: $${this._wrStats.totalPnL.toFixed(2)})`);

    // Feed into per-asset adaptive learning
    if (asset) {
      this._recordAssetResult(pnl, asset, direction, magnitudeBucket);
    }

    // Per-duration stats (Option B)
    if (windowMins != null) {
      if (!this._stats.byDuration[windowMins]) {
        this._stats.byDuration[windowMins] = { trades: 0, wins: 0, losses: 0, pnl: 0, skipped: 0 };
      }
      const bucket = this._stats.byDuration[windowMins];
      bucket.trades++;
      if (pnl > 0) bucket.wins++; else bucket.losses++;
      bucket.pnl = +(bucket.pnl + pnl).toFixed(2);
    }
  }

  // ── Per-asset adaptive learning ─────────────────────────────────────

  _emptyAssetStats() {
    const empty = () => ({
      wins: 0, losses: 0, totalPnL: 0,
      byDirection: { Up: { w: 0, l: 0 }, Down: { w: 0, l: 0 } },
      byMagnitude: { small: { w: 0, l: 0 }, medium: { w: 0, l: 0 }, large: { w: 0, l: 0 } },
      recentResults: []  // rolling last-50 results for trend detection (true=win, false=loss)
    });
    return { bitcoin: empty(), ethereum: empty(), solana: empty() };
  }

  /**
   * Record a resolved trade into per-asset stats.
   * @param {number} pnl - trade P&L
   * @param {string} asset - asset key (bitcoin/ethereum/solana)
   * @param {string} direction - Up or Down
   * @param {string} magnitudeBucket - small/medium/large (or null to skip)
   */
  _recordAssetResult(pnl, asset, direction, magnitudeBucket) {
    if (!asset || !this._assetStats[asset]) return;
    const s = this._assetStats[asset];
    const won = pnl > 0;

    // Global per-asset
    if (won) s.wins++; else s.losses++;
    s.totalPnL += pnl;

    // By direction
    if (direction === 'Up' || direction === 'Down') {
      if (won) s.byDirection[direction].w++; else s.byDirection[direction].l++;
    }

    // By magnitude bucket
    if (magnitudeBucket && s.byMagnitude[magnitudeBucket]) {
      if (won) s.byMagnitude[magnitudeBucket].w++; else s.byMagnitude[magnitudeBucket].l++;
    }

    // Rolling last-50 for trend detection
    s.recentResults.push(won);
    if (s.recentResults.length > 50) s.recentResults.shift();

    // Persist
    if (this.db) this.db.setSetting('updown_assetStats', this._assetStats);

    // Check per-asset auto-disable / re-enable
    this._checkAssetAutoDisable(asset);
  }

  /**
   * Get the magnitude bucket for a given pctMove.
   * small = <0.10%, medium = 0.10-0.20%, large = >0.20%
   */
  _getMagnitudeBucket(absPctMove) {
    if (absPctMove >= 0.20) return 'large';
    if (absPctMove >= 0.10) return 'medium';
    return 'small';
  }

  /**
   * Check if an asset should be auto-disabled or re-enabled based on performance.
   * Disable: 30+ trades and WR < 52%
   * Re-enable: rolling last-50 WR >= 55% (hysteresis)
   */
  _checkAssetAutoDisable(asset) {
    const s = this._assetStats[asset];
    if (!s) return;
    const total = s.wins + s.losses;
    const wr = total > 0 ? s.wins / total : 0;

    if (this._disabledAssets[asset]) {
      // Check re-enable: rolling last-50 WR >= 55%
      const recent = s.recentResults;
      if (recent.length >= 20) {
        const recentWins = recent.filter(Boolean).length;
        const recentWR = recentWins / recent.length;
        if (recentWR >= 0.55) {
          delete this._disabledAssets[asset];
          if (this.db) this.db.setSetting('updown_autoDisabledAssets', this._disabledAssets);
          this._log('info', `[Adaptive] Re-enabled ${asset}: rolling WR ${(recentWR * 100).toFixed(1)}% >= 55% (${recent.length} recent trades)`);
        }
      }
    } else {
      // Check disable: 30+ trades and WR < 52%
      if (total >= 30 && wr < 0.52) {
        this._disabledAssets[asset] = {
          disabledAt: new Date().toISOString(),
          reason: `WR ${(wr * 100).toFixed(1)}% < 52% after ${total} trades`,
          wrAtDisable: wr,
          totalTrades: total
        };
        if (this.db) this.db.setSetting('updown_autoDisabledAssets', this._disabledAssets);
        this._log('warn', `[Adaptive] Disabled ${asset}: WR ${(wr * 100).toFixed(1)}% < 52% after ${total} trades (PnL: $${s.totalPnL.toFixed(2)})`);
        try { this.telegram?.send?.(`🚫 UpDown auto-disabled ${asset}: WR ${(wr * 100).toFixed(1)}% < 52% after ${total} trades. PnL: $${s.totalPnL.toFixed(2)}`); } catch (_) {}
      }
    }
  }

  /**
   * Get per-asset win rate. Returns null if insufficient data (<20 trades).
   */
  _getAssetWR(asset) {
    const s = this._assetStats[asset];
    if (!s) return null;
    const total = s.wins + s.losses;
    if (total < 20) return null;
    return (s.wins / total) * 100;
  }

  /**
   * Get per-asset+direction win rate. Returns null if insufficient data (<20 trades).
   */
  _getDirectionWR(asset, direction) {
    const s = this._assetStats[asset];
    if (!s || !s.byDirection[direction]) return null;
    const d = s.byDirection[direction];
    const total = d.w + d.l;
    if (total < 20) return null;
    return (d.w / total) * 100;
  }

  /**
   * Get per-asset+magnitude WR. Returns null if insufficient data (<20 trades).
   */
  _getMagnitudeWR(asset, bucket) {
    const s = this._assetStats[asset];
    if (!s || !s.byMagnitude[bucket]) return null;
    const b = s.byMagnitude[bucket];
    const total = b.w + b.l;
    if (total < 20) return null;
    return (b.w / total) * 100;
  }

  /**
   * Bootstrap per-asset stats from ALL historical UpDown trades in the DB.
   * Called once at startup. Reads the raw DB file to get trades beyond the
   * getTradeHistory(500) cap.
   */
  bootstrapLearning() {
    // Skip if already have meaningful data (>50 total trades across all assets)
    const existing = Object.values(this._assetStats).reduce((sum, s) => sum + s.wins + s.losses, 0);
    if (existing >= 50) {
      this._log('info', `[Adaptive] Bootstrap skipped — already have ${existing} per-asset records`);
      return;
    }

    let allTrades = [];
    try {
      const fs = require('fs');
      const path = require('path');
      const dbPath = path.join(__dirname, 'data', 'polymarket.json');
      if (!fs.existsSync(dbPath)) {
        this._log('info', '[Adaptive] Bootstrap skipped — DB file not found');
        return;
      }
      const raw = JSON.parse(fs.readFileSync(dbPath, 'utf8'));
      allTrades = raw.trades || [];
    } catch (e) {
      this._log('warn', '[Adaptive] Bootstrap failed to read DB: ' + e.message);
      return;
    }

    const updownTrades = allTrades.filter(t =>
      t.copied_from === 'updown_strategy' && t.pnl != null
    );

    if (updownTrades.length === 0) {
      this._log('info', '[Adaptive] Bootstrap: no resolved UpDown trades found in DB');
      return;
    }

    // Reset stats before bootstrap
    this._assetStats = this._emptyAssetStats();

    let bootstrapped = 0;
    for (const t of updownTrades) {
      const market = (t.market || '').toLowerCase();
      let asset = null;
      if (market.includes('bitcoin') || market.includes('btc')) asset = 'bitcoin';
      else if (market.includes('ethereum') || market.includes('eth')) asset = 'ethereum';
      else if (market.includes('solana') || market.includes('sol')) asset = 'solana';
      if (!asset || !this._assetStats[asset]) continue;

      // Direction from side: YES=Up, NO=Down
      const direction = t.side === 'YES' ? 'Up' : (t.side === 'NO' ? 'Down' : null);
      if (!direction) continue;

      const pnl = t.pnl;
      const won = pnl > 0;
      const s = this._assetStats[asset];

      // Global per-asset
      if (won) s.wins++; else s.losses++;
      s.totalPnL += pnl;

      // By direction
      if (s.byDirection[direction]) {
        if (won) s.byDirection[direction].w++; else s.byDirection[direction].l++;
      }

      // Skip magnitude for bootstrap — we don't have entry pctMove for historical trades
      // Magnitude stats will build up organically from new trades going forward

      // Rolling last-50 (use only the most recent trades)
      s.recentResults.push(won);

      bootstrapped++;
    }

    // Trim rolling windows to last 50
    for (const asset of Object.keys(this._assetStats)) {
      const s = this._assetStats[asset];
      if (s.recentResults.length > 50) {
        s.recentResults = s.recentResults.slice(-50);
      }
    }

    // Persist bootstrapped stats
    if (this.db) this.db.setSetting('updown_assetStats', this._assetStats);

    // Run auto-disable checks for each asset
    for (const asset of Object.keys(this._assetStats)) {
      this._checkAssetAutoDisable(asset);
    }

    // Log summary
    const summary = Object.entries(this._assetStats).map(([asset, s]) => {
      const total = s.wins + s.losses;
      const wr = total > 0 ? (s.wins / total * 100).toFixed(1) : '0.0';
      return `${asset}: ${wr}% WR (${total} trades, $${s.totalPnL.toFixed(2)})`;
    }).join(', ');
    this._log('info', `[Adaptive] Bootstrapped from ${bootstrapped} historical trades: ${summary}`);
  }

  // ── Resolution checker — resolves dry-run trades after candle close ──

  async _resolvePendingTrades() {
    if (!this._pendingResolutions || !this._pendingResolutions.length) return;

    const now = Date.now();
    const resolved = [];

    for (let i = 0; i < this._pendingResolutions.length; i++) {
      const r = this._pendingResolutions[i];
      if (!r.window) { resolved.push(i); continue; }

      const endTs = r.window.endTime.getTime();
      // Wait 10s after candle close for final price to settle
      if (now < endTs + 10000) continue;

      // Candle has closed — resolve via Binance spot
      try {
        const closePrice = await this._getSpotPrice(r.symbol);
        if (!closePrice) continue;

        const won = r.direction === 'Up' ? closePrice > r.openPrice : closePrice < r.openPrice;
        // Dynamic crypto fee: 0.25 * p² * (1-p)², ~1.56% at p=0.50
        const feePerShare = _cryptoTakerFee(r.price);
        const pnl = won ? ((1 - r.price) - feePerShare) * r.finalSize : -(r.price * r.finalSize);

        // Extract asset key for adaptive learning (from stored field or symbol reverse-lookup)
        const resolveAsset = r.asset || this._symbolToAsset(r.symbol);
        this.recordTradeResult(pnl, resolveAsset, r.direction, r.magnitudeBucket || null, r.windowMins || null);
        this._log('info', `[RESOLVED] ${r.market.slice(0, 50)} → ${won ? 'WIN' : 'LOSS'} $${pnl.toFixed(2)} (close: ${closePrice.toFixed(2)} vs open: ${r.openPrice.toFixed(2)}, asset: ${resolveAsset || 'unknown'})`);

        // Update DB trade record
        if (this.db?.updateTrade && r.dbTradeId) {
          this.db.updateTrade(r.dbTradeId, {
            status: 'closed',
            pnl: +pnl.toFixed(2),
            exit_reason: won ? 'resolved_win' : 'resolved_loss',
            closed_at: new Date().toISOString()
          });
        }

        // Notify risk engine to close the position (prevents zombie in openPositions)
        if (this.risk?.recordResult && r.tradeId) {
          try { this.risk.recordResult(r.tradeId, pnl); } catch (e) { /* swallow */ }
        }

        resolved.push(i);
      } catch (e) {
        const ageMs = now - r.enteredAt;

        // After 30 min of Binance failures, try Polymarket gamma-api fallback
        if (ageMs > 30 * 60 * 1000) {
          const gammaResult = await this._tryGammaResolution(r);
          if (gammaResult) {
            // Polymarket fallback succeeded — record with real PnL
            const resolveAsset = r.asset || this._symbolToAsset(r.symbol);
            this.recordTradeResult(gammaResult.pnl, resolveAsset, r.direction, r.magnitudeBucket || null, r.windowMins || null);
            this._log('info', `[GAMMA-FALLBACK] ${r.market.slice(0, 50)} → ${gammaResult.won ? 'WIN' : 'LOSS'} $${gammaResult.pnl.toFixed(2)}`);

            if (this.db?.updateTrade && r.dbTradeId) {
              this.db.updateTrade(r.dbTradeId, {
                status: 'closed',
                pnl: +gammaResult.pnl.toFixed(2),
                exit_reason: gammaResult.won ? 'gamma_fallback_win' : 'gamma_fallback_loss',
                closed_at: new Date().toISOString()
              });
            }
            if (this.risk?.recordResult && r.tradeId) {
              try { this.risk.recordResult(r.tradeId, gammaResult.pnl); } catch (e) { /* swallow */ }
            }
            resolved.push(i);
            continue;  // skip the timeout check below
          }
        }

        // After 2 hours with no resolution from Binance OR Polymarket, give up at $0
        // Do NOT call recordTradeResult — synthetic $0 should not pollute learning data
        if (ageMs > 2 * 60 * 60 * 1000) {
          this._log('warn', `[TIMEOUT] ${r.market.slice(0, 50)} — no resolution after 2h, closing at $0`);
          if (this.db?.updateTrade && r.dbTradeId) {
            this.db.updateTrade(r.dbTradeId, { status: 'closed', pnl: 0, exit_reason: 'resolution_timeout', closed_at: new Date().toISOString() });
          }
          if (this.risk?.recordResult && r.tradeId) {
            try { this.risk.recordResult(r.tradeId, 0); } catch (e) { /* swallow */ }
          }
          resolved.push(i);
        }
        // Otherwise: keep retrying on next cycle (don't add to resolved)
      }
    }

    // Remove resolved (iterate backwards to keep indices valid)
    if (resolved.length > 0) {
      for (let i = resolved.length - 1; i >= 0; i--) {
        this._pendingResolutions.splice(resolved[i], 1);
      }
      this._persistPendingResolutions();
    }
  }

  // Polymarket gamma-api fallback for resolution when Binance is unavailable.
  // Returns { pnl, won } if the market is closed/resolved, or null otherwise.
  async _tryGammaResolution(r) {
    try {
      const searchTitle = (r.market || '').replace(/[^a-zA-Z0-9 ]/g, ' ').slice(0, 80).trim();
      const keywords = searchTitle.split(/\s+/).filter(w => w.length > 3).slice(0, 5).join(' ');
      if (!keywords) return null;

      const resp = await axios.get(`${GAMMA}/markets`, {
        params: { limit: 20, closed: true, title: keywords },
        timeout: 8000
      });
      const markets = resp.data || [];
      if (!markets.length) return null;

      const titleLower = (r.market || '').toLowerCase().trim();

      // Exact match first, then fuzzy substring match
      let match = markets.find(m => (m.question || '').toLowerCase().trim() === titleLower);
      if (!match) {
        match = markets.find(m => {
          const q = (m.question || '').toLowerCase().trim();
          return (q.length > 20 && titleLower.includes(q)) ||
                 (titleLower.length > 20 && q.includes(titleLower));
        });
      }
      if (!match) return null;

      // Market must actually be closed/resolved
      const isClosed = match.closed === true || match.resolved === true;
      if (!isClosed) return null;

      // Determine winner: prefer tokens[0].winner, fall back to outcomePrices
      let yesWon = null;
      if (Array.isArray(match.tokens) && match.tokens.length >= 1 && typeof match.tokens[0].winner === 'boolean') {
        yesWon = match.tokens[0].winner === true;
      } else if (match.outcomePrices) {
        try {
          const prices = typeof match.outcomePrices === 'string'
            ? JSON.parse(match.outcomePrices)
            : match.outcomePrices;
          if (Array.isArray(prices) && prices.length >= 1) {
            const p0 = parseFloat(prices[0]);
            if (!isNaN(p0)) yesWon = p0 >= 0.5;
          }
        } catch (_) { /* swallow */ }
      }
      if (yesWon === null) return null;

      // Map YES/NO winner to our Up/Down direction
      const won = r.direction === 'Up' ? yesWon : !yesWon;
      const feePerShare = _cryptoTakerFee(r.price);
      const pnl = won ? ((1 - r.price) - feePerShare) * r.finalSize : -(r.price * r.finalSize);
      return { pnl, won };
    } catch (_) {
      return null;
    }
  }

  // Startup catchup: find any UpDown trades stuck with null PnL in DB and resolve via Binance
  async _resolveStaleDbTrades() {
    if (!this.db) return;
    const trades = this.db.getTradeHistory?.(200) || [];
    // H3: Only resolve DRY-RUN stale trades via Binance here. Live trades must
    // resolve via Polymarket's own Chainlink payout (tracked by exit-engine
    // checkResolutions via gamma-api). Using Binance for live pnl causes drift
    // between recorded pnl and actual wallet balance over time — edge cases
    // where the Chainlink resolution differs from the Binance 5m kline
    // accumulate and break bankroll-percentage risk caps. Exit-engine has its
    // own stale-resolution fallback for stuck live trades (the 'stale_unresolved'
    // path), so it's safe for us to leave live 'open' trades alone.
    const stale = trades.filter(t =>
      (t.copied_from || '').includes('updown') &&
      t.pnl == null &&
      t.status === 'dry_run' &&
      t.dry_run !== false  // defensive: require explicit dry-run flag
    );
    if (!stale.length) return;
    this._log('info', `Catchup: resolving ${stale.length} unresolved dry-run UpDown trades from DB`);

    const ASSET_MAP_LOCAL = { bitcoin: 'BTCUSDT', ethereum: 'ETHUSDT', solana: 'SOLUSDT', bnb: 'BNBUSDT', dogecoin: 'DOGEUSDT', doge: 'DOGEUSDT', xrp: 'XRPUSDT' };
    let resolved = 0;
    for (const t of stale) {
      const w = this._parseMarketWindow(t.market || '');
      if (!w || w.endTime.getTime() > Date.now()) continue; // candle not ended yet
      const asset = Object.keys(ASSET_MAP_LOCAL).find(k => (t.market || '').toLowerCase().includes(k));
      if (!asset) {
        // Synthetic $0 — do NOT call recordTradeResult (would bias asset stats with unknown outcome)
        this.db.updateTrade(t.id, { status: 'closed', pnl: 0, exit_reason: 'catchup_no_asset' });
        if (this.risk?.recordResult) {
          try { const rp = (this.risk.state?.openPositions || []).find(p => p.tradeId === t.id); if (rp) this.risk.recordResult(rp.id, 0); } catch (e) { /* swallow */ }
        }
        resolved++; continue;
      }
      try {
        const axios = require('axios');
        const r = await axios.get('https://api.binance.com/api/v3/klines', {
          params: { symbol: ASSET_MAP_LOCAL[asset], interval: '5m', startTime: w.startTime.getTime(), endTime: w.endTime.getTime(), limit: 1 },
          timeout: 5000
        });
        const kline = r.data?.[0];
        if (!kline) {
          // Synthetic $0 — do NOT call recordTradeResult (would bias asset stats with unknown outcome)
          this.db.updateTrade(t.id, { status: 'closed', pnl: 0, exit_reason: 'catchup_no_kline' });
          if (this.risk?.recordResult) {
            try { const rp = (this.risk.state?.openPositions || []).find(p => p.tradeId === t.id); if (rp) this.risk.recordResult(rp.id, 0); } catch (e) { /* swallow */ }
          }
          resolved++; continue;
        }
        const open = parseFloat(kline[1]), close = parseFloat(kline[4]);
        const dir = t.side === 'YES' ? 'Up' : 'Down';
        const won = dir === 'Up' ? close > open : close < open;
        const feePerShare = _cryptoTakerFee(t.price);
        const pnl = won ? ((1 - t.price) - feePerShare) * t.size : -(t.price * t.size);
        this.db.updateTrade(t.id, { status: 'closed', pnl: +pnl.toFixed(2), exit_reason: won ? 'catchup_win' : 'catchup_loss', closed_at: new Date().toISOString() });
        this.recordTradeResult(pnl, asset, dir, null, null); // windowMins not available in catchup path

        // Notify risk engine to close the position (prevents zombie in openPositions)
        // Risk position uses id=updown_XXXXX_timestamp, tradeId=dbIntId — find by tradeId match
        if (this.risk?.recordResult) {
          try {
            const riskPos = (this.risk.state?.openPositions || []).find(p => p.tradeId === t.id);
            if (riskPos) this.risk.recordResult(riskPos.id, pnl);
          } catch (e) { /* swallow */ }
        }

        resolved++;
        await new Promise(r => setTimeout(r, 150));
      } catch (_) {
        // Synthetic $0 — do NOT call recordTradeResult (would bias asset stats with unknown outcome)
        this.db.updateTrade(t.id, { status: 'closed', pnl: 0, exit_reason: 'catchup_error' });

        // Notify risk engine to close the position even on error (prevents zombie)
        if (this.risk?.recordResult) {
          try {
            const riskPos = (this.risk.state?.openPositions || []).find(p => p.tradeId === t.id);
            if (riskPos) this.risk.recordResult(riskPos.id, 0);
          } catch (e) { /* swallow */ }
        }

        resolved++;
      }
    }
    if (resolved > 0) this._log('info', `Catchup: resolved ${resolved}/${stale.length} stale UpDown trades`);
  }

  _persistPendingResolutions() {
    if (this.db) {
      try { this.db.setSetting('updown_pendingResolutions', this._pendingResolutions); } catch (_) {}
    }
  }

  // ── H1: Live-trade entry metadata (for asset/direction/magnitude learning) ──

  _persistLiveEntryMetadata() {
    if (!this.db) return;
    try {
      // Serialize Map to plain object for JSON storage
      const obj = {};
      for (const [k, v] of this._liveEntryMetadata) obj[k] = v;
      this.db.setSetting('updown_liveEntryMetadata', obj);
    } catch (_) {}
  }

  /**
   * H1: Called by server.js exit-engine onExit hook for live updown trades.
   * Derives asset and direction from the resolved position, looks up the stored
   * magnitudeBucket from _liveEntryMetadata, and feeds everything into
   * recordTradeResult so per-asset adaptive learning works in live mode.
   *
   * Without this, server.js used to call recordTradeResult(pnl) with no context,
   * which early-returned from _recordAssetResult and silently disabled:
   *   - per-asset auto-disable (protective circuit breaker)
   *   - per-asset+direction WR threshold (adaptive magnitude multiplier)
   *   - per-asset+magnitude WR (small-magnitude skip on bad assets)
   *
   * @param {object} pos - position record from risk.openPosition (has id, market, side)
   * @param {number} pnl - realized pnl for this trade
   */
  handleLiveExit(pos, pnl) {
    if (!pos || typeof pnl !== 'number' || !isFinite(pnl)) {
      this._log('warn', 'handleLiveExit called with invalid pos/pnl');
      return;
    }

    // Derive asset from market title (same logic as _evaluateSingleMarket:879)
    let asset = null;
    const titleLower = (pos.market || '').toLowerCase();
    for (const key of Object.keys(ASSET_MAP)) {
      if (titleLower.includes(key)) { asset = key; break; }
    }
    // Handle abbreviations as a fallback
    if (!asset) {
      if (titleLower.includes('btc')) asset = 'bitcoin';
      else if (titleLower.includes('eth')) asset = 'ethereum';
      else if (titleLower.includes('sol')) asset = 'solana';
    }

    // Derive direction from position side. Up-or-Down uses YES=Up, NO=Down.
    const direction = pos.side === 'YES' ? 'Up' : (pos.side === 'NO' ? 'Down' : null);

    // Look up the stored magnitude bucket and window duration by the updown internal tradeId (pos.id)
    const meta = this._liveEntryMetadata.get(pos.id);
    const magnitudeBucket = meta?.magnitudeBucket || null;
    const windowMins = meta?.windowMins || null;  // per-duration tracking (Option B)

    // Record — recordTradeResult handles the null cases internally
    this.recordTradeResult(pnl, asset, direction, magnitudeBucket, windowMins);

    // Clean up the side-map entry so it doesn't grow unbounded
    if (this._liveEntryMetadata.has(pos.id)) {
      this._liveEntryMetadata.delete(pos.id);
      this._persistLiveEntryMetadata();
    }
  }

  /**
   * GC sweep for _liveEntryMetadata. Entries older than maxAgeMs (default 24h)
   * are assumed abandoned (e.g. position lost without triggering onExit due to
   * some edge-case crash) and removed so the map can't grow indefinitely.
   * Called from the existing _cleanupTradedIds interval tick.
   */
  _gcLiveEntryMetadata(maxAgeMs = 24 * 60 * 60 * 1000) {
    const now = Date.now();
    let pruned = 0;
    for (const [tradeId, meta] of this._liveEntryMetadata) {
      if (!meta?.openedAt || (now - meta.openedAt) > maxAgeMs) {
        this._liveEntryMetadata.delete(tradeId);
        pruned++;
      }
    }
    if (pruned > 0) {
      this._persistLiveEntryMetadata();
      this._log('debug', `GC: pruned ${pruned} stale live entry metadata records`);
    }
  }

  // ── Binance WebSocket for real-time spot prices ───────────────────────

  _connectBinanceWs() {
    if (this._binanceWs) return;
    const streams = Object.values(ASSET_MAP).map(s => s.toLowerCase() + '@miniTicker');
    const url = 'wss://stream.binance.com:9443/stream?streams=' + streams.join('/');

    // WebSocket should always be available in Node 22+ (package.json engines pins
    // this). If it somehow isn't, fall back to REST polling and set the stats flag
    // so `getStats()` surfaces the degraded state — updown's entire signal quality
    // depends on spot price freshness, so operators need to see this loudly.
    const WS = typeof WebSocket !== 'undefined' ? WebSocket : null;
    if (!WS) {
      this._stats.restFallbackActive = true;
      this._log('warn', 'WebSocket not available — FALLING BACK to Binance REST polling for spot prices (degraded mode). Upgrade to Node 22+ to restore WS feed.');
      // Fall back to polling Binance REST every 3s (built into _evaluateSingleMarket)
      return;
    }
    // Clear the flag in case this is a reconnect after a prior fallback
    this._stats.restFallbackActive = false;

    try {
      this._binanceWs = new WS(url);
    } catch (e) {
      this._log('warn', 'Binance WS creation failed: ' + e.message);
      this._scheduleBinanceReconnect();
      return;
    }

    this._binanceWs.onopen = () => {
      this._log('info', 'Binance WebSocket connected — real-time spot prices active');
    };

    this._binanceWs.onmessage = (event) => {
      try {
        const msg = JSON.parse(typeof event.data === 'string' ? event.data : event.data.toString());
        const data = msg.data || msg;
        if (data.s && data.c) {
          // miniTicker: s=symbol, c=close price (last price)
          this._spotPrices[data.s] = parseFloat(data.c);
        }
      } catch (_) {}
    };

    this._binanceWs.onerror = () => {};

    this._binanceWs.onclose = () => {
      this._binanceWs = null;
      this._log('info', 'Binance WS disconnected — reconnecting...');
      this._scheduleBinanceReconnect();
    };
  }

  _scheduleBinanceReconnect() {
    if (this._binanceReconnectTimer) return;
    this._binanceReconnectTimer = setTimeout(() => {
      this._binanceReconnectTimer = null;
      this._connectBinanceWs();
    }, 5000);
  }

  // ── Market discovery (slower loop — 30s) ──────────────────────────────

  async _refreshMarkets() {
    try {
      const freshMarkets = await this._fetchActiveUpDownMarkets();

      // Merge: keep existing cached markets that haven't expired, add new ones
      const merged = new Map();
      // Keep existing markets that still have time left
      for (const m of this._activeMarkets) {
        const w = this._parseMarketWindow(m.question || '');
        if (w && this._calculateMinutesRemaining(w.endTime) > -1) {
          merged.set(m.conditionId, m);
        }
      }
      // Add fresh discoveries (overwrites stale data for same conditionId)
      for (const m of freshMarkets) {
        merged.set(m.conditionId, m);
      }
      this._activeMarkets = [...merged.values()];
      this._marketsRefreshedAt = Date.now();

      // Subscribe discovered token IDs to WebSocket for real-time prices
      if (this.ws && this._activeMarkets.length > 0) {
        const tokenIds = [];
        for (const m of this._activeMarkets) {
          if (m.tokens) {
            for (const t of m.tokens) {
              if (t.token_id) tokenIds.push(t.token_id);
            }
          }
        }
        if (tokenIds.length > 0) {
          this.ws.subscribe(tokenIds);
        }
      }
    } catch (e) {
      this._log('warn', 'Market refresh failed: ' + e.message);
    }
  }

  // ── Fast evaluation loop (3s — uses cached markets + WS spot prices) ──

  async _evaluateMarkets() {
    // H2: reentrancy guard. setInterval does not wait for async callbacks; if one
    // pass takes longer than 3s (REST fallback Binance fetches + per-market awaits),
    // the next tick fires while the first is still running. Without this guard, two
    // passes can race past `this._tradedIds.has(conditionId)` before either has
    // called `this._tradedIds.add(conditionId)`, causing a double-entry on the same
    // market. Return immediately if another pass is in flight.
    if (this._evaluating) return;
    this._evaluating = true;

    try {
      const cfg = this.getConfig();
      if (!cfg.updown_enabled || this._activeMarkets.length === 0) return;

      this._stats.scans++;
      this._stats.lastScan = new Date().toISOString();
      this._stats.marketsFound += this._activeMarkets.length;

      // Pre-fetch all spot prices once per loop (avoids serial REST calls per market)
      if (!this._binanceWs) {
        // M4: we're in REST fallback. Track so getStats() can surface degraded state.
        this._stats.restFallbackActive = true;
        const now = Date.now();
        for (const sym of Object.values(ASSET_MAP)) {
          // Refresh if stale (>5s) or missing
          if (!this._spotPrices[sym] || !this._spotPriceTs?.[sym] || now - this._spotPriceTs[sym] > 5000) {
            this._stats.restFallbackRequests++;
            try {
              const p = await this._getSpotPrice(sym);
              if (p == null) {
                this._stats.restFallbackFailures++;
              } else {
                this._spotPrices[sym] = p;
                if (!this._spotPriceTs) this._spotPriceTs = {};
                this._spotPriceTs[sym] = now;
              }
            } catch (_) {
              this._stats.restFallbackFailures++;
            }
          }
        }
      }

      for (const market of this._activeMarkets) {
        try {
          await this._evaluateSingleMarket(market, cfg);
        } catch (e) {
          this._log('debug', 'Market eval error: ' + e.message);
        }
      }
    } finally {
      this._evaluating = false;
    }
  }

  async _evaluateSingleMarket(market, cfg) {
    const title = market.question || '';
    const conditionId = market.conditionId;
    if (!conditionId) return;

    // Live guard: predicted-market seeds (wall-clock fallback) have synthetic
    // `pred_<asset>_<endMs>` conditionIds and no real on-chain market. Even if
    // CLOB's resolveTokenIds happened to attach a real tokenId afterwards, the
    // conditionId is still fake — buying against it would create a position
    // with no resolution path. The downstream `!targetTokenId` guard at
    // line ~1196 is NOT sufficient on its own because tokenId resolution may
    // succeed for coincidental title matches. Hard-skip on the `_predicted`
    // flag OR the `pred_` conditionId prefix as a belt-and-suspenders check.
    const isPredicted = market._predicted === true
      || (typeof conditionId === 'string' && conditionId.startsWith('pred_'));
    if (isPredicted && !this._isDryRun()) {
      this._stats.skippedPrediction = (this._stats.skippedPrediction || 0) + 1;
      if (this._stats.skippedPrediction % 50 === 1) {
        this._log('debug', `[LiveGuard] Skipped predicted market in live mode: ${conditionId}`);
      }
      return;
    }

    // Max concurrent UpDown positions — prevent position explosion.
    // Include `_inflightEntries` so concurrent evaluations in the same scan cycle
    // can't all race past the cap while earlier placeOrder calls are still pending.
    const maxUpdownPositions = cfg.updown_maxConcurrentPositions || 8;
    const currentUpdown = (this.risk?.state?.openPositions || []).filter(p => p.copied_from === 'updown_strategy').length;
    const inflight = this._inflightEntries || 0;
    if (currentUpdown + inflight >= maxUpdownPositions) return;

    // Auto-disable: pause if WR < 52% after 50+ resolved trades
    // Dynamic fee: 0.25 * p² * (1-p)², ~1.56% at p=0.50, breakeven ~50.8%
    if (this._paused) return;
    const totalResolved = this._wrStats.wins + this._wrStats.losses;
    if (totalResolved >= 50) {
      const wr = this._wrStats.wins / totalResolved;
      if (wr < 0.52) {
        this._paused = true;
        this._log('warn', `UpDown auto-paused: WR ${(wr * 100).toFixed(1)}% < 52% after ${totalResolved} trades (PnL: $${this._wrStats.totalPnL.toFixed(2)})`);
        return;
      }
    }

    // Dedup
    if (this._tradedIds.has(conditionId)) { this._stats.skippedDedup++; return; }

    // Per-asset auto-disable (only logged once per skip)
    {
      const titleLower = title.toLowerCase();
      let earlyAsset = null;
      if (titleLower.includes('bitcoin')) earlyAsset = 'bitcoin';
      else if (titleLower.includes('ethereum')) earlyAsset = 'ethereum';
      else if (titleLower.includes('solana')) earlyAsset = 'solana';
      if (earlyAsset && this._disabledAssets[earlyAsset]) {
        // Log every 50th occurrence to avoid spam
        if (!this._disabledLogCounter) this._disabledLogCounter = {};
        this._disabledLogCounter[earlyAsset] = (this._disabledLogCounter[earlyAsset] || 0) + 1;
        if (this._disabledLogCounter[earlyAsset] % 50 === 1) {
          this._log('debug', `[Adaptive] Skipping ${earlyAsset} — auto-disabled (${this._disabledAssets[earlyAsset].reason})`);
        }
        return;
      }
    }

    // Parse timing
    const window = this._parseMarketWindow(title);
    if (!window) {
      this._log('debug', `UpDown skip: can't parse window from "${title.slice(0, 60)}"`);
      return;
    }

    // ── Option B: per-duration window filter ──────────────────────────
    // Compute the candle duration so we can (a) filter disabled windows and
    // (b) apply per-window maxMinutesLeft instead of the global setting.
    const windowMins = Math.round((window.endTime.getTime() - window.startTime.getTime()) / 60000);

    // Read enabled windows — live-tunable via DB setting
    let enabledWindows = cfg.updown_enabledWindows;
    try {
      const dbWindows = this.db?.getSetting('updown_enabledWindows', null);
      if (Array.isArray(dbWindows)) enabledWindows = dbWindows;
    } catch (_) { /* fallback to config default */ }

    if (!enabledWindows.includes(windowMins)) {
      // Track per-duration skip count in byDuration bucket
      if (!this._stats.byDuration[windowMins]) {
        this._stats.byDuration[windowMins] = { trades: 0, wins: 0, losses: 0, pnl: 0, skipped: 0 };
      }
      this._stats.byDuration[windowMins].skipped++;
      this._stats.skippedWindowDuration++;
      // Audit every 50th skip to avoid spam
      if (this._stats.skippedWindowDuration % 50 === 1) {
        this.audit?.record('UPDOWN_SKIP', {
          market: title, reason: 'window_duration_disabled', windowMins, enabledWindows
        });
      }
      return;
    }

    // Per-window maxMinutesLeft — fall back to global if not specified
    let maxMinutesLeftByWindow = cfg.updown_maxMinutesLeftByWindow;
    try {
      const dbByWindow = this.db?.getSetting('updown_maxMinutesLeftByWindow', null);
      if (dbByWindow && typeof dbByWindow === 'object') maxMinutesLeftByWindow = dbByWindow;
    } catch (_) { /* fallback to config default */ }
    const effectiveMaxMinutesLeft = (maxMinutesLeftByWindow[windowMins] != null)
      ? maxMinutesLeftByWindow[windowMins]
      : cfg.updown_maxMinutesLeft;

    const minutesLeft = this._calculateMinutesRemaining(window.endTime);
    if (minutesLeft < cfg.updown_minMinutesLeft || minutesLeft > effectiveMaxMinutesLeft) {
      this._stats.skippedTiming++;
      // Log every 20th timing skip to avoid spam
      if (this._stats.skippedTiming % 20 === 1) {
        this._log('debug', `UpDown timing skip: ${minutesLeft.toFixed(1)}min left (window: ${cfg.updown_minMinutesLeft}-${effectiveMaxMinutesLeft}min, ${windowMins}-min candle) "${title.slice(0, 50)}"`);
      }
      return;
    }

    // Determine asset
    const assetKey = Object.keys(ASSET_MAP).find(k => title.toLowerCase().includes(k));
    if (!assetKey) return;
    const symbol = ASSET_MAP[assetKey];

    // Skip excluded assets in live mode (paper still trades them for data collection)
    const isDryRun = this.risk?.getConfig()?.dryRun !== false;
    if (!isDryRun) {
      const excluded = this.db?.getSetting('updown_liveExcludedAssets', []) || [];
      if (excluded.includes(assetKey)) {
        this._log('debug', `Skipping ${assetKey} — excluded from live trading`);
        return;
      }
    }

    // Get spot price — prefer WebSocket (real-time), fallback to REST
    let spotPrice = this._spotPrices[symbol];
    if (!spotPrice) {
      try {
        spotPrice = await this._getSpotPrice(symbol);
      } catch (_) { return; }
    }
    if (!spotPrice) return;

    // Get candle open price from Binance klines (cached per candle)
    let openPrice;
    try {
      openPrice = await this._getCandleOpen(symbol, window);
    } catch (_) { /* fallback below */ }
    // Fallback for predicted candles: cache spot at first evaluation as the "open"
    if (!openPrice) {
      const cacheKey = `${symbol}_${window.startTime.getTime()}`;
      if (!this._openPriceCache) this._openPriceCache = new Map();
      if (this._openPriceCache.has(cacheKey)) {
        openPrice = this._openPriceCache.get(cacheKey);
      } else {
        openPrice = spotPrice; // First time seeing this candle — snapshot spot as open
        this._openPriceCache.set(cacheKey, spotPrice);
        // Clean old entries (keep last 20)
        if (this._openPriceCache.size > 20) {
          const oldest = this._openPriceCache.keys().next().value;
          this._openPriceCache.delete(oldest);
        }
      }
    }

    // Direction and magnitude
    const pctMove = ((spotPrice - openPrice) / openPrice) * 100;
    const absPct = Math.abs(pctMove);

    // Up bias: ties go to Up, so require higher magnitude for Down
    const minMag = pctMove >= 0 ? cfg.updown_minMagnitudePct : cfg.updown_minMagnitudePct * 1.5;
    if (absPct < minMag) { this._stats.skippedMag++; return; }

    const direction = pctMove >= 0 ? 'Up' : 'Down';
    const side = direction === 'Up' ? 'YES' : 'NO';

    // ── Data-driven adaptive rules (per-asset learning) ──────────────
    // Candle duration: 5-min = 66% WR, 15-min = ~50% WR (tracked in _stats.byDuration)
    // windowMins was computed above in the Option B duration filter — reuse it here.

    const assetName = assetKey.toLowerCase();

    // Per-asset auto-disable check (in case it slipped past the early check)
    if (this._disabledAssets[assetName]) {
      this._stats.skippedMag++;
      return;
    }

    // Adaptive magnitude threshold per asset+direction
    // Default: 1.0x for Up, 1.5x for Down (existing Up bias)
    // Learning: if a direction has WR < 50% after 20+ trades → raise to 2.5x
    //           if small magnitudes have WR < 50% after 20+ trades → require medium+
    const directionWR = this._getDirectionWR(assetName, direction);
    const smallMagWR = this._getMagnitudeWR(assetName, 'small');

    // Compute adaptive magnitude multiplier
    let magMultiplier = direction === 'Up' ? 1.0 : 1.5;
    let magReason = 'default';

    if (directionWR != null && directionWR < 52) {
      // This direction has been losing — require 2.5x magnitude
      magMultiplier = 2.5;
      magReason = `${direction} WR ${directionWR.toFixed(1)}%`;
    }

    // Apply adaptive magnitude check
    const adaptiveMinMag = cfg.updown_minMagnitudePct * magMultiplier;
    if (absPct < adaptiveMinMag) {
      this._stats.skippedMag++;
      // Log adaptive decisions every 30 skips
      if (this._stats.skippedMag % 30 === 1 && magReason !== 'default') {
        this._log('debug', `[Adaptive] ${assetName} ${direction} threshold raised to ${adaptiveMinMag.toFixed(3)}% (${magReason})`);
      }
      return;
    }

    // Skip small-magnitude trades for assets where they perform poorly
    if (smallMagWR != null && smallMagWR < 50) {
      const currentBucket = this._getMagnitudeBucket(absPct);
      if (currentBucket === 'small') {
        this._stats.skippedMag++;
        if (this._stats.skippedMag % 30 === 1) {
          this._log('debug', `[Adaptive] ${assetName} skipping small magnitudes (WR ${smallMagWR.toFixed(1)}%)`);
        }
        return;
      }
    }

    // Check market price — for UpDown, HIGHER prices = BETTER (momentum following)
    // Data: <0.20 = 31% WR, 0.40-0.60 = 62% WR, >0.60 = 90% WR
    // Prefer entries where market agrees with our direction (price > 0.40)
    const tokenIdx = side === 'YES' ? 0 : 1;
    const mktPrice = parseFloat(market.tokens?.[tokenIdx]?.price) || 0.5;
    // Only skip if price is extremely high (>0.90 = 10:1 risk/reward against us)
    if (mktPrice > 0.90) { this._stats.skippedPrice++; return; }

    // ── Adaptive sizing based on edge strength + per-asset learning ──
    // Higher market price = market agrees = more confidence = bigger size
    // 5-min candles = higher WR = bigger size
    // Per-asset WR drives the asset multiplier (data-driven, not hardcoded)
    const assetWR = this._getAssetWR(assetName);
    let assetMultiplier;
    if (assetWR == null) {
      // Insufficient data — use neutral multiplier
      assetMultiplier = 1.0;
    } else if (assetWR >= 80) {
      assetMultiplier = 1.5;
    } else if (assetWR >= 70) {
      assetMultiplier = 1.2;
    } else if (assetWR >= 60) {
      assetMultiplier = 1.0;
    } else {
      assetMultiplier = 0.7;
    }

    // Per-window sizing multiplier — live-tunable via DB setting (Option B)
    let sizingMultiplierByWindow = cfg.updown_sizingMultiplierByWindow;
    try {
      const dbSizing = this.db?.getSetting('updown_sizingMultiplierByWindow', null);
      if (dbSizing && typeof dbSizing === 'object') sizingMultiplierByWindow = dbSizing;
    } catch (_) { /* fallback to config default */ }
    // windowMins was computed above during the duration filter; use the same value.
    // Fall back to 1.0 if the duration isn't mapped (safe neutral).
    const windowSizingMultiplier = (sizingMultiplierByWindow[windowMins] != null)
      ? sizingMultiplierByWindow[windowMins]
      : 1.0;

    let sizeUSD = cfg.updown_minSize;
    const edgeMultiplier =
      (mktPrice >= 0.60 ? 2.0 : mktPrice >= 0.40 ? 1.5 : 1.0) *  // price confidence
      windowSizingMultiplier *                                        // per-window sizing (replaces hardcoded 5-min bonus)
      assetMultiplier;                                              // data-driven asset performance
    sizeUSD = Math.min(cfg.updown_maxSize, Math.max(cfg.updown_minSize, Math.round(cfg.updown_minSize * edgeMultiplier)));
    if (absPct >= 0.20) sizeUSD = Math.min(cfg.updown_maxSize, sizeUSD * 2);

    // Resolve token IDs
    const tokens = this._parseTokens(market);
    const targetTokenId = side === 'YES' ? tokens?.upTokenId : tokens?.downTokenId;
    const condId = market.conditionId;

    // C4: guard against missing token IDs. Predicted markets (`pred_*`) and any market
    // where Gamma didn't return clobTokenIds will have undefined tokenId — placing an
    // order with undefined tokenId will silently fail or do something unexpected live.
    // In live mode we MUST have a real token; skip otherwise.
    // (Use the strict _isDryRun() check which also honors the live_strategies whitelist,
    //  not the weaker `isDryRun` computed earlier for the excluded-assets check.)
    if (!targetTokenId && !this._isDryRun()) {
      this._stats.skippedPrice++;
      return;
    }
    // Dry-run with null token: allow through — self-resolution via Binance doesn't
    // need a token ID, and this gives us learning data on predicted/synthetic markets.

    const tradeId = `updown_${(condId || '').slice(0, 8)}_${Date.now()}`;

    // Mark dedup immediately
    this._tradedIds.add(condId);
    this._tradedIdsTTL.set(condId, Date.now() + 10 * 60 * 1000);

    // Audit signal
    this.audit?.record('UPDOWN_SIGNAL', {
      tradeId, market: title, direction, side, symbol,
      spot: spotPrice, open: openPrice, pctMove: +pctMove.toFixed(4),
      marketPrice: mktPrice, sizeUSD, minutesLeft: +minutesLeft.toFixed(1)
    });

    this._log('info', `SIGNAL: ${direction} ${title.slice(0, 50)} | spot=$${spotPrice.toFixed(2)} vs open=$${openPrice.toFixed(2)} (${pctMove >= 0 ? '+' : ''}${pctMove.toFixed(3)}%) | ${side} @$${mktPrice.toFixed(3)} $${sizeUSD}`);

    // Record for the UI Signal Activity Feed.
    // action is set to dry_run/executed in _executeTrade once the trade lands;
    // here we emit a 'signal' marker so the feed shows the intent immediately.
    this._recordEvent({
      conditionId: condId,
      market: title,
      side,
      size: sizeUSD,
      marketPrice: mktPrice,
      action: this._isDryRun() ? 'dry_run' : 'fill',
      rejectReason: null,
      pctMove: +pctMove.toFixed(3),
      minutesLeft: +minutesLeft.toFixed(1)
    });

    // Execute
    await this._executeTrade({
      tradeId, market: title, conditionId: condId,
      tokenId: targetTokenId, side: direction, price: mktPrice, sizeUSD,
      asset: assetKey, symbol, spotPrice, openPrice,
      pctMove: Math.abs(pctMove), direction, minsLeft: minutesLeft,
      // Read from the Gamma-cached market object. _refreshMarkets now preserves
      // m.negRisk; undefined (predicted/synthetic markets) falls back to false.
      negRisk: market.negRisk === true, window,
      windowMins  // per-duration tracking (Option B)
    });
  }

  getStats() {
    return {
      running:  this._interval !== null,
      config:   this.getConfig(),
      ...this._stats,
      tradedIdsActive: this._tradedIds.size
    };
  }

  // ── Legacy scan (redirects to new real-time pipeline) ──────────────────

  async scan() {
    await this._refreshMarkets();
    await this._evaluateMarkets();
  }

  // ── Market evaluation ─────────────────────────────────────────────────

  async _evaluateMarket(market, cfg) {
    const title = market.question || market.title || '';

    // Parse the candle window from the title
    const window = this._parseMarketWindow(title);
    if (!window) return; // can't parse — skip silently

    // Calculate minutes remaining until candle close
    const minsLeft = this._calculateMinutesRemaining(window.endTime);

    // Only trade in the sweet spot: 1-3 minutes remaining
    if (minsLeft < cfg.updown_minMinutesLeft || minsLeft > cfg.updown_maxMinutesLeft) {
      this._stats.skippedTiming++;
      return;
    }

    // Dedup: already traded this candle?
    const conditionId = market.conditionId || market.condition_id;
    if (!conditionId) return;

    if (this._tradedIds.has(conditionId)) {
      this._stats.skippedDedup++;
      return;
    }

    // Determine the asset from title
    const asset = this._parseAsset(title);
    if (!asset) return; // unknown asset

    const symbol = ASSET_MAP[asset];

    // Fetch spot price and candle open in parallel
    let spotPrice, openPrice;
    try {
      [spotPrice, openPrice] = await Promise.all([
        this._getSpotPrice(symbol),
        this._getCandleOpen(symbol)
      ]);
    } catch (e) {
      this._log('warn', `Price fetch failed for ${symbol}: ${e.message}`);
      return;
    }

    if (!spotPrice || !openPrice || spotPrice <= 0 || openPrice <= 0) {
      this._log('debug', `Invalid prices for ${symbol}: spot=${spotPrice}, open=${openPrice}`);
      return;
    }

    // Calculate direction and magnitude
    const pctMove = Math.abs(spotPrice - openPrice) / openPrice * 100;
    const direction = spotPrice >= openPrice ? 'Up' : 'Down';

    // Minimum magnitude filter — avoid the noise zone
    if (pctMove < cfg.updown_minMagnitudePct) {
      this._stats.skippedMag++;
      this.audit?.record('UPDOWN_SKIP', {
        market: title, asset, symbol,
        reason: `magnitude ${pctMove.toFixed(4)}% < min ${cfg.updown_minMagnitudePct}%`,
        spot: spotPrice, open: openPrice, direction, minsLeft: +minsLeft.toFixed(1)
      });
      return;
    }

    // Up bias for borderline cases: if the move is tiny and direction is Down,
    // boost the threshold — Chainlink ties go to Up, so borderline Down is risky
    if (direction === 'Down' && pctMove < cfg.updown_minMagnitudePct * 1.5) {
      this._stats.skippedMag++;
      this.audit?.record('UPDOWN_SKIP', {
        market: title, asset, symbol,
        reason: `Down direction but magnitude ${pctMove.toFixed(4)}% < boosted threshold ${(cfg.updown_minMagnitudePct * 1.5).toFixed(4)}% (Up bias)`,
        spot: spotPrice, open: openPrice, direction, minsLeft: +minsLeft.toFixed(1)
      });
      return;
    }

    // Resolve token IDs for the market
    const tokens = this._parseTokens(market);
    if (!tokens || !tokens.upTokenId || !tokens.downTokenId) {
      this._log('debug', `Could not resolve Up/Down token IDs for "${title}"`);
      return;
    }

    // Our target token
    const targetTokenId = direction === 'Up' ? tokens.upTokenId : tokens.downTokenId;
    const targetOutcome = direction;

    // Check market price for our target token
    let marketPrice;
    try {
      marketPrice = await this._getMarketPrice(targetTokenId);
    } catch (e) {
      this._log('debug', `getMarketPrice failed for ${targetTokenId}: ${e.message}`);
      return;
    }

    if (marketPrice == null) return;

    // Skip if market already prices our direction too high — not enough upside
    if (marketPrice > cfg.updown_maxEntryPrice) {
      this._stats.skippedPrice++;
      this.audit?.record('UPDOWN_SKIP', {
        market: title, asset, symbol,
        reason: `market price ${marketPrice.toFixed(3)} > max entry ${cfg.updown_maxEntryPrice}`,
        spot: spotPrice, open: openPrice, direction, pctMove: +pctMove.toFixed(4), minsLeft: +minsLeft.toFixed(1)
      });
      return;
    }

    // Skip if price is suspiciously low (stale/broken data)
    if (marketPrice <= 0.01) {
      this.audit?.record('UPDOWN_SKIP', {
        market: title, reason: 'market price <= $0.01 (data error)', price: marketPrice
      });
      return;
    }

    // Calculate position size based on magnitude
    const sizeUSD = this._calculateSize(pctMove, cfg);

    // Build trade ID
    const tradeId = `updown_${conditionId.slice(0, 8)}_${Date.now()}`;

    // Log the signal
    this.audit?.record('UPDOWN_SIGNAL', {
      tradeId, market: title, asset, symbol, conditionId,
      direction, targetOutcome, targetTokenId,
      spot: spotPrice, open: openPrice,
      pctMove: +pctMove.toFixed(4),
      marketPrice: +marketPrice.toFixed(3),
      sizeUSD, minsLeft: +minsLeft.toFixed(1)
    });

    // Mark dedup immediately to prevent double-entry from parallel iterations
    this._tradedIds.add(conditionId);
    // Auto-expire dedup after 10 minutes (well past candle close)
    this._tradedIdsTTL.set(conditionId, Date.now() + 10 * 60 * 1000);

    // Execute the trade
    await this._executeTrade({
      tradeId,
      market: title,
      conditionId,
      tokenId: targetTokenId,
      side: targetOutcome,
      price: marketPrice,
      sizeUSD,
      asset,
      symbol,
      spotPrice,
      openPrice,
      pctMove,
      direction,
      minsLeft,
      negRisk: market.negRisk || false,
      window
    });
  }

  // ── Trade execution ───────────────────────────────────────────────────

  async _executeTrade({ tradeId, market, conditionId, tokenId, side, price, sizeUSD, asset, symbol, spotPrice, openPrice, pctMove, direction, minsLeft, negRisk, window, windowMins }) {
    const isDryRun = this._isDryRun();

    // Strategy health check — block if updown strategy is cold
    const stratHealth = this.risk?.checkStrategyHealth?.('updown');
    if (stratHealth && !stratHealth.healthy) {
      this._log('warn', `UpDown strategy circuit breaker: ${stratHealth.reason}`);
      this.audit?.record('UPDOWN_SKIP', { tradeId, market, reason: stratHealth.reason });
      return;
    }

    // Risk check
    let riskResult;
    try {
      riskResult = this.risk.checkTrade({ id: tradeId, market, side, size: sizeUSD, price });
    } catch (e) {
      this._log('warn', `_executeTrade risk.checkTrade threw: ${e.message}`);
      this.audit?.record('UPDOWN_SKIP', { tradeId, market, reason: 'risk.checkTrade threw: ' + e.message });
      this._stats.tradesFailed++;
      return;
    }

    if (!riskResult?.allowed) {
      this.audit?.record('UPDOWN_SKIP', { tradeId, market, reason: riskResult?.reason || 'risk denied', price });
      this._log('debug', `UpDown blocked by risk: ${riskResult?.reason}`);
      return;
    }

    // Apply size adjustment from risk engine
    const finalSize = riskResult.adjustSize != null ? riskResult.adjustSize : sizeUSD;
    if (finalSize < 1) {
      this.audit?.record('UPDOWN_SKIP', { tradeId, market, reason: `adjustedSize ${finalSize} < $1`, price });
      return;
    }

    if (isDryRun) {
      // Paper trade — record without touching CLOB
      this.audit?.record('UPDOWN_FILL', {
        tradeId, market, conditionId, side, direction,
        fillPrice: price, size: finalSize,
        asset, symbol, spot: spotPrice, open: openPrice,
        pctMove: +pctMove.toFixed(4), minsLeft: +minsLeft.toFixed(1),
        pnlEstimate: +(((1 - price) - _cryptoTakerFee(price)) * finalSize).toFixed(4),
        dryRun: true
      });

      this._stats.tradesEntered++;
      this._stats.lastTrade = new Date().toISOString();
      this._stats.pnlEstimate += ((1 - price) - _cryptoTakerFee(price)) * finalSize;

      this._log('info', `[DRY-RUN] UpDown trade: ${direction} on "${market}" @${price.toFixed(3)} size=$${finalSize} | ${asset} spot=${spotPrice.toFixed(2)} open=${openPrice.toFixed(2)} move=${pctMove.toFixed(3)}% minsLeft=${minsLeft.toFixed(1)}`);

      // Log trade to DB for dashboard visibility
      const dbResult = this.db?.logTrade?.({
        market, side: direction === 'Up' ? 'YES' : 'NO',
        price, size: finalSize,
        copied_from: 'updown_strategy',
        status: 'dry_run', dry_run: true,
        created_at: new Date().toISOString()
      });
      const dbTradeId = dbResult?.id || null;

      // ALL dry-run UpDown trades self-resolve via Binance candle close
      // (Don't register with risk engine — exit-engine can't resolve without CLOB)
      // Queue for resolution instead of setTimeout (survives restarts)
      if (!this._pendingResolutions) this._pendingResolutions = [];
      // Ensure we have a window — parse from title if not passed
      const resolveWindow = window || this._parseMarketWindow(market);
      // Capture entry magnitude bucket for adaptive learning feedback
      const magnitudeBucket = this._getMagnitudeBucket(Math.abs(pctMove));
      this._pendingResolutions.push({
        tradeId, dbTradeId, market, direction, symbol,
        openPrice, price, finalSize, window: resolveWindow,
        enteredAt: Date.now(),
        asset, magnitudeBucket,
        windowMins: windowMins || null  // per-duration tracking (Option B)
      });
      // Persist queue to DB so it survives restarts
      this._persistPendingResolutions();

      return;
    }

    // Live trade — place FOK order
    if (!this.clob?.isReady()) {
      this._log('warn', 'UpDown live trade skipped — CLOB not ready');
      this.audit?.record('UPDOWN_SKIP', { tradeId, market, reason: 'CLOB not ready' });
      this._stats.tradesFailed++;
      return;
    }

    const orderShares = Math.floor(finalSize / price);
    if (orderShares < 1) {
      this.audit?.record('UPDOWN_SKIP', { tradeId, market, reason: `orderShares ${orderShares} < 1 at price ${price}` });
      return;
    }

    // Dynamic tick size: the CLOB rejects orders whose price precision exceeds
    // the market's real tick. Binary crypto up/down markets have been observed
    // with both 0.01 and 0.001 tick sizes. Query the SDK first; fall back to
    // 0.01 if the call fails (never block a trade on a metadata lookup).
    let resolvedTickSize = '0.01';
    try {
      if (typeof this.clob.client?.getTickSize === 'function') {
        const t = await this.clob.client.getTickSize(tokenId);
        if (t) resolvedTickSize = String(t);
      }
    } catch (e) {
      this._log('debug', `getTickSize failed for ${tokenId?.slice?.(0, 20)}...: ${e.message}`);
    }

    // Cross-the-spread: the WS/REST cached "market price" is the midpoint/last,
    // not the best ask. A FOK BUY at the midpoint can't take liquidity when the
    // ask is 1–3 ticks higher — SDK returns `"order couldn't be fully filled"`.
    // Query the order book for the real ask and round to tick size; cap at the
    // strategy's max-entry to enforce risk limits.
    let fillPrice = price;
    try {
      const book = await this.clob.client.getOrderBook(tokenId);
      // Polymarket book: asks are sorted ascending by price, so the LAST entry
      // is the best (lowest) ask. (Other CLOB implementations sort differently —
      // always pick the minimum to be safe.)
      if (book?.asks?.length) {
        const askPrices = book.asks.map(a => parseFloat(a.price)).filter(p => Number.isFinite(p) && p > 0);
        if (askPrices.length) {
          const bestAsk = Math.min(...askPrices);
          // Take the best ask directly — it's what sellers are quoting, so a
          // BUY at that price crosses the spread and fills the top of book.
          fillPrice = bestAsk;
        }
      }
    } catch (e) {
      this._log('debug', `getOrderBook failed for ${tokenId?.slice?.(0, 20)}...: ${e.message}`);
    }
    // Round to tick size (the CLOB rejects over-precise prices).
    const tickNum = parseFloat(resolvedTickSize) || 0.01;
    fillPrice = Math.round(fillPrice / tickNum) * tickNum;
    // Enforce the strategy's max entry cap.
    const cfgMaxEntry = this.db?.getSetting('updown_maxEntryPrice', 0.6) || 0.6;
    if (fillPrice > cfgMaxEntry) {
      this._stats.skippedPrice++;
      this.audit?.record('UPDOWN_SKIP', {
        tradeId, market, reason: `best ask ${fillPrice.toFixed(3)} > maxEntry ${cfgMaxEntry}`, price: fillPrice
      });
      return;
    }
    // Recompute shares against the actual fill price.
    let orderSharesFinal = Math.floor(finalSize / fillPrice);
    if (orderSharesFinal < 1) {
      this.audit?.record('UPDOWN_SKIP', {
        tradeId, market, reason: `orderShares ${orderSharesFinal} < 1 at ask ${fillPrice}`
      });
      return;
    }

    // Polymarket requires a minimum $1 notional per order. Bump shares up if
    // the computed notional falls below the floor (e.g. 2 * $0.47 = $0.94).
    if (fillPrice > 0 && orderSharesFinal * fillPrice < 1.01) {
      const minShares = Math.ceil(1.01 / fillPrice);
      if (minShares * fillPrice > finalSize) {
        this.audit?.record('UPDOWN_SKIP', {
          tradeId, market,
          reason: `min $1 notional bump (${minShares} * ${fillPrice.toFixed(3)} = $${(minShares * fillPrice).toFixed(2)}) exceeds finalSize $${finalSize}`
        });
        this._log('warn', `UpDown skip: min-notional bump would exceed maxSize ($${finalSize})`);
        return;
      }
      orderSharesFinal = Math.max(orderSharesFinal, minShares);
    }

    // Reserve an in-flight slot against the concurrent-position cap BEFORE we
    // commit to placing the order. This is released in the finally block at the
    // end of this method, after either risk.openPosition has registered the
    // real position OR the order has failed. Without this, multiple markets in
    // the same scan cycle can read the same stale `currentUpdown` count and
    // race past the cap.
    this._inflightEntries = (this._inflightEntries || 0) + 1;
    let _inflightReleased = false;
    const _releaseInflight = () => {
      if (_inflightReleased) return;
      _inflightReleased = true;
      this._inflightEntries = Math.max(0, (this._inflightEntries || 1) - 1);
    };

    try {
    let orderResult;
    try {
      orderResult = await this.clob.placeOrder(tokenId, 'BUY', fillPrice, orderSharesFinal, {
        tickSize:  resolvedTickSize,
        negRisk:   negRisk,
        orderType: 'FAK'
      });
    } catch (e) {
      this._stats.tradesFailed++;
      this.audit?.record('UPDOWN_FAIL', { tradeId, market, reason: 'placeOrder threw: ' + e.message, price, size: finalSize });
      this._log('warn', `UpDown order failed: ${e.message}`);
      if (!this._isDryRun()) {
        try { this.telegram?.send?.(`⚠️ UpDown LIVE order failed: ${e.message}\nMarket: ${market?.slice(0,40)}`); } catch (_) {}
      }
      return;
    }

    // C3: clob.placeOrder returns { success, orderId, error }. Check success AND propagate
    // the actual error message instead of the generic "no orderId in response".
    const orderId = orderResult?.orderId || orderResult?.id || orderResult?.order_id;
    if (!orderResult?.success || !orderId) {
      this._stats.tradesFailed++;
      const reason = orderResult?.error || 'no orderId in response';
      this.audit?.record('UPDOWN_FAIL', { tradeId, market, reason, price, size: finalSize });
      this._log('warn', `UpDown order failed: ${reason}`);
      if (!this._isDryRun()) {
        try { this.telegram?.send?.(`⚠️ UpDown LIVE order rejected: ${reason}\nMarket: ${market?.slice(0,40)}`); } catch (_) {}
      }
      return;
    }

    // Confirm fill status
    // C2: Polymarket CLOB SDK returns status in UPPERCASE ('MATCHED', 'FILLED').
    // Lowercase before comparing or every live fill is incorrectly classified as failed.
    let status;
    // M2: capture the underlying getOrderStatus error so it reaches the audit log,
    // not just the warn log. Without this, debugging a run of failed live orders
    // is hard because the audit trail only sees "status: unknown".
    let statusError = null;
    try {
      const statusResult = await this.clob.getOrderStatus(orderId);
      status = (statusResult?.status || '').toLowerCase();
    } catch (e) {
      statusError = e.message;
      this._log('warn', `getOrderStatus failed for ${orderId}: ${e.message}`);
      status = 'unknown';
    }

    if (status === 'matched' || status === 'filled') {
      this.audit?.record('UPDOWN_FILL', {
        tradeId, market, conditionId, side, direction,
        fillPrice: price, size: finalSize, orderId,
        asset, symbol, spot: spotPrice, open: openPrice,
        pctMove: +pctMove.toFixed(4), minsLeft: +minsLeft.toFixed(1),
        pnlEstimate: +(((1 - price) - _cryptoTakerFee(price)) * finalSize).toFixed(4),
        dryRun: false
      });

      this._stats.tradesEntered++;
      this._stats.lastTrade = new Date().toISOString();
      this._stats.pnlEstimate += ((1 - price) - _cryptoTakerFee(price)) * finalSize;

      this._log('info', `UpDown FILLED: ${direction} on "${market}" @${price.toFixed(3)} size=$${finalSize} order=${orderId}`);

      // Post-fill sanity: warn if actual fill price drifted far from expected
      if (fillPrice > cfgMaxEntry) {
        this._log('warn', `Post-fill price sanity: fillPrice ${fillPrice.toFixed(3)} > maxEntryPrice ${cfgMaxEntry} — possible slippage`);
        this.audit?.record('UPDOWN_WARN', { tradeId, market, reason: `fill price ${fillPrice.toFixed(3)} exceeded maxEntry ${cfgMaxEntry}`, fillPrice, cfgMaxEntry });
      }

      // Log trade to DB for dashboard visibility
      // C5: db.logTrade returns `{ success: true, id: <int> }` — extract the
      // integer id, don't store the wrapper object. Previously this bug made
      // every downstream `db.updateTrade(pos.tradeId, ...)` call silently fail
      // because updateTrade does `findIndex(t => t.id === id)` — comparing
      // against the wrapper object never matches. The end result: every live
      // winning updown trade stayed stuck at status='open', pnl=null, so
      // exit-engine could never mark it status='won', so scheduler's
      // sweepRedemptions filter (which requires status==='won') never fired,
      // so winning CTF tokens were NEVER REDEEMED to USDC. Money locked forever.
      // The dry-run path already does this correctly (see line ~1417).
      const dbResult = this.db?.logTrade?.({
        market, side: direction === 'Up' ? 'YES' : 'NO',
        price, size: finalSize,
        copied_from: 'updown_strategy',
        status: 'open', dry_run: false
      });
      const dbTradeId = dbResult?.id || null;

      // Register position in risk engine so exit-engine can resolve it
      if (this.risk?.openPosition) {
        this.risk.openPosition({
          id: tradeId,
          tradeId: dbTradeId || tradeId,
          market,
          side: direction === 'Up' ? 'YES' : 'NO',
          size: finalSize, price,
          conditionId,
          tokenId,
          copied_from: 'updown_strategy',
          dryRun: false
        });
      }

      // H1: stash entry metadata for handleLiveExit() to retrieve when the
      // position resolves. risk.openPosition strips unknown fields so we keep
      // a side-map keyed by the updown internal tradeId (matches pos.id on exit).
      // magnitudeBucket can't be derived from the resolved position alone —
      // asset and direction CAN, so we only need to store the bucket here.
      // pctMove is already absolute at this point (see _evaluateSingleMarket).
      this._liveEntryMetadata.set(tradeId, {
        magnitudeBucket: this._getMagnitudeBucket(pctMove),
        openedAt: Date.now(),
        windowMins: windowMins || null  // per-duration tracking (Option B)
      });
      this._persistLiveEntryMetadata();
    } else {
      this._stats.tradesFailed++;
      // M2: include the underlying getOrderStatus error (if any) in the audit
      // record so we can debug why live orders are failing.
      const failReason = statusError
        ? `FOK not filled — status: ${status} (getOrderStatus error: ${statusError})`
        : `FOK not filled — status: ${status}`;
      this.audit?.record('UPDOWN_SKIP', {
        tradeId, market,
        reason: failReason,
        price, size: finalSize, orderId,
        statusError: statusError || undefined
      });
      this._log('debug', `UpDown FOK not filled: "${market}" status=${status}${statusError ? ' error=' + statusError : ''}`);
    }
    } finally {
      // Release in-flight cap reservation. If risk.openPosition succeeded above,
      // the real position is now counted in `openPositions`. If it didn't, the
      // slot just goes back to the pool. Safe to call multiple times.
      _releaseInflight();
    }
  }

  // ── Gamma API ─────────────────────────────────────────────────────────

  async _fetchActiveUpDownMarkets() {
    // Up/Down markets are NOT listed in standard Gamma /markets endpoint.
    // They're dynamically created series markets. Discovery methods:
    // 1. Poll known active wallets via data-api for recent Up/Down trades
    // 2. Use the conditionIds from those trades to get market details

    const DISCOVERY_WALLETS = [
      '0x56e593',   // 96% WR, +$80 — most profitable wallet, trades Up/Down actively
      '0xbefe406c', '0x507e52ef', '0x30149b64'
    ];

    const seen = new Map(); // conditionId -> market info
    const maxAge = 5 * 60; // only trades from last 5 minutes

    // Primary discovery: global trade feed (catches ALL Up/Down activity)
    try {
      const globalR = await axios.get('https://data-api.polymarket.com/trades', {
        params: { limit: 50 },
        timeout: 8000
      });
      const globalTrades = globalR.data || [];
      for (const t of globalTrades) {
        if (!t.conditionId || !t.title) continue;
        if (!/up or down/i.test(t.title)) continue;
        // Must be 5-min candle format
        if (!/\d{1,2}:\d{2}(AM|PM)\s*-\s*\d{1,2}:\d{2}(AM|PM)\s*ET/i.test(t.title)) continue;
        const age = (Date.now() / 1000) - (t.timestamp || 0);
        if (age > maxAge) continue;
        if (seen.has(t.conditionId)) continue;

        seen.set(t.conditionId, {
          question: t.title,
          conditionId: t.conditionId,
          tokens: [
            { outcome: 'Up', price: t.outcomeIndex === 0 ? t.price : (1 - t.price), token_id: null },
            { outcome: 'Down', price: t.outcomeIndex === 1 ? t.price : (1 - t.price), token_id: null }
          ],
          _fromGlobalFeed: true
        });
      }
    } catch (e) {
      this._log('debug', 'Global trade feed discovery failed: ' + e.message);
    }

    // Predictive: from each discovered past candle, generate the NEXT candle
    // e.g. seeing "2:50PM-2:55PM ET" → predict "2:55PM-3:00PM ET" and "3:00PM-3:05PM ET"
    const predictions = [];
    for (const [, m] of seen) {
      const w = this._parseMarketWindow(m.question || '');
      if (!w) continue;
      const asset = Object.keys(ASSET_MAP).find(k => (m.question || '').toLowerCase().includes(k));
      if (!asset) continue;
      const duration = w.endTime.getTime() - w.startTime.getTime();
      // Generate next 2 candles
      for (let offset = 1; offset <= 2; offset++) {
        const nextStart = new Date(w.startTime.getTime() + duration * offset);
        const nextEnd = new Date(w.endTime.getTime() + duration * offset);
        // Format title to match existing parsing.
        // _getETOffset() returns hours-to-ADD-to-ET-to-get-UTC, so converting
        // a UTC date back to ET requires SUBTRACT (ET = UTC - offset).
        // Previous version used `+` which generated titles ~8 hours ahead and
        // silently broke this entire prediction path — predicted titles would
        // re-parse to the wrong window and fail the 1-14 min entry check.
        const fmtET = (d) => {
          const etOff = this._getETOffset();
          const et = new Date(d.getTime() - etOff * 60 * 60 * 1000);
          let h = et.getUTCHours(), mm = et.getUTCMinutes();
          const ap = h < 12 ? 'AM' : 'PM';
          h = h === 0 ? 12 : h > 12 ? h - 12 : h;
          return `${h}:${mm.toString().padStart(2, '0')}${ap}`;
        };
        const months = ['January','February','March','April','May','June','July','August','September','October','November','December'];
        const etOff = this._getETOffset();
        const etDate = new Date(nextStart.getTime() - etOff * 60 * 60 * 1000);
        const title = `${asset.charAt(0).toUpperCase() + asset.slice(1)} Up or Down - ${months[etDate.getUTCMonth()]} ${etDate.getUTCDate()}, ${fmtET(nextStart)}-${fmtET(nextEnd)} ET`;
        const predId = `pred_${asset}_${nextEnd.getTime()}`;
        if (!seen.has(predId) && !this._tradedIds.has(predId)) {
          predictions.push({
            question: title,
            conditionId: predId,
            tokens: [
              { outcome: 'Up', price: 0.5, token_id: null },
              { outcome: 'Down', price: 0.5, token_id: null }
            ],
            _predicted: true
          });
        }
      }
    }
    for (const p of predictions) seen.set(p.conditionId, p);

    // Secondary: wallet-specific discovery (fallback)
    const startTs = Math.floor(Date.now() / 1000) - maxAge;
    for (const wallet of DISCOVERY_WALLETS) {
      try {
        const r = await axios.get(`https://data-api.polymarket.com/trades`, {
          params: { user: wallet, limit: 10, start: startTs, sortBy: 'TIMESTAMP', sortDirection: 'DESC' },
          timeout: 8000
        });
        const trades = r.data || [];
        for (const t of trades) {
          if (!t.conditionId || !t.title) continue;
          if (!/up or down/i.test(t.title)) continue;
          const age = (Date.now() / 1000) - (t.timestamp || 0);
          if (age > maxAge) continue;
          if (seen.has(t.conditionId)) continue;

          // Build a market-like object from trade data
          seen.set(t.conditionId, {
            question: t.title,
            conditionId: t.conditionId,
            tokens: [
              { outcome: 'Up', price: t.outcomeIndex === 0 ? t.price : (1 - t.price), token_id: null },
              { outcome: 'Down', price: t.outcomeIndex === 1 ? t.price : (1 - t.price), token_id: null }
            ],
            _fromTrade: true
          });
        }
        // Rate limit between wallet polls
        await new Promise(r => setTimeout(r, 200));
      } catch (e) {
        // Non-critical — skip this wallet
      }
    }

    // Gamma API discovery — search for active Up/Down markets directly.
    // We bump the limit and drop the `tag=crypto` filter (which appeared to
    // exclude many Up/Down markets) so we get a wider net, then post-filter
    // for Up/Down 5-min candles and sort by closing-soonest. This is the
    // critical path for live mode (only Gamma returns real clobTokenIds).
    try {
      await this._throttleGamma();
      // Default limit=100 does not surface low-liquidity 5-min updown markets —
      // Gamma returns top-100 by some implicit sort that excludes them. Adding
      // an end_date window forces Gamma to include ephemeral markets ending in
      // that window. We query the next ~90 min to cover the 1-14 min entry
      // window plus a buffer, and bump limit to 500 so all current candles fit.
      const nowIso = new Date().toISOString();
      const horizonIso = new Date(Date.now() + 90 * 60 * 1000).toISOString();
      const gammaR = await axios.get('https://gamma-api.polymarket.com/markets', {
        params: {
          limit: 500, active: true, closed: false,
          end_date_min: nowIso,
          end_date_max: horizonIso
        },
        timeout: 15000
      });
      const gammaMarkets = gammaR.data || [];
      // Filter to relevant Up/Down 5-min markets, attach endTs for sorting.
      const ENTRY_HORIZON_MS = 60 * 60 * 1000; // 1h — anything farther is useless to the 1-14 min entry window
      const candidates = [];
      for (const m of gammaMarkets) {
        if (!/up or down/i.test(m.question || '')) continue;
        if (!/\d{1,2}:\d{2}(AM|PM)\s*-\s*\d{1,2}:\d{2}(AM|PM)\s*ET/i.test(m.question || '')) continue;
        if (seen.has(m.conditionId)) continue;
        if (!m.endDate && !m.end_date_iso) continue;
        const endTs = new Date(m.endDate || m.end_date_iso).getTime();
        if (!Number.isFinite(endTs)) continue;
        if (endTs < Date.now()) continue; // already-ended stale entries
        if (endTs > Date.now() + ENTRY_HORIZON_MS) continue; // too far out
        candidates.push({ m, endTs });
      }
      // Sort closing-soonest first so the imminent slot is processed first.
      candidates.sort((a, b) => a.endTs - b.endTs);
      for (const { m } of candidates) {
        try {
          const prices = typeof m.outcomePrices === 'string' ? JSON.parse(m.outcomePrices) : (m.outcomePrices || []);
          const tokenIds = typeof m.clobTokenIds === 'string' ? JSON.parse(m.clobTokenIds) : (m.clobTokenIds || []);
          seen.set(m.conditionId, {
            question: m.question,
            conditionId: m.conditionId,
            // Pass through negRisk so _executeTrade can sign orders against the
            // right exchange contract. Previously dropped → live path hardcoded
            // false, which can cause SDK "Invalid token id" rejections.
            negRisk: m.negRisk === true,
            tokens: [
              { outcome: 'Up', price: parseFloat(prices[0]) || 0.5, token_id: tokenIds[0] || null },
              { outcome: 'Down', price: parseFloat(prices[1]) || 0.5, token_id: tokenIds[1] || null }
            ],
            _fromGamma: true
          });
        } catch (_) {}
      }
    } catch (e) {
      this._log('debug', 'Gamma Up/Down discovery failed: ' + e.message);
    }

    // ── Wall-clock seed (cold-start fix) ──────────────────────────────
    // The discovery paths above only return what *someone has already traded*
    // or what Gamma happens to surface. At cold start (or quiet periods) the
    // imminent next 5-min candles may not appear in any of those, so the
    // strategy waits 5-15 minutes before its first trade. We construct titles
    // for the next few 5-min boundaries directly from wall-clock time so the
    // evaluator always has imminent candidates to score.
    //
    // These are predicted markets (no real clobTokenId), so they only fire in
    // dry-run/paper mode — the live path skips them via the !targetTokenId
    // guard in _evaluateSingleMarket. Live mode relies on the Gamma path
    // above, which is also imminent-sorted.
    //
    // We only seed windows that aren't already covered by a real market in
    // `seen`, so this never causes double-trading on the same candle.
    try {
      const FIVE_MIN_MS = 5 * 60 * 1000;
      const SEED_HORIZON = 3; // next 3 candles per asset (~5-15 min ahead)
      const SEED_ASSETS = [
        { key: 'bitcoin',  display: 'Bitcoin' },
        { key: 'ethereum', display: 'Ethereum' },
        { key: 'solana',   display: 'Solana' },
      ];
      // Build a set of (asset, startTime) tuples already covered by real markets
      const coveredWindows = new Set();
      for (const m of seen.values()) {
        if (m._predicted) continue; // don't dedupe against earlier predictions
        const w = this._parseMarketWindow(m.question || '');
        if (!w) continue;
        const a = this._parseAsset(m.question || '');
        if (!a) continue;
        coveredWindows.add(`${a}_${w.startTime.getTime()}`);
      }
      const months = ['January','February','March','April','May','June','July','August','September','October','November','December'];
      const etOff = this._getETOffset();
      const toET = (utcMs) => new Date(utcMs - etOff * 60 * 60 * 1000);
      const fmtET = (utcMs) => {
        const et = toET(utcMs);
        let h = et.getUTCHours(), mm = et.getUTCMinutes();
        const ap = h < 12 ? 'AM' : 'PM';
        h = h === 0 ? 12 : h > 12 ? h - 12 : h;
        return `${h}:${mm.toString().padStart(2, '0')}${ap}`;
      };
      const now = Date.now();
      const firstStart = Math.ceil(now / FIVE_MIN_MS) * FIVE_MIN_MS;
      let seeded = 0;
      for (let i = 0; i < SEED_HORIZON; i++) {
        const startMs = firstStart + i * FIVE_MIN_MS;
        const endMs = startMs + FIVE_MIN_MS;
        const etStart = toET(startMs);
        for (const { key, display } of SEED_ASSETS) {
          if (coveredWindows.has(`${key}_${startMs}`)) continue;
          const title = `${display} Up or Down - ${months[etStart.getUTCMonth()]} ${etStart.getUTCDate()}, ${fmtET(startMs)}-${fmtET(endMs)} ET`;
          const predId = `pred_${key}_${endMs}`;
          if (seen.has(predId) || this._tradedIds.has(predId)) continue;
          seen.set(predId, {
            question: title,
            conditionId: predId,
            tokens: [
              { outcome: 'Up', price: 0.5, token_id: null },
              { outcome: 'Down', price: 0.5, token_id: null }
            ],
            _predicted: true,
            _wallClockSeed: true
          });
          seeded++;
        }
      }
      if (seeded > 0) {
        this._log('debug', `[WallClockSeed] added ${seeded} imminent predicted candles`);
      }
    } catch (e) {
      this._log('debug', 'Wall-clock seed failed: ' + e.message);
    }

    // Note: post-discovery resolveTokenIds enrichment removed. Historically
    // this loop attempted to attach token IDs to wall-clock-seeded predicted
    // markets by calling clob.resolveTokenIds(mkt.question). With the live
    // guard (C4) rejecting null token_id markets in live mode, and the
    // date-range-based resolveTokenIds in clob.js (which only exact-matches
    // real Gamma titles), the loop was both dead code in live and a source
    // of the original mis-token silent-corruption bug. Paper mode is
    // unaffected: real markets already arrive with token_ids from the
    // discovery fetch, and predicted markets intentionally have null ids.
    const markets = [...seen.values()];

    this._log('debug', `Discovered ${markets.length} Up/Down markets from ${DISCOVERY_WALLETS.length} wallets + Gamma API`);
    return markets;
  }

  // ── Binance API ───────────────────────────────────────────────────────

  async _getSpotPrice(symbol) {
    await this._throttleBinance();
    if (this.rateLimiter && !this.rateLimiter.consume('binance')) {
      this._log('warn', 'Rate limited — skipping Binance spot price');
      return null;
    }

    const r = await axios.get(BINANCE_TICKER, {
      params: { symbol },
      timeout: 5000
    });

    const price = parseFloat(r.data?.price);
    return isNaN(price) ? null : price;
  }

  async _getCandleOpen(symbol, window) {
    await this._throttleBinance();
    if (this.rateLimiter && !this.rateLimiter.consume('binance')) {
      this._log('warn', 'Rate limited — skipping Binance candle open');
      return null;
    }

    const params = { symbol, interval: '5m', timeout: 5000 };

    if (window?.startTime) {
      // Fetch the exact candle covering the Polymarket market window
      const startMs = window.startTime.getTime();
      params.startTime = startMs;
      params.endTime = startMs + 5 * 60 * 1000;
      params.limit = 1;
    } else {
      // Fallback: latest candle
      params.limit = 1;
    }

    const r = await axios.get(BINANCE_KLINES, { params, timeout: 5000 });

    // Kline format: [openTime, open, high, low, close, volume, ...]
    const kline = r.data?.[0];
    if (!kline) return null;

    const openPrice = parseFloat(kline[1]);
    return isNaN(openPrice) ? null : openPrice;
  }

  // ── Market price check ────────────────────────────────────────────────

  async _getMarketPrice(tokenId) {
    // Try WS cached price first (zero API calls).
    // M1: 5-second staleness cap. 5-min candle strategy — a price from 30s ago
    // could be the previous candle entirely. The websocket cache's default 2-min
    // staleness is way too loose for this use case.
    if (this.ws && this.ws.isConnected() && !this.ws.fallbackToREST) {
      const wsPrice = this.ws.getCachedPrice(tokenId, 5000);
      if (wsPrice != null) return parseFloat(wsPrice);
    }
    // Try CLOB REST, then fall back to Gamma token price from parsed data
    if (this.clob?.isReady()) {
      try {
        const price = await this.clob.getPrice(tokenId, 'BUY');
        if (price != null) return parseFloat(price);
      } catch (e) {
        this._log('debug', `CLOB getPrice failed for ${tokenId}: ${e.message}`);
      }
    }
    return null;
  }

  // ── Title parsing ─────────────────────────────────────────────────────

  /**
   * Parse the candle window from a market title.
   *
   * Examples:
   *   "Bitcoin Up or Down - April 4, 9:45PM-9:50PM ET"
   *   "Ethereum Up or Down - April 4, 2:00AM-2:05AM ET"
   *   "Solana Up or Down - March 31, 11:55PM-12:00AM ET"
   *
   * Returns: { startTime: Date, endTime: Date } or null if unparseable
   */
  _parseMarketWindow(title) {
    // Match: "Month Day, StartTime-EndTime ET"
    // Handle both 12h formats with optional leading zero
    const re = /(\w+)\s+(\d{1,2}),?\s+(\d{1,2}):(\d{2})(AM|PM)\s*-\s*(\d{1,2}):(\d{2})(AM|PM)\s*ET/i;
    const m = re.exec(title);
    if (!m) {
      // Fallback: match "Month Day, HourAM/PM ET" (hourly markets — not 5-min candles, skip)
      // These markets don't fit the 5-min strategy
      return null;
    }

    const [, monthStr, dayStr, startH, startM, startAP, endH, endM, endAP] = m;

    const month = this._parseMonth(monthStr);
    if (month === -1) return null;

    const day = parseInt(dayStr, 10);

    // Determine year — use current year, handle Dec→Jan rollover
    const now = new Date();
    let year = now.getFullYear();

    // Build dates in ET (Eastern Time)
    // We construct in UTC and offset. ET = UTC-4 (EDT) or UTC-5 (EST).
    // Use Intl to determine current ET offset dynamically.
    const etOffset = this._getETOffset();

    const startHour24 = this._to24h(parseInt(startH, 10), startAP.toUpperCase());
    const startMin    = parseInt(startM, 10);
    const endHour24   = this._to24h(parseInt(endH, 10), endAP.toUpperCase());
    const endMin      = parseInt(endM, 10);

    // Build start time in ET then convert to UTC
    const startDate = new Date(Date.UTC(year, month, day, startHour24 + etOffset, startMin, 0));
    let   endDate   = new Date(Date.UTC(year, month, day, endHour24 + etOffset, endMin, 0));

    // Handle midnight crossover: if end < start, add a day to end
    // e.g., 11:55PM-12:00AM means end is next day
    if (endDate <= startDate) {
      endDate = new Date(endDate.getTime() + 24 * 60 * 60 * 1000);
    }

    return { startTime: startDate, endTime: endDate };
  }

  _parseMonth(str) {
    const months = {
      january: 0, february: 1, march: 2, april: 3, may: 4, june: 5,
      july: 6, august: 7, september: 8, october: 9, november: 10, december: 11
    };
    return months[str.toLowerCase()] ?? -1;
  }

  _to24h(hour, ampm) {
    if (ampm === 'AM') {
      return hour === 12 ? 0 : hour;
    } else {
      return hour === 12 ? 12 : hour + 12;
    }
  }

  _getETOffset() {
    // Return hours to ADD to ET to get UTC (positive = ahead)
    // EDT (March-Nov): ET = UTC-4, so offset = +4
    // EST (Nov-March): ET = UTC-5, so offset = +5
    try {
      // Use a reference date to check if we're in EDT or EST
      const jan = new Date(new Date().getFullYear(), 0, 1);
      const jul = new Date(new Date().getFullYear(), 6, 1);

      // Get offset in minutes for January (EST) and July (EDT)
      // We use Intl to check the actual ET zone
      const formatter = new Intl.DateTimeFormat('en-US', { timeZone: 'America/New_York', hour: 'numeric', hour12: false });

      // Current hour in ET vs UTC tells us the offset
      const nowUTC = new Date();
      const etParts = new Intl.DateTimeFormat('en-US', {
        timeZone: 'America/New_York',
        year: 'numeric', month: '2-digit', day: '2-digit',
        hour: '2-digit', minute: '2-digit', second: '2-digit',
        hour12: false
      }).formatToParts(nowUTC);

      const etHour = parseInt(etParts.find(p => p.type === 'hour')?.value || '0', 10);
      const utcHour = nowUTC.getUTCHours();

      // Offset = UTC hour - ET hour (mod 24)
      let diff = utcHour - etHour;
      if (diff < 0) diff += 24;
      if (diff > 12) diff -= 24; // normalize

      return diff; // typically 4 (EDT) or 5 (EST)
    } catch (e) {
      // Fallback: assume EDT (UTC-4)
      return 4;
    }
  }

  /**
   * Determine asset from title keywords.
   * Returns lowercase key from ASSET_MAP or null.
   */
  _parseAsset(title) {
    const lower = title.toLowerCase();
    for (const key of Object.keys(ASSET_MAP)) {
      if (lower.includes(key)) return key;
    }
    // Also handle abbreviations that might appear
    if (lower.includes('btc')) return 'bitcoin';
    if (lower.includes('eth')) return 'ethereum';
    if (lower.includes('sol')) return 'solana';
    return null;
  }

  _calculateMinutesRemaining(endTime) {
    const now = Date.now();
    return (endTime.getTime() - now) / (60 * 1000);
  }

  // ── Position sizing ───────────────────────────────────────────────────

  _calculateSize(pctMove, cfg) {
    const min = cfg.updown_minSize;
    const max = cfg.updown_maxSize;

    if (pctMove >= 0.20) return max;       // $20 — strong conviction
    if (pctMove >= 0.10) return Math.min(Math.max(min, 10), max);  // $10 — medium
    return min;                            // $5 — minimum viable
  }

  // ── Token parsing from Gamma market data ──────────────────────────────

  _parseTokens(market) {
    const tokens = market.tokens || [];

    let upTokenId = null;
    let downTokenId = null;

    for (const t of tokens) {
      const outcome = (t.outcome || '').toLowerCase();
      if (outcome === 'up' || outcome === 'yes') {
        upTokenId = t.token_id || t.tokenId || null;
      } else if (outcome === 'down' || outcome === 'no') {
        downTokenId = t.token_id || t.tokenId || null;
      }
    }

    if (!upTokenId || !downTokenId) return null;
    return { upTokenId, downTokenId };
  }

  _normalizeGammaMarket(m) {
    if (!m) return m;
    // Parse JSON string fields if needed (Gamma returns these as strings)
    if (!m.tokens) {
      try {
        const outcomes   = typeof m.outcomes === 'string' ? JSON.parse(m.outcomes) : (m.outcomes || []);
        const prices     = typeof m.outcomePrices === 'string' ? JSON.parse(m.outcomePrices) : (m.outcomePrices || []);
        const tokenIds   = typeof m.clobTokenIds === 'string' ? JSON.parse(m.clobTokenIds) : (m.clobTokenIds || []);
        m.tokens = outcomes.map((o, i) => ({
          outcome:  o,
          price:    prices[i] || '0',
          token_id: tokenIds[i] || null,
          winner:   m.resolved && parseFloat(prices[i]) === 1 ? true : false
        }));
      } catch (e) {
        m.tokens = [];
      }
    }
    return m;
  }

  // ── Rate limiting ─────────────────────────────────────────────────────

  async _throttleBinance() {
    const elapsed = Date.now() - this._lastBinanceCall;
    if (elapsed < 200) await new Promise(r => setTimeout(r, 200 - elapsed));
    this._lastBinanceCall = Date.now();
  }

  async _throttleGamma() {
    const elapsed = Date.now() - this._lastGammaCall;
    if (elapsed < 2000) await new Promise(r => setTimeout(r, 2000 - elapsed));
    this._lastGammaCall = Date.now();
  }

  // ── Dedup cleanup ─────────────────────────────────────────────────────

  _cleanupTradedIds() {
    const now = Date.now();
    for (const [id, expiry] of this._tradedIdsTTL) {
      if (now >= expiry) {
        this._tradedIds.delete(id);
        this._tradedIdsTTL.delete(id);
      }
    }
    // H1: also GC stale live-entry metadata from abandoned positions (24h default)
    this._gcLiveEntryMetadata();
  }

  // ── Internal helpers ──────────────────────────────────────────────────

  _isDryRun() {
    try {
      const cfg = this.risk?.getConfig?.();
      if (cfg?.dryRun !== false) return true; // global paper = everything paper
      const liveStrategies = this.db?.getSetting('live_strategies', []) || [];
      if (!liveStrategies.includes('updown')) {
        if (!this._loggedForcedPaper) { this._log('info', '[UpDown] Forced paper mode — not in live_strategies whitelist'); this._loggedForcedPaper = true; }
        return true;
      }
      return false;
    } catch (_) {
      return true; // default to safe/dry-run if risk not available
    }
  }

  /** Reverse-lookup asset key from Binance symbol (e.g. "BTCUSDT" → "bitcoin") */
  _symbolToAsset(symbol) {
    if (!symbol) return null;
    for (const [key, sym] of Object.entries(ASSET_MAP)) {
      if (sym === symbol) return key;
    }
    return null;
  }

  async _safeRun(name, fn) {
    try {
      await fn();
    } catch (e) {
      this._log('warn', `Task ${name} threw (suppressed): ${e.message}`);
    }
  }

  _log(level, msg, data) {
    if (this._customLog) {
      try { this._customLog(level, msg, data); return; } catch (_) {}
    }
    const fn = (level === 'warn' || level === 'error') ? console.error : console.log;
    fn('[UpDownStrategy]', msg, data || '');
  }
}

module.exports = UpDownStrategy;
