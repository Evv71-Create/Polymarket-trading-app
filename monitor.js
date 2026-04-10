/**
 * Wallet Monitor + Market Scanner
 * Wallet mode: polls watched wallets for new trades
 * Market scanner mode: polls a specific market's activity to find bot traders
 */

const axios = require('axios');

const DATA_API = 'https://data-api.polymarket.com';
const GAMMA    = 'https://gamma-api.polymarket.com';
const CLOB     = 'https://clob.polymarket.com';

class WalletMonitor {
  constructor(db, risk, rateLimiter, opts = {}) {
    this.db = db;
    this.risk = risk;
    this.rateLimiter = rateLimiter;
    this.ws = opts.ws || null;  // Polymarket WebSocket for real-time trade detection

    // ── Wallet monitoring ──
    this.wallets = new Map();
    this.callbacks = [];
    this.alertCallbacks = [];
    this.decayCallbacks = [];
    this._whaleSellCallbacks = [];
    this.interval = null;
    this.pollIntervalMs = 10000;    // 10 seconds — WS is primary, REST is fast fallback
    this.running = false;
    this.stats = { polls: 0, tradesDetected: 0, errors: 0 };

    // ── API anomaly detection ──
    this._apiAnomaly = false;
    this._apiAnomalyCount = 0;

    // ── Market scanner ──
    this.scanner = {
      enabled: false,
      interval: null,
      pollIntervalMs: 5000,         // 5 seconds for bot detection
      marketPattern: null,           // e.g. "bitcoin up or down"
      seenTradeIds: new Set(),
      walletActivity: new Map(),     // address -> { count, lastSeen, sides, names }
      totalScanned: 0,
      errors: 0,
      lastPoll: null
    };
  }

  // ═══════════════════════════════════════════════════════════════════
  //  WALLET MONITORING (existing functionality)
  // ═══════════════════════════════════════════════════════════════════

  watch(address, name, opts = {}) {
    if (!address) return;
    this.wallets.set(address, {
      name: name || address.slice(0, 8) + '...',
      lastSeenIds: new Set(),
      winRate: opts.winRate || 0,
      volume: opts.volume || 0,
      estimatedPortfolio: opts.estimatedPortfolio || opts.volume || 0,
      minPositionAlert: opts.minPositionAlert || 1000,
      autoCopy: opts.autoCopy || false,
      errors: 0,
      paused: false,
      recentResults: []
    });
    this.log('info', `Watching wallet: ${name || address}`);
    this.persistWallets();
  }

  unwatch(address) {
    this.wallets.delete(address);
    this.log('info', `Stopped watching: ${address}`);
    this.persistWallets();
  }

  onTrade(callback) { this.callbacks.push(callback); }
  onAlert(callback) { this.alertCallbacks.push(callback); }
  onDecay(callback) { this.decayCallbacks.push(callback); }
  onWhaleSell(callback) { this._whaleSellCallbacks.push(callback); }

  offTrade(callback) { this.callbacks = this.callbacks.filter(cb => cb !== callback); }
  offAlert(callback) { this.alertCallbacks = this.alertCallbacks.filter(cb => cb !== callback); }
  offDecay(callback) { this.decayCallbacks = this.decayCallbacks.filter(cb => cb !== callback); }
  offWhaleSell(callback) { this._whaleSellCallbacks = this._whaleSellCallbacks.filter(cb => cb !== callback); }
  clearCallbacks() {
    this.callbacks = [];
    this.alertCallbacks = [];
    this.decayCallbacks = [];
    this._whaleSellCallbacks = [];
  }

  start(intervalMs) {
    if (this.running) return;
    if (intervalMs) this.pollIntervalMs = intervalMs;
    this.running = true;
    this.log('info', `Wallet monitor started — polling every ${this.pollIntervalMs / 1000}s`);
    // Seed: do an initial poll to populate lastSeenIds WITHOUT firing trade callbacks
    this._seeding = true;
    this.poll().then(() => {
      this._seeding = false;
      this.log('info', `Seeded ${this.wallets.size} wallet(s) — trade replay prevention active`);
      // Wire WS trade listener after seeding (so we have lastSeenIds populated)
      this._setupWsTradeListener();
    }).catch(() => { this._seeding = false; });
    this.interval = setInterval(() => this.poll(), this.pollIntervalMs);
  }

  /**
   * Wire WebSocket trade events for real-time trade detection.
   * When WS is connected, trades arrive instantly instead of waiting for REST poll.
   * REST polling still runs as fallback when WS is disconnected.
   */
  _setupWsTradeListener() {
    if (!this.ws || this._wsTradeListenerActive) return;
    this._wsTradeListenerActive = true;
    this.ws.on('trade', (data) => {
      if (!this.running || this._seeding) return;
      try {
        // Check if this trade belongs to a watched wallet
        const tradeAddr = (data.maker || data.taker || data.owner || data.user || '').toLowerCase();
        for (const [address, wallet] of this.wallets.entries()) {
          if (wallet.paused) continue;
          if (tradeAddr && tradeAddr === address.toLowerCase()) {
            const id = data.transactionHash || data.id || `ws-${Date.now()}-${tradeAddr}`;
            if (wallet.lastSeenIds.has(id)) continue;
            wallet.lastSeenIds.add(id);
            this.stats.tradesDetected++;
            // Fire trade callbacks (same as REST path)
            for (const cb of this.callbacks) {
              try { cb(data, wallet, address); } catch (_) {}
            }
            this.log('info', `WS trade detected for ${wallet.name}: ${JSON.stringify(data).slice(0, 200)}`);
          }
        }
      } catch (e) {
        this.log('debug', 'WS trade handler error: ' + e.message);
      }
    });
    this.log('info', 'WebSocket trade listener wired — real-time trade detection active');
  }

  stop() {
    if (this.interval) { clearInterval(this.interval); this.interval = null; }
    this.running = false;
    this.stopScanner();
    this.log('info', 'Wallet monitor stopped');
  }

  async poll() {
    if (this._pollBusy) return; // guard against overlapping polls
    this._pollBusy = true;
    this.stats.polls++;
    try {
      for (const [address, wallet] of this.wallets.entries()) {
        if (wallet.paused) continue;

        if (this.rateLimiter && !this.rateLimiter.consume('polymarket_data')) {
          this.log('warn', 'Rate limited — skipping poll cycle');
          break;
        }

        try {
          await this.pollWallet(address, wallet);
          wallet.errors = 0;
        } catch (e) {
          wallet.errors++;
          this.stats.errors++;
          this.log('warn', `Poll failed for ${wallet.name}`, { error: e.message, consecutive: wallet.errors });

          if (this.rateLimiter && e.response?.status === 429) {
            this.rateLimiter.reportRateLimit('polymarket_data');
          }

          if (wallet.errors >= 5) {
            wallet.paused = true;
            this.log('error', `Paused monitoring for ${wallet.name} after 5 consecutive errors. Call unpause to resume.`);
            this.persistWallets();
          }
        }

        // Small delay between wallet polls to avoid hammering the API
        await new Promise(r => setTimeout(r, 500));
      }
    } finally {
      this._pollBusy = false;
    }
  }

  unpauseWallet(address) {
    const wallet = this.wallets.get(address);
    if (wallet) {
      wallet.paused = false;
      wallet.errors = 0;
      this.log('info', `Unpaused wallet: ${wallet.name}`);
      this.persistWallets();
    }
  }

  async pollWallet(address, wallet) {
    // If WebSocket is connected and not in fallback mode, skip REST poll.
    // The WS trade listener (wired in _setupWsTradeListener) handles real-time detection.
    if (this.ws && this.ws.isConnected() && !this.ws.fallbackToREST && this._wsTradeListenerActive) {
      return;
    }

    const params = { user: address, limit: 10 };
    // Use lastPollTimestamp to avoid re-fetching old trades
    if (wallet.lastPollTimestamp) {
      params.start = wallet.lastPollTimestamp;
    }
    const r = await axios.get(`${DATA_API}/trades`, {
      params,
      timeout: 8000
    });
    // Update timestamp for next poll
    wallet.lastPollTimestamp = Math.floor(Date.now() / 1000);

    if (this.rateLimiter) this.rateLimiter.clearBackoff('polymarket_data');

    const trades = r.data || [];
    if (trades.length > 0) this._validateApiHealth(trades);

    // DIAG: log poll results for any wallet with fresh trades
    if (trades.length > 0) {
      const newestAge = Math.round((Date.now() / 1000 - (trades[0].timestamp || 0)) / 60);
      if (newestAge < 180) {
        this.log('info', `DIAG pollWallet ${address.slice(0,10)}: ${trades.length} trades, newest ${newestAge}min, seenIds=${wallet.lastSeenIds.size}, autoCopy=${wallet.autoCopy}`);
      }
    }

    const MAX_TRADE_AGE_MS = 2 * 60 * 60 * 1000; // 2 hours — stale trades are in expired markets
    const newTrades = trades.filter(t => {
      const id = t.transactionHash || `${t.proxyWallet}-${t.timestamp}-${t.price}`;
      return !wallet.lastSeenIds.has(id);
    });

    if (newTrades.length === 0) return;

    // Mark all fetched trades as seen (prevents replay on subsequent polls)
    for (const t of trades) {
      const id = t.transactionHash || `${t.proxyWallet}-${t.timestamp}-${t.price}`;
      wallet.lastSeenIds.add(id);
    }

    // Filter out stale trades (older than 2 hours) — prevents copying into expired/past markets
    const freshTrades = newTrades.filter(t => {
      // If no timestamp, we can't verify freshness — skip to be safe
      if (!t.timestamp) {
        this.log('debug', `Skipping trade with missing timestamp: ${t.market || t.asset}`);
        return false;
      }
      const tradeTs = typeof t.timestamp === 'number' ? t.timestamp * 1000 : new Date(t.timestamp).getTime();
      const ageMs = Date.now() - tradeTs;
      if (ageMs > MAX_TRADE_AGE_MS) {
        this.log('debug', `Skipping stale trade (${Math.round(ageMs / 60000)}min old): ${t.market || t.asset}`);
        return false;
      }
      return true;
    });
    if (wallet.lastSeenIds.size > 50) {
      const arr = [...wallet.lastSeenIds];
      wallet.lastSeenIds = new Set(arr.slice(-50));
    }

    // During seeding, skip callbacks — just populate lastSeenIds
    if (this._seeding) return;

    for (const trade of freshTrades) {
      const processed = this.processTrade(trade, address, wallet);
      this.stats.tradesDetected++;

      // Fire whale-sell callbacks for ALL monitored wallets, regardless of auto_copy flag
      if (processed.action === 'SELL' && this._whaleSellCallbacks.length > 0) {
        const wResults = await Promise.allSettled(this._whaleSellCallbacks.map(cb => cb(processed)));
        for (const r of wResults) {
          if (r.status === 'rejected') this.log('error', 'WhaleSell callback error', { error: r.reason?.message || r.reason });
        }
      }

      if (this.db) {
        try {
          this.db.logWalletActivity({
            wallet_address: address, wallet_name: wallet.name,
            market: processed.market, side: processed.side,
            price: processed.price, size: processed.size
          });
        } catch (e) { this.log('warn', 'Failed to log wallet activity', { error: e.message }); }
      }

      const tResults = await Promise.allSettled(this.callbacks.map(cb => cb(processed)));
      for (const r of tResults) {
        if (r.status === 'rejected') this.log('error', 'Trade callback error', { error: r.reason?.message || r.reason });
      }

      if (processed.size >= wallet.minPositionAlert) {
        const aResults = await Promise.allSettled(this.alertCallbacks.map(cb => Promise.resolve(cb({ type: 'large_position', wallet: wallet.name, address, trade: processed }))));
        for (const r of aResults) {
          if (r.status === 'rejected') this.log('error', 'Alert callback error', { error: r.reason?.message || r.reason });
        }
      }
    }
  }

  processTrade(raw, address, wallet) {
    const rawSide = (raw.side || '').toUpperCase();  // BUY or SELL
    // The data API provides 'outcomeIndex' (0=YES token, 1=NO token) and 'outcome' (human label).
    // For "Up or Down" markets, outcome="Up" is index 0 (YES), outcome="Down" is index 1 (NO).
    // IMPORTANT: Always use outcomeIndex for the YES/NO mapping, NOT the outcome string,
    // because outcome can be "Up"/"Down"/"Trump"/"Harris"/etc. — not always "Yes"/"No".
    let outcomeToken;
    if (raw.outcomeIndex !== undefined && raw.outcomeIndex !== null) {
      outcomeToken = parseInt(raw.outcomeIndex) === 0 ? 'YES' : 'NO';
    } else {
      // Fallback for legacy data without outcomeIndex
      const rawOutcome = (raw.outcome || '').toLowerCase();
      outcomeToken = (rawOutcome === 'no' || rawOutcome === 'down') ? 'NO' : 'YES';
    }

    return {
      wallet_address: address,
      wallet_name: wallet.name,
      market: raw.title || raw.question || raw.market || 'Unknown market',
      conditionId: raw.conditionId || null,
      action: rawSide === 'SELL' ? 'SELL' : 'BUY',  // BUY or SELL
      side: outcomeToken,                              // YES or NO (from outcome field)
      price: parseFloat(raw.price) || 0,
      size: parseFloat(raw.amount || raw.size || raw.usdcSize) || 0,
      timestamp: raw.timestamp || new Date().toISOString(),
      win_rate: wallet.winRate,
      volume: wallet.volume,
      wallet_portfolio: wallet.estimatedPortfolio || wallet.volume || 0,
      auto_copy: wallet.autoCopy,
      raw
    };
  }

  // ── Wallet performance decay detection ────────────────────────────

  recordWalletResult(address, pnl) {
    const wallet = this.wallets.get(address);
    if (!wallet) return;
    wallet.recentResults.push({ pnl, timestamp: Date.now() });
    if (wallet.recentResults.length > 50) wallet.recentResults.shift();
  }

  checkDecay(windowDays = 7, minTrades = 5, thresholdPct = 15) {
    const cutoff = Date.now() - windowDays * 86400000;
    const decayed = [];

    for (const [address, wallet] of this.wallets) {
      const recent = wallet.recentResults.filter(r => r.timestamp >= cutoff);
      if (recent.length < minTrades) continue;

      const wins = recent.filter(r => r.pnl > 0).length;
      const recentWinRate = (wins / recent.length) * 100;
      const historicalWinRate = wallet.winRate || 0;

      if (historicalWinRate > 0 && (historicalWinRate - recentWinRate) >= thresholdPct) {
        const info = {
          address, name: wallet.name,
          historicalWinRate, recentWinRate: +recentWinRate.toFixed(1),
          recentTrades: recent.length, dropPct: +(historicalWinRate - recentWinRate).toFixed(1)
        };
        decayed.push(info);
        this.log('warn', `Wallet decay detected: ${wallet.name}`, info);

        for (const cb of this.decayCallbacks) {
          try { cb(info); } catch (e) {}
        }
      }
    }
    return decayed;
  }

  // ── Safe settings update ──────────────────────────────────────────

  static SAFE_UPDATE_KEYS = ['name', 'winRate', 'volume', 'estimatedPortfolio', 'minPositionAlert', 'autoCopy'];

  updateSettings(address, updates) {
    const wallet = this.wallets.get(address);
    if (!wallet) return;
    for (const [k, v] of Object.entries(updates)) {
      if (WalletMonitor.SAFE_UPDATE_KEYS.includes(k)) wallet[k] = v;
    }
  }

  // ═══════════════════════════════════════════════════════════════════
  //  MARKET SCANNER — find bot traders on a specific market
  // ═══════════════════════════════════════════════════════════════════

  /**
   * Start scanning a market's trade feed for frequent traders.
   * @param {string} marketPattern - substring to match in market names, e.g. "bitcoin up or down"
   * @param {number} intervalMs - poll interval in ms (default 5000)
   */
  startScanner(marketPattern, intervalMs) {
    this.stopScanner();

    this.scanner.enabled = true;
    this.scanner.marketPattern = (marketPattern || '').toLowerCase();
    this.scanner.pollIntervalMs = intervalMs || 5000;
    this.scanner.walletActivity = new Map();
    this.scanner.seenTradeIds = new Set();
    this.scanner.totalScanned = 0;
    this.scanner.errors = 0;

    this.log('info', `Market scanner started — "${marketPattern}" every ${this.scanner.pollIntervalMs / 1000}s`);

    // Immediate first poll
    this.scanMarket();
    this.scanner.interval = setInterval(() => this.scanMarket(), this.scanner.pollIntervalMs);
  }

  stopScanner() {
    if (this.scanner.interval) {
      clearInterval(this.scanner.interval);
      this.scanner.interval = null;
    }
    this.scanner.enabled = false;
    this.log('info', 'Market scanner stopped');
  }

  async scanMarket() {
    if (!this.scanner.enabled || !this.scanner.marketPattern) return;

    // Rate limit check — scanner uses 1 request per poll
    if (this.rateLimiter && !this.rateLimiter.consume('polymarket_data')) {
      return; // Skip this tick
    }

    try {
      // Use /trades — the /activity endpoint requires a user param (returns 400 without one)
      const r = await axios.get(`${DATA_API}/trades`, {
        params: { limit: 100 },
        timeout: 8000
      });

      if (this.rateLimiter) this.rateLimiter.clearBackoff('polymarket_data');
      this.scanner.lastPoll = new Date().toISOString();

      const trades = r.data || [];
      const pattern = this.scanner.marketPattern;

      // Filter to matching markets
      const matching = trades.filter(t => {
        const market = (t.title || t.question || t.market || '').toLowerCase();
        return market.includes(pattern);
      });

      // Dedup against already-seen trades
      const newTrades = matching.filter(t => {
        const id = t.transactionHash || `${t.proxyWallet}-${t.timestamp}-${t.price}`;
        if (this.scanner.seenTradeIds.has(id)) return false;
        this.scanner.seenTradeIds.add(id);
        return true;
      });

      // Cap the seen set to prevent memory growth
      if (this.scanner.seenTradeIds.size > 5000) {
        const arr = [...this.scanner.seenTradeIds];
        this.scanner.seenTradeIds = new Set(arr.slice(-3000));
      }

      // Aggregate wallet activity
      for (const trade of newTrades) {
        const addr = trade.proxyWallet;
        if (!addr) continue;

        this.scanner.totalScanned++;
        const existing = this.scanner.walletActivity.get(addr) || {
          address: addr,
          count: 0,
          totalSize: 0,
          sides: { buy: 0, sell: 0 },
          markets: new Set(),
          firstSeen: new Date().toISOString(),
          lastSeen: null
        };

        existing.count++;
        existing.totalSize += parseFloat(trade.amount || trade.size || trade.usdcSize || 0);
        existing.lastSeen = new Date().toISOString();

        const side = (trade.side || '').toUpperCase();
        if (side === 'BUY') existing.sides.buy++;
        else existing.sides.sell++;

        const marketName = trade.title || trade.question || trade.market || '';
        existing.markets.add(marketName.slice(0, 80));

        this.scanner.walletActivity.set(addr, existing);
      }

      if (newTrades.length > 0) {
        this.log('info', `Scanner: ${newTrades.length} new trades on "${pattern}" (${this.scanner.walletActivity.size} unique wallets)`);
      }

      this.scanner.errors = 0;
    } catch (e) {
      this.scanner.errors++;
      if (this.rateLimiter && e.response?.status === 429) {
        this.rateLimiter.reportRateLimit('polymarket_data');
      }
      this.log('warn', `Scanner poll failed`, { error: e.message, consecutive: this.scanner.errors });
    }
  }

  /**
   * Get the most active wallets found by the scanner, sorted by trade count.
   * These are your likely bots.
   */
  getScannerResults(minTrades = 2, limit = 50) {
    const results = [];
    for (const [addr, data] of this.scanner.walletActivity) {
      if (data.count >= minTrades) {
        results.push({
          address: addr,
          trades: data.count,
          totalSize: +data.totalSize.toFixed(2),
          avgSize: +(data.totalSize / data.count).toFixed(2),
          buyCount: data.sides.buy,
          sellCount: data.sides.sell,
          marketCount: data.markets.size,
          firstSeen: data.firstSeen,
          lastSeen: data.lastSeen,
          tradesPerMinute: data.count > 1
            ? +(data.count / ((new Date(data.lastSeen) - new Date(data.firstSeen)) / 60000)).toFixed(2)
            : 0
        });
      }
    }
    return results
      .sort((a, b) => b.trades - a.trades)
      .slice(0, limit);
  }

  /**
   * Auto-watch the top N most active wallets from the scanner.
   */
  watchTopScannerWallets(count = 3, autoCopy = false) {
    const top = this.getScannerResults(3, count);
    const added = [];
    for (const w of top) {
      if (!this.wallets.has(w.address)) {
        this.watch(w.address, `Bot ${w.address.slice(0, 8)}...`, {
          autoCopy,
          volume: w.totalSize,
          winRate: 0 // unknown until we track results
        });
        added.push({ address: w.address, trades: w.trades, tradesPerMinute: w.tradesPerMinute });
      }
    }
    this.log('info', `Auto-watched ${added.length} wallets from scanner results`);
    return added;
  }

  getScannerStatus() {
    return {
      enabled: this.scanner.enabled,
      marketPattern: this.scanner.marketPattern,
      pollIntervalMs: this.scanner.pollIntervalMs,
      uniqueWallets: this.scanner.walletActivity.size,
      totalTradesScanned: this.scanner.totalScanned,
      errors: this.scanner.errors,
      lastPoll: this.scanner.lastPoll,
      topWallets: this.getScannerResults(2, 10)
    };
  }

  // ═══════════════════════════════════════════════════════════════════
  //  STATUS
  // ═══════════════════════════════════════════════════════════════════

  getStatus() {
    return {
      running: this.running,
      walletsWatched: this.wallets.size,
      wallets: [...this.wallets.entries()].map(([addr, w]) => ({
        address: addr, name: w.name, winRate: w.winRate,
        autoCopy: w.autoCopy, errors: w.errors, paused: w.paused,
        recentResultCount: w.recentResults.length
      })),
      pollIntervalSeconds: this.pollIntervalMs / 1000,
      stats: this.stats,
      scanner: this.getScannerStatus()
    };
  }

  // ── Wallet persistence ──────────────────────────────────────────────

  persistWallets(db) {
    if (!db) db = this.db;
    if (!db) return;
    try {
      // GUARD: never overwrite saved wallets with empty list
      if (this.wallets.size === 0) {
        const existing = db.getSetting('monitor_wallets', null);
        if (existing && Array.isArray(existing) && existing.length > 0) {
          this.log('warn', 'Skipping persist — in-memory wallets empty but DB has ' + existing.length + ' saved');
          return;
        }
      }
      const serialized = [];
      for (const [addr, w] of this.wallets) {
        serialized.push({
          address: addr,
          name: w.name,
          winRate: w.winRate,
          volume: w.volume,
          estimatedPortfolio: w.estimatedPortfolio,
          minPositionAlert: w.minPositionAlert,
          autoCopy: w.autoCopy,
          paused: w.paused,
          lastPollTimestamp: w.lastPollTimestamp || 0
        });
      }
      db.setSetting('monitor_wallets', serialized);
    } catch (e) {
      this.log('warn', 'Failed to persist wallets: ' + e.message);
    }
  }

  restoreWallets(db) {
    if (!db) db = this.db;
    if (!db) return;
    try {
      const saved = db.getSetting('monitor_wallets', null);
      if (!saved || !Array.isArray(saved) || saved.length === 0) return;
      for (const w of saved) {
        if (!w.address || this.wallets.has(w.address)) continue;
        this.wallets.set(w.address, {
          name: w.name || w.address.slice(0, 8) + '...',
          lastSeenIds: new Set(),
          winRate: w.winRate || 0,
          volume: w.volume || 0,
          estimatedPortfolio: w.estimatedPortfolio || w.volume || 0,
          minPositionAlert: w.minPositionAlert || 1000,
          autoCopy: w.autoCopy || false,
          errors: 0,
          paused: w.paused || false,
          lastPollTimestamp: w.lastPollTimestamp || 0,
          recentResults: []
        });
      }
      this.log('info', `Restored ${saved.length} wallets from DB`);
    } catch (e) {
      this.log('warn', 'Failed to restore wallets: ' + e.message);
    }
  }

  // ── API anomaly detection ─────────────────────────────────────────

  _validateApiHealth(trades) {
    if (!trades || trades.length === 0) return;
    // Check for suspicious patterns: all prices at 0.5 or all zero volume
    const atDefault = trades.filter(t => Math.abs(parseFloat(t.price || 0.5) - 0.5) < 0.001).length;
    const zeroSize = trades.filter(t => (parseFloat(t.usdcSize || t.size || 0)) === 0).length;
    if (atDefault / trades.length > 0.5 || zeroSize / trades.length > 0.8) {
      this._apiAnomalyCount = (this._apiAnomalyCount || 0) + 1;
      if (this._apiAnomalyCount >= 2) {
        this.log('warn', 'API anomaly detected — market data appears corrupted. New positions halted.');
        this._apiAnomaly = true;
      }
    } else {
      this._apiAnomalyCount = 0;
      this._apiAnomaly = false;
    }
  }

  log(level, message, data) {
    console.log(`[Monitor] [${level}] ${message}`, data || '');
    if (this.db) { try { this.db.logEvent(level, '[Monitor] ' + message, data); } catch (e) {} }
  }
}

module.exports = WalletMonitor;
