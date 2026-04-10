/**
 * Market Maker — Liquidity Provision + Maker Rebate Capture
 *
 * Posts symmetric bid/ask orders around midpoint on liquid crypto markets.
 * Earns 20% maker rebate on crypto markets (Polymarket reward program).
 *
 * Safety caps: $50/market, $200 total MM exposure.
 * Requires CLOB client for order placement + WebSocket for real-time quotes.
 *
 * Disabled by default. Enable via: mm_enabled = true.
 */
'use strict';

const axios = require('axios');
const GAMMA = 'https://gamma-api.polymarket.com';

class MarketMaker {
  constructor({ db, clob, risk, audit, ws, log } = {}) {
    this.db = db;
    this.clob = clob;
    this.risk = risk;
    this.audit = audit;
    this.ws = ws; // WebSocket module for real-time prices
    this._log = log || ((level, msg) => console.log(`[MarketMaker] [${level}] ${msg}`));

    // Active quotes: conditionId -> { yesOrderId, noOrderId, midpoint, spread, size, tokenIds }
    this._activeQuotes = new Map();

    this._quoteTimer = null;
    this._running = false;

    this._stats = {
      quotesPlaced: 0,
      quotesCancelled: 0,
      fillsReceived: 0,
      totalRebates: 0,
      lastQuote: null
    };
  }

  getConfig() {
    return {
      enabled:       this.db?.getSetting('mm_enabled', false),
      maxPerMarket:  this.db?.getSetting('mm_maxPerMarket', 50),
      maxTotal:      this.db?.getSetting('mm_maxTotal', 200),
      spreadPct:     this.db?.getSetting('mm_spreadPct', 3),     // initial 3% spread
      minSpreadPct:  this.db?.getSetting('mm_minSpreadPct', 1),  // tighten to 1%
      quoteIntervalMs: this.db?.getSetting('mm_quoteIntervalMs', 30000), // re-quote every 30s
      minVolume:     this.db?.getSetting('mm_minVolume', 500),   // min daily volume to MM
      maxMarkets:    this.db?.getSetting('mm_maxMarkets', 3)     // max markets to MM simultaneously
    };
  }

  start() {
    const cfg = this.getConfig();
    if (!cfg.enabled) {
      this._log('info', 'Market maker disabled (set mm_enabled=true to activate)');
      return;
    }
    if (!this.clob?.isReady()) {
      this._log('warn', 'Market maker enabled but CLOB not ready — will retry on next quote cycle');
    }

    this._running = true;
    this._log('info', `Market maker started (spread ${cfg.spreadPct}%, max $${cfg.maxTotal} total, quote every ${cfg.quoteIntervalMs/1000}s)`);

    this._quoteTimer = setInterval(() => this._quoteCycle(), cfg.quoteIntervalMs);
    // First cycle after short delay
    setTimeout(() => this._quoteCycle(), 5000);
  }

  stop() {
    this._running = false;
    if (this._quoteTimer) { clearInterval(this._quoteTimer); this._quoteTimer = null; }
    // Cancel all outstanding quotes
    this._cancelAllQuotes();
    this._log('info', 'Market maker stopped');
  }

  getStats() {
    return {
      ...this._stats,
      running: this._running,
      activeQuotes: this._activeQuotes.size,
      totalExposure: this._getTotalExposure()
    };
  }

  // ── Quote cycle ─────────────────────────────────────────────────────

  async _quoteCycle() {
    if (!this._running || !this.clob?.isReady()) return;
    const cfg = this.getConfig();
    if (!cfg.enabled) return;

    try {
      // Cancel stale quotes
      await this._cancelAllQuotes();

      // Find liquid crypto markets
      const markets = await this._findMMMarkets(cfg);

      const totalExposure = this._getTotalExposure();
      let placed = 0;

      for (const mkt of markets) {
        if (placed >= cfg.maxMarkets) break;
        if (totalExposure + cfg.maxPerMarket > cfg.maxTotal) break;

        await this._placeQuotes(mkt, cfg);
        placed++;
      }

      this._stats.lastQuote = new Date().toISOString();
    } catch (e) {
      this._log('warn', `Quote cycle error: ${e.message}`);
    }
  }

  async _findMMMarkets(cfg) {
    try {
      const r = await axios.get(`${GAMMA}/markets`, {
        params: { active: true, limit: 50, closed: false },
        timeout: 8000
      });
      const data = Array.isArray(r.data) ? r.data : (r.data?.data || []);

      return data
        .filter(m => m && !m.resolved && !m.negRisk)
        .filter(m => /bitcoin|btc|ethereum|eth|solana|sol|crypto/i.test(m.question || m.title || ''))
        .filter(m => {
          const vol = parseFloat(m.volume) || parseFloat(m.volumeNum) || 0;
          return vol >= cfg.minVolume;
        })
        .slice(0, cfg.maxMarkets);
    } catch (e) {
      return [];
    }
  }

  async _placeQuotes(mkt, cfg) {
    const condId = mkt.condition_id || mkt.conditionId;
    if (!condId) return;

    try {
      const tokenIds = await this.clob.resolveTokenIds(mkt.question || mkt.title || '');
      if (!tokenIds?.yesTokenId || !tokenIds?.noTokenId) return;

      // Get midpoint
      const mid = await this.clob.getMidpoint(tokenIds.yesTokenId);
      if (!mid || mid <= 0.05 || mid >= 0.95) return; // avoid extreme prices

      const spreadHalf = (cfg.spreadPct / 100) / 2;
      const bidPrice = +(mid - spreadHalf).toFixed(4);
      const askPrice = +(mid + spreadHalf).toFixed(4);

      if (bidPrice <= 0.01 || askPrice >= 0.99) return;

      const sizeUSD = Math.min(cfg.maxPerMarket / 2, 25); // per side
      const bidShares = Math.floor(sizeUSD / bidPrice);
      const askShares = Math.floor(sizeUSD / askPrice);

      if (bidShares < 1 || askShares < 1) return;

      const isDry = this.risk?.getConfig?.()?.dryRun !== false;
      const label = (mkt.question || mkt.title || '').slice(0, 60);

      if (isDry) {
        this._log('info', `[DRY] MM quote: ${label} | bid $${bidPrice} (${bidShares}sh) / ask $${askPrice} (${askShares}sh)`);
        this._stats.quotesPlaced += 2;
      } else {
        // Place bid (buy YES at bidPrice) and ask (sell YES at askPrice)
        const bidResult = await this.clob.placeOrder(tokenIds.yesTokenId, 'BUY', bidPrice, bidShares);
        const askResult = await this.clob.placeOrder(tokenIds.yesTokenId, 'SELL', askPrice, askShares);

        if (bidResult?.success || askResult?.success) {
          this._activeQuotes.set(condId, {
            yesOrderId: bidResult?.orderId, noOrderId: askResult?.orderId,
            midpoint: mid, bidPrice, askPrice, sizeUSD,
            tokenIds, market: label
          });
          this._stats.quotesPlaced += 2;
          this._log('info', `MM quoted: ${label} | bid $${bidPrice} / ask $${askPrice}`);
        }
      }

      if (this.audit) {
        try {
          this.audit.record('MM_QUOTE', {
            market: label, conditionId: condId,
            midpoint: mid, bidPrice, askPrice,
            bidShares, askShares, sizeUSD, dryRun: isDry
          });
        } catch (_) {}
      }
    } catch (e) {
      this._log('warn', `Failed to place quotes on ${condId}: ${e.message}`);
    }
  }

  async _cancelAllQuotes() {
    for (const [condId, quote] of this._activeQuotes) {
      try {
        if (quote.yesOrderId) await this.clob.cancelOrder?.(quote.yesOrderId);
        if (quote.noOrderId) await this.clob.cancelOrder?.(quote.noOrderId);
        this._stats.quotesCancelled += 2;
      } catch (_) {}
    }
    this._activeQuotes.clear();
  }

  _getTotalExposure() {
    let total = 0;
    for (const q of this._activeQuotes.values()) {
      total += (q.sizeUSD || 0) * 2; // both sides
    }
    return total;
  }
}

module.exports = MarketMaker;
