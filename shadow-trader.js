/**
 * Shadow Trader — parallel dry-run A/B engine.
 * Mirrors live signals with different params (Kelly 0.30, confidence threshold 50).
 * Logs to shadow-audit.jsonl. Weekly comparison fires SHADOW_COMPARISON entries.
 * After 3 consecutive outperforming weeks (>=20 trades) auto-prompts param adoption.
 * Never touches CLOB. All errors are swallowed — never bubble to the live path.
 */
'use strict';

const fs   = require('fs');
const path = require('path');

const DEFAULTS = {
  kellyFraction: 0.30,       // live uses 0.25
  confidenceThreshold: 50,   // live uses 55
  maxBankrollPct: 0.08,
  enabled: true
};

class ShadowTrader {
  constructor({ db, signal, scheduler, notifier, dataDir }) {
    this.db        = db;
    this.signal    = signal;
    this.notifier  = notifier;
    this.dataDir   = dataDir;
    this._auditPath = path.join(dataDir, 'shadow-audit.jsonl');
    this._positions = [];
    this._weeklyStats = null;
    this._weeklyStatsCachedAt = 0;
    this._outperformStreak = db.getSetting('shadow_outperform_streak', 0) || 0;
    try {
      const saved = db.getSetting('shadow_positions', []);
      if (Array.isArray(saved)) this._positions = saved;
    } catch (_) {}
    this._log('info', 'ShadowTrader initialised');
  }

  // Called fire-and-forget from the live whale-buy callback.
  async evaluateShadow(walletTrade) {
    try {
      const cfg = this._cfg();
      if (!cfg.enabled) return;

      const trade  = walletTrade || {};
      const market = trade.market || trade.title || '';
      const side   = trade.side || 'YES';
      const price  = parseFloat(trade.price || 0);
      const wallet = trade.wallet_address || trade.proxyWallet || '';

      if (!market || !price || !wallet || price <= 0 || price >= 1) return;

      // Lightweight confidence from wallet tracker (7d win rate * 100)
      let confidence = 50;
      try {
        if (this.signal?.walletTracker) {
          const s = this.signal.walletTracker.getWalletStats(wallet, '7d');
          if (s && s.totalTrades >= 3) confidence = Math.round((s.winRate ?? 0) * 100);
        }
      } catch (_) {}

      if (confidence < cfg.confidenceThreshold) {
        this._audit({ type: 'shadow_skip', market, side, price, wallet,
          reason: `confidence ${confidence} < threshold ${cfg.confidenceThreshold}` });
        return;
      }

      // Fractional Kelly sizing
      const bankroll  = this.db.getSetting('risk_bankroll', 500);
      const p = Math.max(0.01, Math.min(0.99, confidence / 100));
      const b = (1 - price) / price;
      const f = Math.max(0, (p * b - (1 - p)) / b) * cfg.kellyFraction;
      const size = Math.max(0, parseFloat((bankroll * Math.min(f, cfg.maxBankrollPct)).toFixed(2)));

      if (size < 1) {
        this._audit({ type: 'shadow_skip', market, side, price, wallet,
          reason: `size ${size} below $1 minimum` });
        return;
      }

      // Exposure cap: keep shadow total notional under 50% of bankroll
      const exposure = this._positions.reduce((s, p) => s + p.size, 0);
      if (exposure + size > bankroll * 0.5) {
        this._audit({ type: 'shadow_skip', market, side, price, wallet,
          reason: 'shadow exposure cap reached' });
        return;
      }

      const pos = {
        id: `shd_${Date.now()}_${Math.random().toString(36).slice(2, 7)}`,
        market, side, price, size,
        openedAt: new Date().toISOString(),
        copied_from: wallet, confidence,
        kellyFraction: cfg.kellyFraction,
        source: 'shadow'
      };
      this._positions.push(pos);
      this._savePosDB();
      this._audit({ type: 'shadow_open', ...pos });
      this._log('info', `Shadow opened: ${market} ${side} @${price} size=${size}`);

    } catch (err) {
      this._log('warn', 'evaluateShadow suppressed: ' + err.message);
    }
  }

  // Record resolution outcome for an open shadow position.
  recordOutcome(market, pnl) {
    try {
      const idx = this._positions.findIndex(
        p => (p.market || '').toLowerCase() === (market || '').toLowerCase());
      if (idx === -1) return;
      const pos = this._positions.splice(idx, 1)[0];
      this._savePosDB();

      const stats = this._stats();
      const wk = this._weekKey();
      if (!stats[wk]) stats[wk] = { shadowPnl: 0, shadowTrades: 0, livePnl: 0, liveTrades: 0 };
      stats[wk].shadowPnl    += pnl;
      stats[wk].shadowTrades += 1;
      this._saveStats(stats);
      this._audit({ type: 'shadow_close', market, pnl, positionId: pos.id });
    } catch (err) {
      this._log('warn', 'recordOutcome suppressed: ' + err.message);
    }
  }

  // Weekly scheduled job — compare shadow vs live, emit SHADOW_COMPARISON entry.
  async comparePerformance() {
    try {
      const stats = this._stats();
      const weeks = Object.keys(stats).sort();
      if (!weeks.length) { this._log('info', 'Shadow: no weekly data yet'); return; }

      const wk = weeks[weeks.length - 1];
      const w  = stats[wk];
      const summary = {
        tag: 'SHADOW_COMPARISON', week: wk,
        shadowPnl: +(w.shadowPnl || 0).toFixed(2), shadowTrades: w.shadowTrades || 0,
        livePnl:   +(w.livePnl   || 0).toFixed(2), liveTrades:   w.liveTrades   || 0,
        shadowWon: (w.shadowPnl || 0) > (w.livePnl || 0),
        generatedAt: new Date().toISOString()
      };

      this._audit({ type: 'SHADOW_COMPARISON', ...summary });
      this._log('info', 'Shadow comparison logged', summary);

      if (summary.shadowWon && summary.shadowTrades >= 20) {
        this._outperformStreak++;
      } else {
        this._outperformStreak = 0;
      }
      this.db.setSetting('shadow_outperform_streak', this._outperformStreak);
      this._checkAutoPromote(summary);

    } catch (err) {
      this._log('warn', 'comparePerformance suppressed: ' + err.message);
    }
  }

  // Returns summary object for GET /api/shadow/performance.
  getStatus() {
    try {
      const cfg   = this._cfg();
      const stats = this._stats();
      return {
        enabled: cfg.enabled, config: cfg,
        openPositions: this._positions.length,
        openExposure: +this._positions.reduce((s, p) => s + p.size, 0).toFixed(2),
        outperformStreak: this._outperformStreak,
        weeklyHistory: Object.keys(stats).sort().map(wk => ({ week: wk, ...stats[wk] })),
        auditPath: this._auditPath
      };
    } catch (_) { return { enabled: false, error: 'status unavailable' }; }
  }

  // ── Private ────────────────────────────────────────────────────────────

  _checkAutoPromote(summary) {
    if (this._outperformStreak < 3) return;
    const cfg = this._cfg();
    this.db.setSetting('shadow_promote_pending', {
      detectedAt: new Date().toISOString(),
      weeks: this._outperformStreak,
      proposedConfig: cfg,
      latestWeekSummary: summary
    });
    const msg = `Shadow has outperformed live for ${this._outperformStreak} weeks `
      + `(shadow $${summary.shadowPnl} vs live $${summary.livePnl}). `
      + `POST /api/shadow/promote to adopt params (Kelly ${cfg.kellyFraction}, `
      + `confidence threshold ${cfg.confidenceThreshold}).`;
    try { this.notifier?.send('Shadow trader ready to promote', msg, { type: 'info' }); } catch (_) {}
    this._audit({ type: 'shadow_promote_suggested', streak: this._outperformStreak, summary });
    this._log('info', 'Auto-promote flagged', { streak: this._outperformStreak });
  }

  _cfg() {
    try { return Object.assign({}, DEFAULTS, this.db.getSetting('shadow_config', {})); }
    catch (_) { return { ...DEFAULTS }; }
  }

  _stats() {
    const CACHE_TTL = 5 * 60 * 1000; // 5 minutes
    if (this._weeklyStats && (Date.now() - this._weeklyStatsCachedAt) < CACHE_TTL) return this._weeklyStats;
    try {
      const v = this.db.getSetting('shadow_weekly_stats', {});
      this._weeklyStats = (v && typeof v === 'object' && !Array.isArray(v)) ? v : {};
    } catch (_) { this._weeklyStats = {}; }
    this._weeklyStatsCachedAt = Date.now();
    return this._weeklyStats;
  }

  _saveStats(s) { this._weeklyStats = s; try { this.db.setSetting('shadow_weekly_stats', s); } catch (_) {} }
  _savePosDB()  { try { this.db.setSetting('shadow_positions', this._positions); } catch (_) {} }

  _weekKey() {
    const n = new Date();
    // ISO week number using UTC to avoid timezone drift
    const d = new Date(Date.UTC(n.getUTCFullYear(), n.getUTCMonth(), n.getUTCDate()));
    d.setUTCDate(d.getUTCDate() + 4 - (d.getUTCDay() || 7));
    const yearStart = new Date(Date.UTC(d.getUTCFullYear(), 0, 1));
    const wk = Math.ceil(((d - yearStart) / 86400000 + 1) / 7);
    return `${d.getUTCFullYear()}-W${String(wk).padStart(2, '0')}`;
  }

  _audit(obj) {
    try {
      fs.appendFile(this._auditPath, JSON.stringify({ ts: new Date().toISOString(), ...obj }) + '\n', 'utf8', (err) => {
        if (err) this._log('warn', 'audit write failed: ' + err.message);
      });
    } catch (_) {}
  }

  _log(level, msg, data) {
    const fn = (level === 'warn' || level === 'error') ? console.error : console.log;
    fn('[ShadowTrader]', msg, data || '');
  }
}

module.exports = ShadowTrader;
