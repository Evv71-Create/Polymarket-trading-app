/**
 * Database module — JSON file storage
 * Fixes: debounced saves, sensitive key filtering, risk state persistence,
 *        capped query limits, public settings whitelist
 */

const path = require('path');
const fs = require('fs');

// Always use project data/ folder — single DB for both Electron and CLI
const DATA_DIR = path.join(__dirname, 'data');

if (!fs.existsSync(DATA_DIR)) fs.mkdirSync(DATA_DIR, { recursive: true });
const DB_PATH = path.join(DATA_DIR, 'polymarket.json');

const SENSITIVE_KEYS = [
  'polymarket_api_key', 'telegram_token', 'telegram_chatId',
  'api_secret', 'private_key', 'news_llmApiKey', 'polymarket_passphrase'
];

const PUBLIC_WRITABLE_KEYS = [
  'risk_maxDailyLoss', 'risk_maxTradeSize', 'risk_maxOpenPositions',
  'risk_maxExposurePct', 'risk_drawdownPausePct', 'risk_minWinRateCopy',
  'risk_minVolumeCopy', 'risk_maxSlippagePct', 'risk_bankroll', 'risk_enabled',
  'risk_stopLossPct', 'risk_takeProfitPct', 'risk_trailingStopPct',
  'risk_maxMarketExposure', 'risk_dryRun',
  'signal_minOriginalSize', 'signal_minWinRate', 'signal_maxCopySize',
  'signal_copyRatio', 'signal_copyDelayMs', 'signal_minPrice',
  'signal_maxPrice', 'signal_allowedCategories',
  'signal_sizingMode', 'signal_minConvictionPct', 'signal_maxConvictionPct',
  'signal_maxBankrollPct',
  'signal_minMarketDurationMinutes', 'signal_maxMarketDurationMinutes',
  'scheduler_autoStart', 'scheduler_autoWatchTop', 'scheduler_autoCopy',
  'scheduler_maxAutoWatchWallets', 'scheduler_autoActivateTop', 'scheduler_marketFilter',
  'notif_sound', 'notif_desktop', 'notif_inApp',
  'monitor_decayWindowDays', 'monitor_decayMinTrades', 'monitor_decayThresholdPct',
  'news_enabled', 'news_maxCallsPerDay', 'news_minDivergence', 'news_pollIntervalMs',
  'news_maxTradeSize', 'news_llmModel', 'news_gnewsApiKey', 'news_newsapiKey',
  'mm_enabled', 'mm_maxPerMarket', 'mm_maxTotal', 'mm_spreadPct',
  'external_signals_enabled',
  'live_strategies',
  'updown_enabled', 'updown_minSize', 'updown_maxSize',
  'updown_minMagnitudePct', 'updown_maxEntryPrice',
  'updown_minMinutesLeft', 'updown_maxMinutesLeft',
  'updown_scanIntervalMs', 'updown_maxConcurrentPositions',
  'updown_liveExcludedAssets', 'updown_autoDisabledAssets',
  'updown_enabledWindows', 'updown_maxMinutesLeftByWindow', 'updown_sizingMultiplierByWindow',
  'arb_enabled', 'arb_maxConcurrentPositions', 'arb_maxResolutionArbSize',
  'arb_minResolutionEdge',
  'weather_enabled', 'weather_minEdge', 'weather_maxTradeSize', 'weather_kellyFraction',
  'weather_ensembleIntervalMs', 'weather_hrrrIntervalMs', 'weather_maxConcurrentPositions',
  'weather_hrrrLateWindowHours', 'weather_minMarketPrice', 'weather_hrrrMinEdge',
  'weather_cities'
];

let _data = null;
let _saveTimer = null;
const SAVE_DEBOUNCE_MS = 500;
// .bak is a rolling backup; updating it on EVERY save copies the full
// 3MB+ DB file synchronously and blocks the event loop. Throttle to at
// most once per BAK_INTERVAL_MS — atomic rename in saveImmediate already
// guarantees durability of the primary file.
const BAK_INTERVAL_MS = 60_000;
let _lastBakAt = 0;

function load() {
  if (_data) return _data;
  try {
    if (fs.existsSync(DB_PATH)) {
      _data = JSON.parse(fs.readFileSync(DB_PATH, 'utf8'));
    }
  } catch (e) {
    console.error('[DB] Load error on primary file:', e.message);
    // Primary file is corrupt — attempt recovery from .bak
    const bakPath = DB_PATH + '.bak';
    if (fs.existsSync(bakPath)) {
      try {
        _data = JSON.parse(fs.readFileSync(bakPath, 'utf8'));
        console.error('[DB] Recovered from .bak — restoring primary file');
        fs.copyFileSync(bakPath, DB_PATH);
      } catch (e2) {
        console.error('[DB] .bak recovery also failed:', e2.message);
      }
    }
  }

  _data = _data || {};
  _data.settings  = _data.settings  || {};
  _data.watchlist = _data.watchlist || [];
  _data.pinned    = _data.pinned    || [];
  _data.trades    = _data.trades    || [];
  _data.snapshots = _data.snapshots || [];
  _data.activity  = _data.activity  || [];
  _data.events    = _data.events    || [];
  _data.riskState = _data.riskState || null;
  _data.journal   = _data.journal   || [];
  _data._nextId   = _data._nextId   || 1;
  return _data;
}

function saveImmediate() {
  try {
    const tmpPath = DB_PATH + '.tmp';
    const serialized = JSON.stringify(_data, null, 2);

    // Sanity-check: refuse to write if the result is suspiciously small
    // (guards against in-memory state being partially reset before flush)
    if (serialized.length < 200) {
      console.error('[DB] Save aborted — serialized data suspiciously small (' + serialized.length + ' bytes), possible state corruption');
      return;
    }

    // Throttled rolling backup: copy DB→.bak at most once every BAK_INTERVAL_MS.
    // Writing .bak on every save was a major source of event-loop blocking when
    // updown signals fire many times per cycle (3MB sync copy each time).
    const nowMs = Date.now();
    if (nowMs - _lastBakAt > BAK_INTERVAL_MS && fs.existsSync(DB_PATH)) {
      try {
        fs.copyFileSync(DB_PATH, DB_PATH + '.bak');
        _lastBakAt = nowMs;
      } catch (_) {}
    }

    // Atomic write: tmp → rename. Atomic rename guarantees the primary file
    // is either fully updated or unchanged, so the previous round-trip
    // re-read+parse validation step (which doubled save latency by re-reading
    // the entire 3MB file) is redundant given JSON.stringify can't produce
    // invalid JSON for plain object data.
    fs.writeFileSync(tmpPath, serialized);
    fs.renameSync(tmpPath, DB_PATH);
  }
  catch (e) { console.error('[DB] Save error:', e.message); }
}

function save() {
  if (_saveTimer) clearTimeout(_saveTimer);
  _saveTimer = setTimeout(() => { _saveTimer = null; saveImmediate(); }, SAVE_DEBOUNCE_MS);
}

function flushSync() {
  if (_saveTimer) { clearTimeout(_saveTimer); _saveTimer = null; }
  if (_data) saveImmediate();
}

function nextId() { const id = load()._nextId++; save(); return id; }

// ── Settings ───────────────────────────────────────────────────────────

function getSetting(key, defaultValue = null) {
  const v = load().settings[key];
  return v !== undefined ? v : defaultValue;
}

function setSetting(key, value) {
  load().settings[key] = value;
  save();
  return true;
}

function setPublicSetting(key, value) {
  if (!PUBLIC_WRITABLE_KEYS.includes(key)) {
    return { success: false, error: `Setting '${key}' is not writable via API` };
  }
  setSetting(key, value);
  return { success: true };
}

function getAllSettings() {
  const all = { ...load().settings };
  for (const key of SENSITIVE_KEYS) {
    if (key in all) all[key] = '••••••••';
  }
  return all;
}

function getSettingInternal(key, defaultValue = null) {
  return getSetting(key, defaultValue);
}

// Internal write that bypasses the PUBLIC_WRITABLE_KEYS whitelist enforced by
// setPublicSetting. Callers (server.js credential endpoint, clob.js credential
// derivation) enforce their own per-call key whitelists.
function setSettingInternal(key, value) {
  return setSetting(key, value);
}

// ── Risk State Persistence ─────────────────────────────────────────────

function saveRiskState(state) {
  load().riskState = {
    dailyPnL: state.dailyPnL,
    sessionPnL: state.sessionPnL,
    openPositions: state.openPositions,
    paused: state.paused,
    pauseReason: state.pauseReason,
    lastReset: state.lastReset,
    consecutiveLosses: state.consecutiveLosses || 0,
    circuitBreakerUntil: state.circuitBreakerUntil || null,
    peakEquity: state.peakEquity || 0,
    maxDrawdownHit: state.maxDrawdownHit || 0,
    strategyResults: state.strategyResults || {},
    strategyHistory: state.strategyHistory || {},
    systemWinStreak: state.systemWinStreak || 0,
    directionHeat: state.directionHeat || {},
    sessionNotional: state.sessionNotional || 0,
    savedAt: new Date().toISOString()
  };
  save();
}

function loadRiskState() {
  const s = load().riskState;
  if (!s) return null;
  if (s.lastReset === new Date().toISOString().slice(0, 10)) return s;
  // New day: reset daily PnL but preserve circuit breaker if still active
  const cbUntil = s.circuitBreakerUntil ? new Date(s.circuitBreakerUntil) : null;
  const stillInCB = cbUntil && cbUntil > new Date();
  return {
    dailyPnL: 0, sessionPnL: s.sessionPnL || 0,
    openPositions: s.openPositions || [],
    paused: stillInCB ? true : false,
    pauseReason: stillInCB ? s.pauseReason : null,
    lastReset: new Date().toISOString().slice(0, 10), savedAt: s.savedAt,
    consecutiveLosses: 0, // Reset on new day — stale loss streaks shouldn't block fresh trades
    circuitBreakerUntil: stillInCB ? s.circuitBreakerUntil : null
  };
}

// ── Watchlist ──────────────────────────────────────────────────────────

function getWatchlist() { return [...load().watchlist]; }

function addToWatchlist(trader) {
  const d = load();
  const idx = d.watchlist.findIndex(t => t.id === trader.id);
  const entry = {
    id: trader.id, name: trader.name, address: trader.address || trader.addr,
    roi: trader.roi, win_rate: trader.win_rate || trader.wr,
    volume: trader.volume || trader.vol,
    trades: trader.trades || 0, tag: trader.tag,
    color: trader.color || trader.c || 'ca',
    note: trader.note, is_verified: trader.is_verified ? 1 : 0,
    added_at: new Date().toISOString()
  };
  if (idx >= 0) d.watchlist[idx] = entry; else d.watchlist.push(entry);
  save();
  return { success: true };
}

function updateWatchlistTrader(id, updates) {
  const d = load();
  const idx = d.watchlist.findIndex(t => String(t.id) === String(id));
  if (idx >= 0) { Object.assign(d.watchlist[idx], updates); save(); return { success: true }; }
  return { success: false, error: 'Not found' };
}

function removeFromWatchlist(id) {
  const d = load();
  d.watchlist = d.watchlist.filter(t => String(t.id) !== String(id));
  save();
  return { success: true };
}

// ── Pinned markets ─────────────────────────────────────────────────────

function getPinnedMarkets() { return [...load().pinned]; }

function addPinnedMarket(pin) {
  const d = load();
  d.pinned.push({ id: pin.id, market: pin.market, side: pin.side, reason: pin.reason || '', pinned_at: new Date().toISOString() });
  save();
  return { success: true };
}

function removePinnedMarket(id) {
  const d = load();
  d.pinned = d.pinned.filter(p => String(p.id) !== String(id));
  save();
  return { success: true };
}

// ── Trade history ──────────────────────────────────────────────────────

function logTrade(trade) {
  const id = nextId();
  const entry = {
    id, market: trade.market, side: trade.side, price: trade.price,
    size: trade.size, copied_from: trade.copied_from,
    status: trade.status || 'queued', dry_run: trade.dry_run || false,
    stop_loss: trade.stop_loss || null, take_profit: trade.take_profit || null,
    pnl: null, executed_at: new Date().toISOString()
  };
  load().trades.push(entry);
  if (_data.trades.length > 2000) _data.trades = _data.trades.slice(-2000);
  saveImmediate(); // trades are financial state — don't debounce
  return { success: true, id };
}

function updateTrade(id, updates) {
  const d = load();
  const idx = d.trades.findIndex(t => t.id === id);
  if (idx >= 0) { Object.assign(d.trades[idx], updates); save(); return { success: true }; }
  return { success: false };
}

function getTradeHistory(limit = 50) {
  return load().trades.slice(-Math.min(Math.max(1, limit), 500)).reverse();
}

// Returns the full trade table (uncapped). Use for aggregate stats —
// getTradeHistory's 500-row cap silently truncates 7d/all-time numbers.
function getAllTrades() {
  return load().trades.slice();
}

function getTradeStats() {
  // Include paper/dry-run trades — app operates primarily in paper mode
  const closed = load().trades.filter(t => (t.status === 'closed' || t.status === 'won' || t.status === 'lost') && t.pnl !== null);
  if (!closed.length) return { total: 0, wins: 0, losses: 0, total_pnl: 0, avg_pnl: 0, best_trade: 0, worst_trade: 0, win_rate: 0 };
  const pnls = closed.map(t => t.pnl);
  const wins = pnls.filter(p => p > 0).length;
  const total_pnl = pnls.reduce((s, p) => s + p, 0);
  return {
    total: closed.length, wins, losses: closed.length - wins,
    total_pnl: +total_pnl.toFixed(2), avg_pnl: +(total_pnl / closed.length).toFixed(2),
    best_trade: Math.max(...pnls), worst_trade: Math.min(...pnls),
    win_rate: +((wins / closed.length) * 100).toFixed(1)
  };
}

// ── Wallet snapshots ───────────────────────────────────────────────────

function saveWalletSnapshot(wallet) {
  load().snapshots.push({ ...wallet, snapshot_at: new Date().toISOString() });
  if (_data.snapshots.length > 500) _data.snapshots = _data.snapshots.slice(-500);
  save();
  return { success: true };
}

function getWalletHistory(address, days = 30) {
  const since = new Date(Date.now() - days * 86400000).toISOString();
  return load().snapshots.filter(s => s.address === address && s.snapshot_at >= since);
}

// ── Wallet activity ────────────────────────────────────────────────────

function logWalletActivity(activity) {
  load().activity.push({ ...activity, detected_at: new Date().toISOString() });
  if (_data.activity.length > 500) _data.activity = _data.activity.slice(-500);
  save();
  return { success: true };
}

function getRecentActivity(walletAddress, limit = 20) {
  const capped = Math.min(Math.max(1, limit), 200);
  const all = load().activity;
  const filtered = walletAddress ? all.filter(a => a.wallet_address === walletAddress) : all;
  return filtered.slice(-capped).reverse();
}

// ── Event log ──────────────────────────────────────────────────────────

function logEvent(level, message, data) {
  try {
    load().events.push({ level, message, data: data ? JSON.stringify(data).slice(0, 500) : null, logged_at: new Date().toISOString() });
    if (_data.events.length > 1000) _data.events = _data.events.slice(-1000);
    // Event log is an in-memory ring buffer for the UI log viewer; losing the
    // last few minutes of logs on crash is acceptable. The previous save() call
    // here triggered a debounced 3MB JSON.stringify+write on every log line and
    // was a major contributor to event-loop blocking under heavy log volume.
    // Events still get persisted whenever any other db.save call happens to fire.
  } catch (e) {}
}

// ── Trade journal ──────────────────────────────────────────────────────

function logJournalEntry(entry) {
  load().journal.push({ ...entry, logged_at: new Date().toISOString() });
  if (_data.journal.length > 500) _data.journal = _data.journal.slice(-500);
  save();
}

function getJournal(limit = 50) {
  return load().journal.slice(-Math.min(Math.max(1, limit), 500)).reverse();
}

function getEventLog(limit = 100, level = null) {
  const capped = Math.min(Math.max(1, limit), 1000);
  const events = load().events;
  const filtered = level ? events.filter(e => e.level === level) : events;
  return filtered.slice(-capped).reverse();
}

// ── DB shim for analytics ──────────────────────────────────────────────

function getDB() {
  return {
    prepare: (sql) => ({
      get: (...args) => analyticsQuery(sql, args, 'get'),
      all: (...args) => analyticsQuery(sql, args, 'all'),
      run: (...args) => { save(); return { lastInsertRowid: nextId() }; }
    }),
    exec: () => {},
    pragma: () => {}
  };
}

function analyticsQuery(sql, args, mode) {
  const d = load();
  const sqlL = sql.toLowerCase().trim();
  // Extract days filter from SQL (e.g., "-7 days")
  const _daysMatch = sql.match(/-(\d+)\s+days/);
  const _filterDays = _daysMatch ? parseInt(_daysMatch[1]) : 9999;
  const _sinceDate = new Date(Date.now() - _filterDays * 86400000).toISOString();
  try {
    if (sqlL.includes('from trade_history') && sqlL.includes('sum(pnl)')) {
      if (mode === 'get') {
        // Map getTradeStats fields to analytics expected field names, with days filter
        const filtered = d.trades.filter(t => (t.status === 'closed' || t.status === 'won' || t.status === 'lost') && t.pnl !== null && t.executed_at >= _sinceDate);
        if (!filtered.length) return { totalTrades: 0, wins: 0, losses: 0, pending: 0, totalPnL: 0, avgPnL: 0, bestTrade: 0, worstTrade: 0, totalVolume: 0 };
        const pnls = filtered.map(t => t.pnl);
        const wins = pnls.filter(p => p > 0).length;
        const total_pnl = pnls.reduce((s, p) => s + p, 0);
        return {
          totalTrades: filtered.length, wins, losses: filtered.length - wins,
          pending: 0, totalPnL: +total_pnl.toFixed(2), avgPnL: +(total_pnl / filtered.length).toFixed(2),
          bestTrade: pnls.reduce((a, b) => Math.max(a, b), -Infinity),
          worstTrade: pnls.reduce((a, b) => Math.min(a, b), Infinity),
          totalVolume: +filtered.reduce((s, t) => s + (parseFloat(t.size) || 0), 0).toFixed(2)
        };
      }
      return d.trades.filter(t => t.pnl !== null && !t.dry_run && t.executed_at >= _sinceDate);
    }
    if (sqlL.includes('from wallet_snapshots') && sqlL.includes('group by address')) {
      const groups = {};
      d.snapshots.forEach(s => {
        if (!groups[s.address]) groups[s.address] = { address: s.address, name: s.name, rois: [], wrs: [], count: 0 };
        groups[s.address].rois.push(s.roi || 0);
        groups[s.address].wrs.push(s.win_rate || 0);
        groups[s.address].count++;
      });
      return Object.values(groups).map(g => ({
        address: g.address, name: g.name,
        avgRoi: +(g.rois.reduce((a, b) => a + b, 0) / g.rois.length).toFixed(1),
        avgWinRate: +(g.wrs.reduce((a, b) => a + b, 0) / g.wrs.length).toFixed(1),
        snapshots: g.count
      })).sort((a, b) => b.avgWinRate - a.avgWinRate).slice(0, 20);
    }
    if (sqlL.includes('copied_from as wallet') && sqlL.includes('group by copied_from')) {
      const groups = {};
      d.trades.filter(t => t.copied_from && t.pnl !== null && !t.dry_run).forEach(t => {
        if (!groups[t.copied_from]) groups[t.copied_from] = { wallet: t.copied_from, trades: 0, wins: 0, pnl: 0 };
        groups[t.copied_from].trades++;
        if (t.pnl > 0) groups[t.copied_from].wins++;
        groups[t.copied_from].pnl += t.pnl;
      });
      return Object.values(groups).map(g => ({
        ...g, totalPnL: +g.pnl.toFixed(2), avgPnL: +(g.pnl / g.trades).toFixed(2),
        winRate: +((g.wins / g.trades) * 100).toFixed(1)
      })).sort((a, b) => b.totalPnL - a.totalPnL);
    }
    if (sqlL.includes('date(executed_at)') && sqlL.includes('group by day')) {
      const groups = {};
      d.trades.filter(t => t.pnl !== null && !t.dry_run).forEach(t => {
        const day = t.executed_at.slice(0, 10);
        if (!groups[day]) groups[day] = { day, dayPnL: 0 };
        groups[day].dayPnL += t.pnl;
      });
      return Object.values(groups).map(g => ({ ...g, dayPnL: +g.dayPnL.toFixed(2) })).sort((a, b) => a.day.localeCompare(b.day));
    }
    if (sqlL.includes('strftime') && sqlL.includes('group by hour')) {
      const groups = {};
      d.trades.filter(t => t.pnl !== null && !t.dry_run).forEach(t => {
        const hour = new Date(t.executed_at).getHours();
        if (!groups[hour]) groups[hour] = { hour, trades: 0, wins: 0, totalPnL: 0 };
        groups[hour].trades++;
        if (t.pnl > 0) groups[hour].wins++;
        groups[hour].totalPnL += t.pnl;
      });
      return Object.values(groups).map(g => ({ ...g, totalPnL: +g.totalPnL.toFixed(2) })).sort((a, b) => a.hour - b.hour);
    }
  } catch (e) { console.error('[DB shim] Query error:', e.message); }
  return mode === 'get' ? null : [];
}

function getDBInfo() {
  const d = load();
  return {
    path: DB_PATH, dataDir: DATA_DIR,
    tables: {
      settings: Object.keys(d.settings).length, watchlist: d.watchlist.length,
      pinned: d.pinned.length, trades: d.trades.length,
      snapshots: d.snapshots.length, activity: d.activity.length, events: d.events.length
    }
  };
}

// ── DB backup rotation ──────────────────────────────────────────────────
let _backupInterval = null;

function startBackupRotation(intervalMs = 60 * 60 * 1000, maxBackups = 24) {
  if (_backupInterval) return;
  const backupDir = path.join(DATA_DIR, 'backups');
  if (!fs.existsSync(backupDir)) fs.mkdirSync(backupDir, { recursive: true });

  const doBackup = () => {
    try {
      const ts = new Date().toISOString().replace(/[:.]/g, '-');
      const backupPath = path.join(backupDir, `polymarket_${ts}.json`);
      if (_data) fs.writeFileSync(backupPath, JSON.stringify(_data, null, 2));

      // Prune old backups
      const files = fs.readdirSync(backupDir)
        .filter(f => f.startsWith('polymarket_') && f.endsWith('.json'))
        .sort()
        .reverse();
      for (const old of files.slice(maxBackups)) {
        try { fs.unlinkSync(path.join(backupDir, old)); } catch (e) {}
      }
    } catch (e) { console.error('[DB] Backup failed:', e.message); }
  };

  doBackup(); // Immediate first backup
  _backupInterval = setInterval(doBackup, intervalMs);
}

function stopBackupRotation() {
  if (_backupInterval) { clearInterval(_backupInterval); _backupInterval = null; }
}

function closeDB() { flushSync(); stopBackupRotation(); }

module.exports = {
  DATA_DIR, getDB, closeDB, getDBInfo, flushSync,
  getSetting, setSetting, setPublicSetting, getSettingInternal, setSettingInternal, getAllSettings,
  getWatchlist, addToWatchlist, updateWatchlistTrader, removeFromWatchlist,
  getPinnedMarkets, addPinnedMarket, removePinnedMarket,
  logTrade, updateTrade, getTradeHistory, getAllTrades, getTradeStats,
  saveWalletSnapshot, getWalletHistory,
  logWalletActivity, getRecentActivity,
  logEvent, getEventLog,
  saveRiskState, loadRiskState,
  logJournalEntry, getJournal,
  startBackupRotation, stopBackupRotation,
  SENSITIVE_KEYS, PUBLIC_WRITABLE_KEYS
};
