/**
 * Express Server
 * Fixes: auth token, restricted CORS, subsystem cleanup on stop,
 *        settings whitelist, rate limiting, API key validation,
 *        audit trail, dry run support, no db variable shadowing
 */

const express = require('express');
const axios = require('axios');
const cors = require('cors');
const path = require('path');
const http = require('http');
const crypto = require('crypto');
const { WebSocketServer } = require('ws');
const setupRoutes = require('./routes');

let app = null;
let server = null;
const logs = [];
const MAX_LOGS = 300;

// Server process start timestamp — defines the "session" window for the
// dashboard's "This Session" card. Distinct from risk.sessionPnL, which
// persists across restarts for daily-loss-limit purposes.
const _serverStartedAt = Date.now();

// Auth token — generated at startup, passed to Electron preload
let authToken = null;

function log(level, message, data) {
  const entry = { time: new Date().toISOString(), level, message, data: data ? JSON.stringify(data).slice(0, 500) : undefined };
  logs.push(entry);
  if (logs.length > MAX_LOGS) logs.shift();
  // Debug logs are spammy (hundreds per monitor poll). On Windows, console.log
  // is synchronous and each call blocks the event loop for ~1-2ms. Skipping
  // console+DB persistence for debug-level logs cuts hundreds of ms per cycle
  // out of the main loop. The in-memory ring buffer above is still updated so
  // the in-app log viewer still shows them.
  if (level === 'debug') return;
  if (level === 'error') console.error(`[${level}] ${message}`, data || '');
  else console.log(`[${level}] ${message}`, data || '');
  try { dbModule && dbModule.logEvent(level, message, data); } catch (e) {}
}

function getLogs() { return [...logs]; }
function clearLogs() { logs.length = 0; }

// ── Module references (no shadowing) ────────────────────────────────

let dbModule = null;
let riskEngine = null;
let rateLimiter = null;
let auditTrail = null;
let monitor = null;
let signal = null;
let notifier = null;
let analytics = null;
let scheduler = null;
let telegram = null;
let clobClient = null;
let clobReady = false;
let exitEngine = null;
let walletTracker = null;
let strategyEngine = null;
let walletLifecycle = null;
let shadowTrader = null;
let arbEngine = null;
let polyWs = null;
let newsSignal = null;
let externalSignals = null;
let marketMaker = null;
let updownStrategy = null;
let bundleArb = null;
let routeModules = null;
let bankrollSyncInterval = null;
let clobReconnectInterval = null;
let inFlightCleanupInterval = null;
let dailyReconciliationInterval = null;
let wss = null;
let wsClients = new Map(); // ws -> { page: string }
let wsPushInterval = null;
let wsWhaleInterval = null;

// ── Event loop lag detector ─────────────────────────────────────────
// Logs whenever the event loop is blocked > 250ms. Helps identify what's
// causing dashboard refresh stalls. Self-contained, ~zero overhead when idle.
let _lagDetectorTimer = null;
function startLagDetector() {
  if (_lagDetectorTimer) return;
  let last = Date.now();
  _lagDetectorTimer = setInterval(() => {
    const now = Date.now();
    const lag = now - last - 100;  // expected interval is 100ms
    if (lag > 250) {
      try { console.warn(`[LagDetector] event loop blocked ${lag}ms at ${new Date(last + 100).toISOString()}`); } catch (_) {}
    }
    last = now;
  }, 100);
  if (_lagDetectorTimer.unref) _lagDetectorTimer.unref();
}

// ── Endpoint response cache ─────────────────────────────────────────
// Tiny TTL cache for expensive assembled endpoints. The dashboard refreshes
// many endpoints in parallel; with a 500ms TTL, repeated calls within the
// same refresh window short-circuit instead of re-walking 11 getStatus() calls.
const _endpointCache = new Map(); // key -> { data, expiresAt }
function cachedJson(key, ttlMs, builder) {
  const now = Date.now();
  const hit = _endpointCache.get(key);
  if (hit && hit.expiresAt > now) return hit.data;
  const data = builder();
  _endpointCache.set(key, { data, expiresAt: now + ttlMs });
  return data;
}
const _inFlightOrders = new Map(); // key: `${market}::${side}`, value: timestamp

// ── Startup smoke test for resolveTokenIds ──────────────────────────
// Verifies that clob.resolveTokenIds() actually returns the correct
// conditionId for real crypto up/down markets fetched fresh from Gamma.
// Returns { status: 'pass'|'fail'|'skipped', reason?, verified? }.
// - pass: all 3 markets round-tripped cleanly
// - skipped: Gamma returned <3 usable candidates (API down / no window)
// - fail: at least one market returned null, wrong conditionId, or failed
//         the condition_ids plural round-trip. Caller should force dryRun.
async function runResolveTokenIdsSmokeTest(clobClient, logFn) {
  if (!clobClient || typeof clobClient.resolveTokenIds !== 'function') {
    return { status: 'skipped', reason: 'clob client not available' };
  }
  // 1. Pull a small set of real active crypto updown markets from Gamma
  let candidates = [];
  try {
    const r = await axios.get('https://gamma-api.polymarket.com/markets', {
      params: {
        limit: 50,
        active: true,
        closed: false,
        end_date_min: new Date().toISOString(),
        end_date_max: new Date(Date.now() + 60 * 60 * 1000).toISOString()
      },
      timeout: 10000
    });
    const all = r.data || [];
    candidates = all.filter(m =>
      /up or down/i.test(m.question || '') &&
      /bitcoin|ethereum|solana|dogecoin|xrp|bnb/i.test(m.question || '') &&
      m.conditionId
    );
  } catch (e) {
    return { status: 'skipped', reason: `gamma pre-fetch failed: ${e.message}` };
  }
  if (candidates.length < 3) {
    return { status: 'skipped', reason: `only ${candidates.length} usable candidates in window` };
  }

  // 2. Verify each of the first 3
  const picks = candidates.slice(0, 3);
  for (const cand of picks) {
    let resolved;
    try {
      resolved = await clobClient.resolveTokenIds(cand.question);
    } catch (e) {
      return { status: 'fail', reason: `resolveTokenIds threw for "${String(cand.question).slice(0, 50)}": ${e.message}` };
    }
    if (!resolved) {
      return { status: 'fail', reason: `resolveTokenIds returned null for "${String(cand.question).slice(0, 50)}"` };
    }
    if (resolved.conditionId !== cand.conditionId) {
      return {
        status: 'fail',
        reason: `conditionId mismatch for "${String(cand.question).slice(0, 50)}": expected ${cand.conditionId?.slice(0, 20)}, got ${resolved.conditionId?.slice(0, 20)}`
      };
    }
    // 3. Cross-verify via condition_ids plural round-trip
    try {
      const v = await axios.get('https://gamma-api.polymarket.com/markets', {
        params: { condition_ids: resolved.conditionId, limit: 1 },
        timeout: 5000
      });
      const got = v.data?.[0];
      if (!got || got.conditionId !== cand.conditionId) {
        return {
          status: 'fail',
          reason: `condition_ids round-trip failed for "${String(cand.question).slice(0, 50)}"`
        };
      }
    } catch (e) {
      // Skip on network hiccup — don't hard-fail startup on a flaky round-trip
      if (logFn) logFn('warn', `smoke test round-trip threw for ${cand.conditionId?.slice(0, 20)}: ${e.message}`);
    }
  }
  return { status: 'pass', verified: picks.length };
}

// ── Whale accumulator (persistent volume tracker) ────────────────────
// Polls /trades continuously so large wallets emerge over time.
const whaleAcc = {
  wallets: new Map(),    // address -> { name, trades, volume, buys, sells, markets: Set, lastSeen }
  seenIds: new Set(),
  totalScanned: 0,
  interval: null,
  lastPoll: null,
  errors: 0,
  started: null
};

// ── Accumulator persistence ─────────────────────────────────────────
const fs = require('fs');

function _getAccumulatorFilePath() {
  const db = getDB();
  const dataDir = db?.DATA_DIR || path.join(__dirname, 'data');
  return path.join(dataDir, 'whale-accumulator-data.json');
}

function persistAccumulator() {
  try {
    // GUARD: never overwrite existing data with empty state
    if (whaleAcc.wallets.size === 0) {
      const filePath = _getAccumulatorFilePath();
      if (fs.existsSync(filePath) && fs.statSync(filePath).size > 100) {
        log('warn', 'Skipping accumulator persist — in-memory is empty but file has data');
        return;
      }
    }
    const serialized = [];
    for (const [addr, w] of whaleAcc.wallets) {
      serialized.push({
        address: addr, name: w.name, pseudonym: w.pseudonym,
        trades: w.trades, volume: w.volume, buys: w.buys, sells: w.sells,
        markets: [...(w.markets || [])],
        firstSeen: w.firstSeen, lastSeen: w.lastSeen
      });
    }
    const data = {
      wallets: serialized,
      totalScanned: whaleAcc.totalScanned,
      lastPoll: whaleAcc.lastPoll,
      savedAt: new Date().toISOString()
    };
    const filePath = _getAccumulatorFilePath();
    const tmpPath = filePath + '.tmp';
    fs.writeFileSync(tmpPath, JSON.stringify(data));
    fs.renameSync(tmpPath, filePath);
  } catch (e) { log('warn', 'Failed to persist accumulator: ' + e.message); }
}

function restoreAccumulator() {
  try {
    let saved = null;
    const filePath = _getAccumulatorFilePath();
    if (fs.existsSync(filePath)) {
      const raw = fs.readFileSync(filePath, 'utf8');
      saved = JSON.parse(raw);
    } else {
      // Migration path: try loading from DB settings
      const d = getDB();
      if (d) {
        saved = d.getSetting('whale_accumulator_data');
        if (saved) {
          // Remove legacy data from DB settings to prevent 50MB+ DB bloat
          d.setSetting('whale_accumulator_data', null);
          log('info', 'Migrated accumulator data from DB settings to standalone file');
        }
      }
    }
    if (!saved || !saved.wallets || !saved.wallets.length) return;
    for (const w of saved.wallets) {
      whaleAcc.wallets.set(w.address, {
        address: w.address, name: w.name, pseudonym: w.pseudonym || '',
        trades: w.trades || 0, volume: w.volume || 0, buys: w.buys || 0, sells: w.sells || 0,
        markets: new Set(w.markets || []),
        firstSeen: w.firstSeen, lastSeen: w.lastSeen
      });
    }
    whaleAcc.totalScanned = saved.totalScanned || 0;
    whaleAcc.lastPoll = saved.lastPoll;
    log('info', `Restored accumulator: ${whaleAcc.wallets.size} wallets, ${whaleAcc.totalScanned} trades scanned (saved ${saved.savedAt})`);
  } catch (e) { log('warn', 'Failed to restore accumulator: ' + e.message); }
}

async function pollForWhales() {
  try {
    const r = await axios.get(`${DATA}/trades`, { params: { limit: 500 }, timeout: 12000 });
    whaleAcc.lastPoll = new Date().toISOString();
    const trades = r.data || [];

    for (const t of trades) {
      const id = t.transactionHash || `${t.proxyWallet}-${t.timestamp}-${t.price}`;
      if (whaleAcc.seenIds.has(id)) continue;
      whaleAcc.seenIds.add(id);
      if (whaleAcc.seenIds.size > 10000) { // FIFO cap
        const iter = whaleAcc.seenIds.values();
        while (whaleAcc.seenIds.size > 8000) whaleAcc.seenIds.delete(iter.next().value);
      }

      const addr = t.proxyWallet;
      if (!addr) continue;

      whaleAcc.totalScanned++;
      if (!whaleAcc.wallets.has(addr)) {
        whaleAcc.wallets.set(addr, {
          address: addr,
          name: t.name || t.pseudonym || addr.slice(0, 8) + '...',
          pseudonym: t.pseudonym || '',
          trades: 0, volume: 0, buys: 0, sells: 0,
          markets: new Set(),
          firstSeen: new Date().toISOString(),
          lastSeen: null
        });
      }
      const w = whaleAcc.wallets.get(addr);
      w.trades++;
      // usdcSize is the USDC notional; fall back to size*price
      const notional = parseFloat(t.usdcSize || 0) || (parseFloat(t.size || 0) * parseFloat(t.price || 0));
      w.volume += notional;
      const tSide = (t.side || '').toUpperCase();
      if (tSide === 'BUY') w.buys++; else if (tSide === 'SELL') w.sells++;
      if (t.title || t.question) w.markets.add((t.title || t.question).slice(0, 60));
      w.lastSeen = new Date().toISOString();
      // Update name if API gives a better one
      if (t.name && t.name !== w.name) w.name = t.name;
      if (t.pseudonym && t.pseudonym !== w.pseudonym) w.pseudonym = t.pseudonym;
    }

    // Cap seenIds to avoid memory growth
    if (whaleAcc.seenIds.size > 100000) {
      const arr = [...whaleAcc.seenIds];
      whaleAcc.seenIds = new Set(arr.slice(-60000));
    }
    // Cap wallets Map — keep top 1500 by volume when exceeding 2000
    if (whaleAcc.wallets.size > 2000) {
      const sorted = [...whaleAcc.wallets.entries()]
        .sort((a, b) => (b[1].volume || 0) - (a[1].volume || 0));
      const keep = new Set(sorted.slice(0, 1500).map(e => e[0]));
      let evicted = 0;
      for (const addr of whaleAcc.wallets.keys()) {
        if (!keep.has(addr)) { whaleAcc.wallets.delete(addr); evicted++; }
      }
      log('info', `[WhaleAcc] Evicted ${evicted} low-volume wallets (cap: 2000)`);
    }
    whaleAcc.errors = 0;
    persistAccumulator();
  } catch (e) {
    whaleAcc.errors++;
    log('warn', 'Whale accumulator poll failed', { error: e.message });
  }
}

function syncWalletPortfolios() {
  // Push accumulated volume estimates to watched wallets so proportional sizing works
  if (!monitor) return;
  for (const [addr] of monitor.wallets) {
    const accData = whaleAcc.wallets.get(addr);
    if (accData && accData.volume > 0) {
      monitor.updateSettings(addr, { estimatedPortfolio: accData.volume });
    }
  }
}

/**
 * Auto-feed high-volume wallets from the accumulator into the wallet tracker
 * so win rates start building immediately on promising wallets.
 */
function feedAccumulatorToTracker() {
  if (!walletTracker) return;

  // Priority: wallets active in short-term markets (≤1h) with decent volume.
  // Thresholds bumped 5x — previous values let the tracker grow unbounded to
  // 1600+ wallets, of which only 66 actually drive copy-trade signals. Tighter
  // gates keep the tracker focused on truly high-quality candidates.
  const SHORT_MIN_TRADES = 25;
  const SHORT_MIN_VOLUME = 5000;
  const LONG_MIN_TRADES = 50;
  const LONG_MIN_VOLUME = 25000;

  const SignalEngine = require('./signal');

  let added = 0;
  for (const [addr, w] of whaleAcc.wallets) {
    if (walletTracker.isTracking(addr)) continue;

    // Check if this wallet trades short-term markets
    let hasShortTerm = false;
    for (const mkt of w.markets) {
      const dur = SignalEngine.parseMarketDurationMinutes(mkt);
      if (dur !== null && dur <= 60) { hasShortTerm = true; break; }
    }

    const minTrades = hasShortTerm ? SHORT_MIN_TRADES : LONG_MIN_TRADES;
    const minVolume = hasShortTerm ? SHORT_MIN_VOLUME : LONG_MIN_VOLUME;

    if (w.trades >= minTrades && w.volume >= minVolume) {
      walletTracker.trackWallet(addr);
      added++;
    }
  }

  if (added > 0) {
    log('info', `Auto-fed ${added} wallets from accumulator to tracker (total tracked: ${walletTracker.walletTrades.size})`);
  }
}

function startWhaleAccumulator() {
  if (whaleAcc.interval) return;
  restoreAccumulator();  // restore from DB before starting
  whaleAcc.started = new Date().toISOString();
  log('info', `Whale accumulator started — polling /trades every 60s (restored ${whaleAcc.wallets.size} wallets)`);
  pollForWhales();  // immediate first poll
  whaleAcc.interval = setInterval(() => {
    pollForWhales();
    syncWalletPortfolios();  // keep watched wallet estimates fresh
    feedAccumulatorToTracker();  // auto-discover promising wallets for win rate tracking
  }, 60000);
}

function stopWhaleAccumulator() {
  if (whaleAcc.interval) { clearInterval(whaleAcc.interval); whaleAcc.interval = null; }
}

function getWhaleResults(minVolume = 0, limit = 100) {
  const results = [];
  for (const [, w] of whaleAcc.wallets) {
    if (w.volume >= minVolume) {
      results.push({
        address: w.address,
        name: w.name,
        pseudonym: w.pseudonym,
        trades: w.trades,
        volume: +w.volume.toFixed(2),
        buys: w.buys,
        sells: w.sells,
        marketCount: w.markets.size,
        avgSize: w.trades > 0 ? +(w.volume / w.trades).toFixed(2) : 0,
        buyPct: w.trades > 0 ? Math.round((w.buys / w.trades) * 100) : 0,
        firstSeen: w.firstSeen,
        lastSeen: w.lastSeen
      });
    }
  }
  return results.sort((a, b) => b.volume - a.volume).slice(0, limit);
}

function getWhaleAccStatus() {
  return {
    running: !!whaleAcc.interval,
    totalWallets: whaleAcc.wallets.size,
    totalTradesScanned: whaleAcc.totalScanned,
    lastPoll: whaleAcc.lastPoll,
    started: whaleAcc.started,
    errors: whaleAcc.errors,
    topByVolume: getWhaleResults(0, 5).map(w => ({
      address: w.address, name: w.name, volume: w.volume, trades: w.trades
    }))
  };
}

function getDB() {
  if (!dbModule) {
    try { dbModule = require('./db'); } catch (e) { log('warn', 'DB not available: ' + e.message); }
  }
  return dbModule;
}

function getRisk() {
  if (!riskEngine) {
    try {
      const R = require('./risk');
      riskEngine = new R(getDB(), auditTrail);
    } catch (e) { log('warn', 'Risk engine not available: ' + e.message); }
  }
  return riskEngine;
}

const GAMMA = 'https://gamma-api.polymarket.com';
const CLOB  = 'https://clob.polymarket.com';
const DATA  = 'https://data-api.polymarket.com';

// ── WebSocket broadcast helpers ─────────────────────────────────────

function wsBroadcast(type, data) {
  if (!wss || wsClients.size === 0) return;
  const msg = JSON.stringify({ type, data, ts: Date.now() });
  for (const [ws] of wsClients) {
    if (ws.readyState === 1) {
      try { ws.send(msg); } catch (e) {}
    }
  }
}

function wsBroadcastToPage(page, type, data) {
  if (!wss || wsClients.size === 0) return;
  const msg = JSON.stringify({ type, data, ts: Date.now() });
  for (const [ws, info] of wsClients) {
    if (ws.readyState === 1 && info.page === page) {
      try { ws.send(msg); } catch (e) {}
    }
  }
}

function wsGatherDashboard() {
  try {
    const db = getDB();
    if (!db) return {};
    // Use getAllTrades — getTradeHistory(500) silently truncates and breaks
    // 7d/all-time stats once the trade table grows past 500 rows.
    const all = db.getAllTrades();
    const now = Date.now();
    const h24 = now - 24 * 60 * 60 * 1000;
    const d7 = now - 7 * 24 * 60 * 60 * 1000;

    function calcStats(trades) {
      // Include 'won' and 'lost' — exit-engine now labels resolved trades as
      // 'won'/'lost' instead of generic 'closed'. Keep 'closed' for backwards
      // compat with older trades and dry-run resolution paths.
      const closed = trades.filter(t => (t.status === 'closed' || t.status === 'won' || t.status === 'lost') && t.pnl != null);
      if (!closed.length) return { count: 0, wins: 0, losses: 0, pnl: 0, avgPnl: 0, winRate: 0 };
      const pnls = closed.map(t => t.pnl);
      const pnl = pnls.reduce((s, p) => s + p, 0);
      const wins = pnls.filter(p => p > 0).length;
      return {
        count: closed.length, wins, losses: closed.length - wins,
        pnl: +pnl.toFixed(2),
        avgPnl: +(pnl / closed.length).toFixed(2),
        winRate: +((wins / closed.length) * 100).toFixed(1)
      };
    }

    const trades24h = all.filter(t => new Date(t.executed_at).getTime() >= h24);
    const trades7d = all.filter(t => new Date(t.executed_at).getTime() >= d7);
    const tradesSession = all.filter(t => new Date(t.executed_at).getTime() >= _serverStartedAt);
    const openTrades = all.filter(t => t.status === 'open');
    const riskStatus = getRisk()?.getStatus?.() || {};
    // Session card derives count/wins/losses/winRate/avgPnl from trades since
    // server start. pnl prefers risk.sessionPnL (running counter, includes
    // open-position realized) and falls back to closed-trade sum.
    const sessionStats = calcStats(tradesSession);
    const sessionPnl = riskStatus.sessionPnL ?? sessionStats.pnl;

    return {
      session: { ...sessionStats, pnl: sessionPnl },
      h24: calcStats(trades24h),
      d7: calcStats(trades7d),
      all: calcStats(all),
      openPositions: openTrades.length,
      dryRun: riskStatus.dryRun ?? db.getSetting('risk_dryRun', true),
      paused: riskStatus.paused ?? false,
      pauseReason: riskStatus.pauseReason ?? null,
      consecutiveLosses: riskStatus.consecutiveLosses ?? 0,
      circuitBreakerActive: riskStatus.circuitBreakerActive ?? false,
      circuitBreakerEnabled: db.getSetting('risk_circuitBreakerEnabled', true),
      circuitBreakerUntil: riskStatus.circuitBreakerUntil ?? null
    };
  } catch (e) { return {}; }
}

function wsGatherSystemStatus() {
  return {
    server: 'running',
    version: getVersion(),
    risk: riskEngine?.getStatus() || null,
    monitor: monitor?.getStatus() || null,
    signal: signal?.getStatus() || null,
    scheduler: scheduler?.getStatus() || null,
    db: getDB()?.getDBInfo() || null,
    notifications: { unread: notifier?.getUnreadCount() || 0 },
    telegram: telegram?.getStatus() || null,
    rateLimiter: rateLimiter?.getStatus() || null,
    audit: auditTrail?.getInfo() || null,
    clob: clobClient?.getStatus() || null,
    exitEngine: exitEngine?.getStatus() || null
  };
}

async function wsPushPageData(ws, page) {
  try {
    const db = getDB();
    if (page === 'dashboard') {
      const stats = wsGatherDashboard();
      const trades = db?.getTradeHistory(10) || [];
      const tradeStats = db?.getTradeStats() || {};
      const riskData = getRisk()?.getStatus() || { enabled: false };
      const systemStatus = wsGatherSystemStatus();
      const payload = { stats, trades, tradeStats, risk: riskData, system: systemStatus };
      if (ws.readyState === 1) ws.send(JSON.stringify({ type: 'dashboard', data: payload, ts: Date.now() }));
    } else if (page === 'trades') {
      const trades = db?.getTradeHistory(100) || [];
      const tradeStats = db?.getTradeStats() || {};
      if (ws.readyState === 1) ws.send(JSON.stringify({ type: 'trades', data: { trades, stats: tradeStats }, ts: Date.now() }));
    } else if (page === 'signal') {
      const signalStatus = signal?.getStatus() || { enabled: false };
      const activity = signal?.getRecentRejections(100) || [];
      if (ws.readyState === 1) ws.send(JSON.stringify({ type: 'signal', data: { status: signalStatus, activity }, ts: Date.now() }));
    } else if (page === 'scanner') {
      const scannerStatus = monitor?.getScannerStatus() || { enabled: false };
      const scannerResults = monitor?.getScannerResults(2, 50) || [];
      if (ws.readyState === 1) ws.send(JSON.stringify({ type: 'scanner', data: { status: scannerStatus, results: scannerResults }, ts: Date.now() }));
    } else if (page === 'updown') {
      const updownStatus = updownStrategy?.getStats() || { enabled: false, reason: 'updown strategy not loaded' };
      if (ws.readyState === 1) ws.send(JSON.stringify({ type: 'updown', data: updownStatus, ts: Date.now() }));
    } else if (page === 'risk') {
      const riskData = getRisk()?.getStatus() || { enabled: false };
      if (ws.readyState === 1) ws.send(JSON.stringify({ type: 'risk', data: riskData, ts: Date.now() }));
    }
  } catch (e) {
    log('warn', 'WS push error', { page, error: e.message });
  }
}

async function initSystems() {
  try {
    const db = getDB();
    const rsk = getRisk();

    // Default live_strategies whitelist — only proven strategies trade live
    if (!db.getSetting('live_strategies')) {
      db.setSetting('live_strategies', ['copy', 'updown']);
    }

    const RateLimiter = require('./rate-limiter');
    rateLimiter = new RateLimiter();

    const AuditTrail = require('./audit');
    auditTrail = new AuditTrail(db ? db.DATA_DIR : path.join(__dirname, 'data'));
    auditTrail.systemEvent('startup', { version: getVersion() });

    // Update risk engine with audit trail
    if (rsk && !rsk.audit) rsk.audit = auditTrail;

    const WalletMonitor = require('./monitor');
    const SignalEngine = require('./signal');
    const NotificationSystem = require('./notifications');
    const Analytics = require('./analytics');
    const Scheduler = require('./scheduler');

    notifier = new NotificationSystem(db);
    notifier.loadSettings();
    notifier.onNotification((data) => {
      wsBroadcast('notification', data);
    });

    const TelegramBot = require('./telegram');
    telegram = new TelegramBot(db, rateLimiter);
    telegram.loadFromDB();

    monitor = new WalletMonitor(db, rsk, rateLimiter);
    monitor.restoreWallets(db);
    signal = new SignalEngine(db, rsk, notifier, auditTrail);

    // Wire eviction handler (clobClient wired after CLOB init below)
    signal.onEvict(async (pos, reason) => {
      if (exitEngine) {
        const currentPrice = pos.tokenId ? await clobClient.getPrice(pos.tokenId, 'SELL') : 0;
        await exitEngine.exitPosition(pos, reason, currentPrice || 0);
      } else {
        rsk.recordResult(pos.id, 0);
      }
    });

    analytics = new Analytics(db);

    // ── CLOB client (real order execution) ──
    const PolymarketCLOB = require('./clob');
    clobClient = new PolymarketCLOB(db, rateLimiter);
    try {
      const ok = await clobClient.initialize();
      if (ok) {
        clobReady = true;
        log('info', 'CLOB client ready — live trading enabled');

        // Defense-in-depth smoke test: before the allowance pre-flight,
        // verify that `clob.resolveTokenIds(question)` actually returns the
        // correct conditionId for real crypto updown markets. Catches the
        // class of bug where Gamma's fuzzy title search silently returns
        // the wrong market (the exact bug that cost $6.48 this session).
        // If the round-trip fails, we force dryRun=true and let the server
        // start anyway so Eric can see the dashboard and diagnose.
        try {
          const riskDryRunPre = db.getSetting('risk_dryRun', true);
          const liveStrategiesPre = db.getSetting('live_strategies', []) || [];
          // Run the smoke test whenever the operator has ANY live strategies
          // configured, regardless of current dryRun flag. We never auto-flip
          // dryRun=false from paper (that's what POST /api/risk/enable-live is
          // for), but we DO want the log to tell us whether the resolveTokenIds
          // path is currently healthy so a transient failure can be retried.
          const wantsLive = Array.isArray(liveStrategiesPre) && liveStrategiesPre.length > 0;
          if (wantsLive) {
            log('info', `Running resolveTokenIds startup smoke test (live_strategies=[${liveStrategiesPre.join(',')}], dryRun=${riskDryRunPre})...`);
            const smokeResult = await runResolveTokenIdsSmokeTest(clobClient, log);
            if (smokeResult.status === 'pass') {
              if (riskDryRunPre === true) {
                log('info', `Smoke test passed (${smokeResult.verified} markets verified). Current mode is PAPER — POST /api/risk/enable-live to resume live trading.`);
              } else {
                log('info', `Smoke test passed (${smokeResult.verified} markets verified). Live mode active.`);
              }
            } else if (smokeResult.status === 'fail') {
              log('error', `Smoke test FAILED: ${smokeResult.reason}`);
              if (riskDryRunPre === false) {
                log('error', 'Flipping dryRun=true defensively. Use POST /api/risk/enable-live to re-enable once resolved.');
                try { db.setSetting('risk_dryRun', true); } catch (e) {}
                // notifier/telegram may be null here on first startup — authoritative alert is the log line above.
                try { notifier?.send?.('Smoke Test Failed', `resolveTokenIds round-trip failed: ${smokeResult.reason}. Forced dry-run mode.`, { type: 'error', priority: 'critical' }); } catch (e) {}
                try { telegram?.send?.(`CRITICAL: smoke test failed — forced dry-run. Reason: ${smokeResult.reason}`); } catch (e) {}
              } else {
                log('warn', 'Current mode already PAPER — not flipping flag. Fix the smoke test failure before calling /api/risk/enable-live.');
              }
            } else {
              // skipped — Gamma unavailable or too few candidates. Do NOT flip dryRun either way.
              log('warn', `Smoke test SKIPPED: ${smokeResult.reason}. Health unknown — will not auto-flip dryRun flag.`);
            }
          } else {
            log('info', 'Smoke test skipped — no live_strategies configured.');
          }
        } catch (e) {
          log('warn', 'Smoke test threw (non-fatal, proceeding): ' + e.message);
        }

        // O1: USDC allowance pre-flight. Auto-approve USDC for the exchange
        // up front so the first live trade doesn't have to wait 10–30 seconds
        // for an on-chain approval transaction (which would miss the 5-min
        // Up/Down candle window). Only runs if the user has explicitly
        // configured live mode — paper-only sessions never touch the chain.
        try {
          const riskDryRun = db.getSetting('risk_dryRun', true);
          const liveStrategies = db.getSetting('live_strategies', []) || [];
          const updownLive = riskDryRun === false && Array.isArray(liveStrategies) && liveStrategies.includes('updown');

          if (updownLive) {
            // Cover 8 concurrent updown positions at max size (audit recommendation).
            // maxSize fallback matches DEFAULTS.updown_maxSize in updown-strategy.js.
            const maxSize = db.getSetting('updown_maxSize', 10) || 10;
            const bufferUSD = maxSize * 8;
            log('info', `Pre-flighting USDC allowance for live updown ($${bufferUSD} buffer)...`);
            const result = await clobClient.ensureAllowance(bufferUSD, false);
            if (result.sufficient) {
              if (result.approved) {
                log('info', `USDC auto-approved for exchange at startup (txHash: ${result.txHash || 'unknown'})`);
              } else {
                log('info', `USDC allowance already sufficient for updown live mode ($${bufferUSD} needed)`);
              }
            } else {
              // Don't block startup — the per-order ensureAllowance in clob.placeOrder
              // will retry, and other strategies may still work. But surface loudly.
              log('error', `USDC allowance pre-flight FAILED: ${result.error || 'unknown'}. Live updown trades will likely fail until this is resolved.`);
            }
          } else {
            log('info', 'Allowance pre-flight skipped — updown not in live mode (paper only)');
          }
        } catch (e) {
          log('warn', 'Allowance pre-flight threw (non-fatal): ' + e.message);
        }
      } else {
        clobReady = false;
        log('warn', 'CLOB client not ready: ' + (clobClient.error || 'missing credentials'));
        log('info', 'Trading will work in dry-run mode. Configure credentials on the Connect page to enable live trading.');
      }
    } catch (e) {
      clobReady = false;
      log('warn', 'CLOB init error: ' + e.message);
    }

    // Wire CLOB into signal engine (AFTER initialization)
    signal.clobClient = clobClient;

    // ── WebSocket for real-time price data ──
    try {
      const PolymarketWebSocket = require('./websocket');
      polyWs = new PolymarketWebSocket({ db, log: (level, msg) => log(level, `[WS] ${msg}`) });
      log('info', 'WebSocket module initialized (lazy-connect on first subscription)');
      // Wire WS into monitor (created earlier, before WS init)
      if (monitor) monitor.ws = polyWs;
    } catch (e) {
      log('warn', 'WebSocket init failed (non-critical): ' + e.message);
    }

    // ── Wallet tracker (win rate tracking per wallet) ──
    const WalletTracker = require('./wallet-tracker');
    walletTracker = new WalletTracker(db, rateLimiter);

    // Wire tracker and monitor into signal engine (must be after creation)
    signal.walletTracker = walletTracker;
    signal.monitor = monitor;
    signal.loadLearningState(); // Restore post-trade learning adjustments

    // Seed the learning state from historical tracker data.
    // This populates wallet confidence adjustments and price zone results
    // from 5000+ resolved trades so the engine learns immediately rather
    // than starting blind.
    signal.bootstrapLearningState();

    // Feed all already-restored monitor wallets into the tracker
    // (restoreWallets ran before the monitor.watch override, so they were missed)
    for (const [addr] of monitor.wallets) {
      walletTracker.trackWallet(addr);
    }
    if (monitor.wallets.size > 0) {
      log('info', `Fed ${monitor.wallets.size} restored monitor wallets to tracker`);
    }

    // ── Strategy evolution engine (multi-armed bandit) ──
    const StrategyEngine = require('./strategy-engine');
    strategyEngine = new StrategyEngine(db);

    // Register default strategies
    strategyEngine.register('cheap_entry', { minPrice: 0.05, maxPrice: 0.35, label: 'Cheap entries ($0.05-$0.35)' });
    strategyEngine.register('sweet_spot', { minPrice: 0.15, maxPrice: 0.50, label: 'Sweet spot ($0.15-$0.50)' });
    strategyEngine.register('moderate', { minPrice: 0.40, maxPrice: 0.70, label: 'Moderate ($0.40-$0.70)' });
    strategyEngine.register('high_conviction', { minPrice: 0.60, maxPrice: 0.80, label: 'High conviction ($0.60-$0.80)' });

    signal.strategyEngine = strategyEngine;
    log('info', 'Strategy engine initialized with ' + strategyEngine.strategies.size + ' strategies');

    // ── Wallet lifecycle manager (ACTIVE/PASSIVE/DISCARDED state machine) ──
    const WalletLifecycle = require('./wallet-lifecycle');
    walletLifecycle = new WalletLifecycle(db, walletTracker);
    walletLifecycle.monitor = monitor;
    walletLifecycle.signal = signal;
    walletLifecycle.scheduler = scheduler;
    walletLifecycle.start();
    log('info', 'Wallet lifecycle manager started');

    // ── Exit engine (stop-loss, take-profit, trailing stop) ──
    const ExitEngine = require('./exit-engine');
    exitEngine = new ExitEngine({ db, risk: rsk, clob: clobClient, notifier, audit: auditTrail, telegram, signal });

    // Wire monitor -> signal (buys) + mirror exits (sells)
    // Queues to process: whale exits run in parallel, buys run sequentially
    const pendingExitPromises = [];

    // M3: Record a volume tick for every observed trade (before any auto_copy filtering)
    monitor.onTrade((trade) => {
      if (signal?.recordVolumeTick) {
        signal.recordVolumeTick(trade.market);
      }
    });

    monitor.onTrade(async (trade) => {
      // autoCopy gate removed — signal engine's focused wallet filter (signal.js:65)
      // handles the decision. This prevents trades being silently dropped when
      // lifecycle autoCopy flags are out of sync with trading activity.

      // ── Whale SELL detected → check if we should mirror-exit ──
      if (trade.action === 'SELL') {
        const positions = rsk?.state?.openPositions || [];
        const match = positions.find(p =>
          p.copied_from_address === trade.wallet_address &&
          p.market?.toLowerCase() === trade.market?.toLowerCase()
        );

        if (match && exitEngine) {
          log('info', 'Whale exit detected — mirror-exiting position', {
            whale: trade.wallet_name, market: trade.market, positionId: match.id
          });
          // Fire exit in parallel — don't await
          const exitPromise = exitEngine.exitPosition(match, 'whale_exit', parseFloat(trade.price) || 0)
            .catch(e => log('error', 'Whale mirror exit failed', { error: e.message, market: trade.market }));
          pendingExitPromises.push(exitPromise);
          // Clean up completed promises periodically
          if (pendingExitPromises.length > 10) {
            await Promise.allSettled(pendingExitPromises.splice(0, pendingExitPromises.length));
          }
          return;
        }
        // No matching position — ignore the sell
        return;
      }

      // ── Whale BUY detected → evaluate as copy signal ──
      const result = await signal.evaluate(trade);
      log('info', 'Signal evaluated', { action: result.action, market: trade.market });

      // Fire shadow evaluation in parallel — fire-and-forget, errors suppressed
      if (shadowTrader) {
        shadowTrader.evaluateShadow(trade).catch(() => {});
      }

      // Push trade event to all WS clients immediately
      wsBroadcast('tradeEvent', { market: trade.market, side: trade.action, wallet: trade.wallet_name, size: trade.size, price: trade.price });
    });

    // I15: Whale exit detection — log only (exit handled by onTrade SELL handler above)
    monitor.onWhaleSell(async (trade) => {
      try {
        const matchedPos = rsk?.state?.openPositions?.find(p =>
          (p.conditionId && trade.conditionId && p.conditionId === trade.conditionId) ||
          (p.market && trade.market && p.market === trade.market)
        );
        if (!matchedPos) return;
        auditTrail?.record('WHALE_SELL_DETECTED', {
          wallet: trade.wallet_address,
          market: trade.market,
          conditionId: trade.conditionId,
          ourSide: matchedPos.side,
          ourSize: matchedPos.size,
          reason: 'Monitored wallet exited position — exit handled by onTrade'
        });
        notifier.send('Whale Exit Detected', `${trade.wallet_address?.slice(0, 8)} sold ${trade.market}`);
      } catch (e) {
        log('error', '[WhaleSell] Log error', { error: e.message });
      }
    });

    // Auto-register watched wallets with tracker for win rate analysis
    const origWatch = monitor.watch.bind(monitor);
    monitor.watch = function(address, name, opts) {
      origWatch(address, name, opts);
      if (walletTracker) walletTracker.trackWallet(address);
    };

    monitor.onAlert((alert) => {
      if (notifier) notifier.largePosition(alert.wallet, alert.trade.market, alert.trade.size);
      if (telegram) telegram.largePosition(alert.wallet, alert.trade.market, alert.trade.size);
      wsBroadcast('alert', { wallet: alert.wallet, market: alert.trade?.market, size: alert.trade?.size });
    });

    // Wire signal -> execution (uses real CLOB client)
    signal.onExecute(async (sig) => {
      if (!clobClient?.isReady()) {
        throw new Error('CLOB client not ready — check credentials on Connect page');
      }

      // Resolve token ID for this market
      const tokens = await clobClient.resolveTokenIds(sig.market);
      if (!tokens) throw new Error('Could not resolve token ID for market: ' + sig.market);

      // Verify market is still active before placing order
      const marketActive = await clobClient.isMarketActive(tokens.conditionId);
      if (!marketActive) {
        log('warn', 'Skipping trade — market is resolved/closed', { market: sig.market });
        return { success: false, error: 'Market is resolved or closed' };
      }

      const tokenId = sig.side === 'YES' ? tokens.yesTokenId : tokens.noTokenId;

      // Convert USD size to shares (CLOB expects shares, not USD — Bug #6)
      const sigPrice = parseFloat(sig.price) || 0;
      const sigShares = sigPrice > 0 ? Math.floor(sig.size / sigPrice) : 0;
      if (sigShares <= 0) throw new Error(`Cannot compute shares: $${sig.size} at price $${sigPrice}`);

      log('info', 'Auto-executing trade via CLOB', {
        market: sig.market, side: sig.side, usdSize: sig.size, shares: sigShares, price: sig.price,
        tokenId: tokenId.slice(0, 20) + '...'
      });

      const result = await clobClient.placeAndVerify(tokenId, 'BUY', sig.price, sigShares, {
        tickSize: tokens.tickSize,
        negRisk: tokens.negRisk,
        orderType: 'GTC',
        verifyTimeoutMs: 15000,
        retryAtMarket: true
      });

      if (!result.success) throw new Error('Order failed: ' + result.error);

      // Use actual filled size/price (handles partial fills)
      const filledSize = result.filledSize || sig.size;
      const filledPrice = result.filledPrice || sig.price;

      // Track position in risk engine for exit monitoring
      if (rsk) {
        rsk.openPosition({
          id: result.orderId || Date.now(),
          tradeId: sig.tradeId,
          market: sig.market,
          side: sig.side,
          size: filledSize,
          price: filledPrice,
          tokenId,
          tickSize: tokens.tickSize,
          negRisk: tokens.negRisk,
          conditionId: tokens.conditionId,
          copied_from: sig.copied_from,
          copied_from_address: sig.copied_from_address
        });
      }

      if (auditTrail) auditTrail.tradeExecute(sig, result.data);
      return result;
    });

    scheduler = new Scheduler({ db, risk: rsk, monitor, signal, notifier, analytics, rateLimiter, audit: auditTrail, telegram });
    scheduler._walletTracker = walletTracker;
    scheduler._getAccumulatorData = (addr) => whaleAcc.wallets.get(addr) || null;
    scheduler._clobClient = clobClient;

    // Wire notifiers into CLOB client for circuit breaker alerts
    if (clobClient) clobClient.setNotifiers(notifier, telegram);

    // ── Shadow trader — parallel dry-run A/B engine ──
    try {
      const ShadowTrader = require('./shadow-trader');
      const dataDir = db?.DATA_DIR || path.join(__dirname, 'data');
      shadowTrader = new ShadowTrader({ db, signal, scheduler, notifier, dataDir });
      // Weekly shadow vs. live comparison (every 7 days)
      scheduler.schedule('shadowComparison', 7 * 24 * 60 * 60 * 1000,
        () => shadowTrader.comparePerformance());
      log('info', 'Shadow trader initialised');
    } catch (e) {
      log('warn', 'Shadow trader init failed (non-critical): ' + e.message);
    }

    // ── Arb engine — resolution arb, near-expiry convergence, imbalance scaffold ──
    try {
      const ArbEngine = require('./arb-engine');
      arbEngine = new ArbEngine({ db, risk: rsk, clob: clobClient, notifier, audit: auditTrail, scheduler, rateLimiter, ws: polyWs });
      arbEngine.start();
      log('info', 'Arb engine initialised (A1 resolution, A2 near-expiry, A3 scaffold)');
    } catch (e) {
      log('warn', 'Arb engine init failed (non-critical): ' + e.message);
    }

    // ── News + LLM signal engine ──
    try {
      const NewsSignalEngine = require('./news-signal');
      newsSignal = new NewsSignalEngine({ db, risk: rsk, clob: clobClient, audit: auditTrail, log: (level, msg, data) => log(level, `[NewsSignal] ${msg}`, data) });
      newsSignal.start(); // only activates if news_enabled=true in DB
      log('info', 'News signal engine initialized');
    } catch (e) {
      log('warn', 'News signal engine init failed (non-critical): ' + e.message);
    }

    // ── External prediction market signals ──
    try {
      const ExternalSignals = require('./external-signals');
      externalSignals = new ExternalSignals({ db, audit: auditTrail, log: (level, msg) => log(level, `[ExtSignals] ${msg}`) });
      externalSignals.start();
      log('info', 'External signals initialized (Manifold + Metaculus)');
    } catch (e) {
      log('warn', 'External signals init failed (non-critical): ' + e.message);
    }

    // ── Up/Down spot price strategy (highest volume markets) ──
    try {
      const UpDownStrategy = require('./updown-strategy');
      updownStrategy = new UpDownStrategy({ db, risk: rsk, clob: clobClient, audit: auditTrail, rateLimiter, ws: polyWs, telegram, notifier, log: (level, msg) => log(level, `[UpDown] ${msg}`) });
      updownStrategy.start();
      log('info', 'Up/Down strategy initialized (scanning every 15s)');
    } catch (e) {
      log('warn', 'Up/Down strategy init failed (non-critical): ' + e.message);
    }

    // ── Route modules (strategy routers with lifecycle hooks) ──
    // Mount all modular strategy routes onto the live Express app and call their
    // init() hooks. Adding a new strategy = create routes/<name>.js + 3 lines
    // in routes/index.js. server.js never needs to know strategy internals.
    if (!routeModules) {
      routeModules = setupRoutes(app, {
        db,
        risk:     rsk,
        clob:     clobClient,
        notifier,
        audit:    auditTrail,
        log:      (level, msg) => log(level, msg),
      });
    }
    await routeModules.initAll();

    // ── Market maker ──
    try {
      const MarketMaker = require('./market-maker');
      marketMaker = new MarketMaker({ db, clob: clobClient, risk: rsk, audit: auditTrail, ws: polyWs, log: (level, msg) => log(level, `[MM] ${msg}`) });
      marketMaker.start(); // only activates if mm_enabled=true in DB
      log('info', 'Market maker initialized');
    } catch (e) {
      log('warn', 'Market maker init failed (non-critical): ' + e.message);
    }

    // ── Bundle arb scanner (risk-free YES+NO arbitrage) ──
    try {
      const BundleArb = require('./bundle-arb');
      bundleArb = new BundleArb({ db, risk: rsk, clob: clobClient, audit: auditTrail, rateLimiter, ws: polyWs, log: (level, msg) => log(level, `[BundleArb] ${msg}`) });
      bundleArb.start();
      log('info', 'Bundle arb scanner initialized');
    } catch (e) {
      log('warn', 'Bundle arb init failed (non-critical): ' + e.message);
    }

    // Wire UpDown WR tracking through exit-engine callbacks.
    // H1 (Apr 8): delegates to updownStrategy.handleLiveExit which derives
    // asset/direction from the position and looks up the stored magnitudeBucket
    // so per-asset adaptive learning (auto-disable, adaptive magnitude threshold)
    // works in live mode. The old raw recordTradeResult(pnl) call silently
    // disabled all adaptive learning for live trades.
    if (exitEngine && updownStrategy) {
      exitEngine.onExit((pos, pnl, _reason) => {
        if (pos.copied_from === 'updown_strategy') {
          updownStrategy.handleLiveExit(pos, pnl);
        }
      });
    }

    // ── Crash recovery: reconcile open positions on restart ──
    // Also re-hydrate any DB trades with status 'open' or 'dry_run' that weren't in riskState
    const reconcilePositions = async () => {
      // Re-hydrate lost open positions from DB trade log
      if (rsk) {
        const dbTrades = getDB()?.getTradeHistory(500) || [];
        const currentIds = new Set((rsk.state?.openPositions || []).map(p => p.id));
        // Re-hydrate ALL open trades regardless of age — exit-engine and UpDown
        // startup catchup will resolve them with actual results from Gamma/Binance.
        // No artificial time window: APIs retain historical data indefinitely.

        for (const t of dbTrades) {
          // Skip already-closed trades — prevents double-counting PnL on restart
          if (t.status === 'closed' || t.status === 'won' || t.status === 'lost') continue;
          if ((t.status === 'open' || t.status === 'dry_run') && !currentIds.has(t.id)) {
            // Reconstruct minimal position for exit engine to track
            const pos = {
              id: t.id,
              tradeId: t.id,  // Must match for recordExit to update DB status
              market: t.market,
              side: t.side,
              price: parseFloat(t.price) || 0,
              size: parseFloat(t.size) || 0,
              copied_from: t.copied_from,
              copied_from_address: t.copied_from_address,
              conditionId: t.conditionId || null,
              tokenId: t.tokenId || null,
              openedAt: t.executed_at || new Date().toISOString(),
              dryRun: t.dry_run || false,
              stop_loss: t.stop_loss || null,
              take_profit: t.take_profit || null
            };
            try { rsk.state.openPositions.push(pos); } catch (_) {}
            log('info', `Crash recovery: re-hydrated position ${t.id} (${t.market}) from DB`);
          }
        }
      }

      const positions = rsk?.state?.openPositions || [];
      if (positions.length === 0) return;

      log('info', `Crash recovery: reconciling ${positions.length} open positions`);

      for (const pos of [...positions]) {
        // Skip dry-run positions — they should only be resolved by the resolution watcher
        if (pos.dryRun) continue;

        try {
          // 1. Check if market has resolved while we were down
          if (pos.conditionId) {
            const isActive = await clobClient?.isMarketActive(pos.conditionId);
            if (isActive === false) {
              log('info', `Market resolved while offline: ${pos.market}`, { positionId: pos.id });
              // The exit engine's resolution watcher will pick this up on next cycle
              continue;
            }
          }

          // 2. Check if the source whale has exited this position
          if (pos.copied_from_address) {
            try {
              const r = await axios.get(`${DATA}/trades`, {
                params: { user: pos.copied_from_address, limit: 30 },
                timeout: 10000
              });
              const trades = r.data || [];

              // Look for a SELL from the whale on the same market after our entry
              const entryTime = new Date(pos.openedAt).getTime();
              const whaleExit = trades.find(t => {
                const tSide = (t.side || '').toUpperCase();
                const market = (t.title || t.question || t.market || '').toLowerCase();
                const ts = t.timestamp ? new Date(parseInt(t.timestamp) * 1000 || t.timestamp).getTime() : 0;
                return tSide === 'SELL' && market === (pos.market || '').toLowerCase() && ts > entryTime;
              });

              if (whaleExit) {
                log('info', `Whale exited while offline: ${pos.copied_from} sold ${pos.market}`, { positionId: pos.id });
                // Try to exit — if profitable, take profit; if losing, damage control
                if (exitEngine && clobClient?.isReady()) {
                  const currentPrice = pos.tokenId ? await clobClient.getPrice(pos.tokenId, 'SELL') : null;
                  if (currentPrice !== null) {
                    const entryPrice = parseFloat(pos.price) || 0;
                    if (currentPrice >= entryPrice) {
                      // In profit — exit to take profit
                      await exitEngine.exitPosition(pos, 'whale_exit', currentPrice);
                    } else {
                      // Losing — use stop-loss logic
                      const lossPct = ((entryPrice - currentPrice) / entryPrice) * 100;
                      const cfg = rsk.getConfig();
                      if (lossPct >= (cfg.stopLossPct || 15)) {
                        await exitEngine.exitPosition(pos, 'stop_loss', currentPrice);
                      } else {
                        // Small loss — exit to follow the whale
                        await exitEngine.exitPosition(pos, 'whale_exit', currentPrice);
                      }
                    }
                  }
                }
              }
            } catch (e) {
              log('warn', 'Crash recovery: failed to check whale activity', { error: e.message, wallet: pos.copied_from });
            }
          }
        } catch (e) {
          log('warn', 'Crash recovery error for position', { id: pos.id, error: e.message });
        }
      }

      log('info', 'Crash recovery complete');
    };

    // Run reconciliation 15 seconds after startup (give CLOB time to init)
    setTimeout(reconcilePositions, 15000);

    // WAL startup reconciliation
    try {
      const WAL = require('./wal');
      const dataDir = getDB()?.DATA_DIR || path.join(__dirname, 'data');
      const wal = new WAL(dataDir);
      const uncommitted = wal.getUncommitted();
      if (uncommitted.length > 0) {
        log('warn', `WAL: ${uncommitted.length} uncommitted trade intent(s) found on startup — these may need manual review`);
        const openPositions = rsk?.getStatus()?.openPositionDetails || [];
        for (const intent of uncommitted) {
          const alreadyOpen = openPositions.some(p => p.market === intent.market);
          if (!alreadyOpen) {
            log('warn', `WAL: unresolved intent for market "${intent.market}" (${intent.side} ${intent.size}) — position not found in risk engine`);
          }
        }
      }
      wal.prune(); // always prune on startup to clean up old committed entries
    } catch (e) {
      log('warn', 'WAL reconciliation failed: ' + e.message);
    }

    // ── Config hardening: set safe defaults on first run ──
    const configDefaults = {
      'risk_bankroll': 500,
      'risk_maxTradeSizeUSD': 25,
      'risk_maxOpenPositions': 10,
      'risk_stopLossPct': 10,
      'risk_trailingStopPct': 8,
      'signal_minMarketDurationMinutes': 1,
      'signal_minConfidence': 40,
      'signal_minRiskRewardRatio': 1.0,
      'signal_maxPrice': 0.50,
    };

    // Permanent blacklist — wallets proven to lose money (never copy these)
    const existingBlacklist = db.getSetting('signal_walletBlacklist', null);
    if (!existingBlacklist) {
      db.setSetting('signal_walletBlacklist', [
        '0x21170d', // 38% WR, -$11.40
        '0xb373fc', // 42% WR, -$69.45 — biggest loser
        '0xae8d27', // 40% WR, -$41.01 — large position losses
        '0x94c1bf', // 54% WR, -$13.34 — wins don't offset losses
        '0xbbad7f', // 42% WR, -$8.87
        '0x53eb76', // 36% WR, -$8.84
      ]);
      log('info', 'Initialized wallet blacklist with 6 toxic wallets');
    }
    for (const [key, val] of Object.entries(configDefaults)) {
      if (db.getSetting(key, undefined) === undefined) {
        db.setSetting(key, val);
        log('info', `Set default: ${key} = ${val}`);
      }
    }

    // ── F2: Live orphan recovery — runs synchronously BEFORE exit-engine starts ──
    // Guards against the zombie-filter race condition where a live open trade exists
    // in the DB but was evicted from risk.openPositions during restart (e.g. a crash
    // mid-save, or risk._restoreState silently filtered it out). Without this, the
    // exit-engine never sees the position and the winning CTF token stays locked
    // on-chain (the sweep filter requires status='won' written by exit-engine).
    //
    // Only live trades are re-injected. Dry-run orphans are intentionally excluded —
    // the deferred reconcilePositions() already handles them with full CLOB/Gamma checks.
    try {
      const allDbTrades = getDB()?.getAllTrades() || [];
      const liveOrphans = allDbTrades.filter(t =>
        t.status === 'open' && t.dry_run !== true
      );

      if (liveOrphans.length > 0) {
        const currentLiveIds = new Set(
          (rsk.state?.openPositions || [])
            .filter(p => !p.dryRun)
            .map(p => p.id)
        );

        let injected = 0;
        for (const t of liveOrphans) {
          if (currentLiveIds.has(t.id)) continue; // already present — skip

          // Reconstruct the position object using the fields risk.js expects in
          // openPositions. We use the same shape as the existing reconcilePositions
          // crash-recovery path so the exit-engine can call exitPosition on it.
          const pos = {
            id: t.id,
            tradeId: t.id,          // C5: integer id so db.updateTrade finds the row
            market: t.market,
            side: t.side,
            category: t.category || 'unknown',
            size: parseFloat(t.size) || 0,
            price: parseFloat(t.price) || 0,
            shares: (parseFloat(t.price) || 0) > 0
              ? Math.floor((parseFloat(t.size) || 0) / parseFloat(t.price))
              : 0,
            conditionId: t.conditionId || null,
            tokenId: t.tokenId || null,
            negRisk: t.negRisk || false,
            copied_from: t.copied_from || null,
            copied_from_address: t.copied_from_address || null,
            openedAt: t.executed_at || new Date().toISOString(),
            dryRun: false,
            stop_loss: t.stop_loss || null,
            take_profit: t.take_profit || null,
          };

          try {
            rsk.state.openPositions.push(pos);
            injected++;
            log('warn', `ORPHAN RECOVERY: re-injected live trade ${t.id} for "${t.market}" into openPositions`);
            auditTrail?.record('ORPHAN_RECOVERY', {
              tradeId: t.id,
              market: t.market,
              side: t.side,
              size: t.size,
              openedAt: t.executed_at,
            });
          } catch (pushErr) {
            log('error', `ORPHAN RECOVERY: failed to inject trade ${t.id}`, { error: pushErr.message });
          }
        }

        if (injected > 0) {
          log('warn', `ORPHAN RECOVERY: ${injected} live trade(s) re-injected before exit-engine start`);
          try {
            telegram?.send(`ORPHAN RECOVERY: ${injected} live open position(s) were missing from risk state and have been re-injected. Check logs for details.`);
          } catch (_) {}
        }
      }
    } catch (e) {
      log('error', 'ORPHAN RECOVERY scan failed (non-fatal, exit-engine starting anyway): ' + e.message);
    }

    // Start exit engine + resolution watcher
    exitEngine.start();

    // Start wallet tracker
    walletTracker.start();

    // Auto-sync bankroll from USDC balance every 5 minutes
    const syncBankroll = async () => {
      if (!clobClient?.isReady()) return;
      try {
        const balance = await clobClient.getUSDCBalance();
        if (balance !== null && balance > 0) {
          const currentBankroll = db.getSetting('risk_bankroll', 500);
          const delta = balance - currentBankroll;
          if (Math.abs(delta) > 1) { // Only update if meaningful change
            db.setSetting('risk_bankroll', balance);
            log('info', 'Bankroll synced from USDC balance', { old: currentBankroll, new: balance, delta: +delta.toFixed(2) });

            // M3: escalate when the delta exceeds a "normal trading pnl" threshold.
            // Expected 5-min updown trade pnl range: ~$0.20–$2. A delta of $10+
            // between syncs (5 min) suggests either an unusually active period
            // OR accounting drift / manual transfer / bug. Fire Telegram so you
            // notice before it compounds. This is cheap insurance against silent
            // bankroll-tracking breakage going live.
            if (Math.abs(delta) > 10) {
              log('warn', 'Large bankroll delta detected between syncs', {
                old: currentBankroll, new: balance, delta: +delta.toFixed(2)
              });
              if (telegram) {
                const sign = delta >= 0 ? '+' : '';
                telegram.send(`⚠️ Bankroll delta ${sign}$${delta.toFixed(2)} in last 5min ($${currentBankroll.toFixed(2)} → $${balance.toFixed(2)}). Verify this matches expected trading activity.`).catch(() => {});
              }
            }

            // Alert if circuit breaker is active and bankroll changed
            if (riskEngine?.state?.circuitBreakerUntil && Date.now() < riskEngine.state.circuitBreakerUntil) {
              log('warn', 'Bankroll changed while circuit breaker active', { old: currentBankroll, new: balance });
              if (telegram) {
                telegram.send(`⚠️ Bankroll changed ($${currentBankroll} → $${balance}) while circuit breaker is active. Trading will NOT auto-resume. Use /resume confirm.`).catch(() => {});
              }
            }
          }
        }
      } catch (e) {
        log('warn', 'Bankroll sync failed', { error: e.message });
      }
    };
    setTimeout(syncBankroll, 10000); // First sync 10s after startup
    bankrollSyncInterval = setInterval(syncBankroll, 5 * 60 * 1000); // Then every 5 minutes

    // ── O5: Daily PnL reconciliation ──
    // Separate concern from syncBankroll (which corrects bankroll drift every 5min).
    // This takes a snapshot of (wallet balance, timestamp) at least 20h apart,
    // sums up closed live trade pnls in the interval, and compares:
    //   expected = previousBalance + sumOfLivePnlInInterval
    //   actual   = currentBalance
    //   drift    = actual - expected
    // If |drift| > $0.50, fire a Telegram alert AND log a warning so the user
    // has an explicit daily signal that recorded pnl matches wallet reality.
    // H3 + M3 eliminate most drift sources, so any alert here means something
    // unusual is happening (manual transfer, fee schedule change, bug, or an
    // edge-case resolution path that's bypassing the normal accounting).
    //
    // Runs hourly — only actually compares if ≥20h have passed since the last
    // snapshot. On first run it just saves a baseline.
    const dailyReconciliation = async () => {
      if (!clobClient?.isReady()) return;
      try {
        const now = Date.now();
        const snap = db.getSetting('updown_dailyReconciliation', null);
        const currentBalance = await clobClient.getUSDCBalance();
        if (currentBalance == null) return;

        // First run: save baseline snapshot, no comparison possible yet
        if (!snap || !snap.lastSnapshotTs || !isFinite(snap.lastSnapshotBalance)) {
          db.setSetting('updown_dailyReconciliation', {
            lastSnapshotTs: now,
            lastSnapshotBalance: currentBalance
          });
          log('info', 'Daily reconciliation: baseline snapshot saved', { balance: currentBalance });
          return;
        }

        const hoursSince = (now - snap.lastSnapshotTs) / (60 * 60 * 1000);
        if (hoursSince < 20) return; // not yet time for next comparison

        // Sum closed LIVE trade pnls in the interval (explicitly exclude dry-run)
        const trades = db.getTradeHistory?.(500) || [];
        const closedInInterval = trades.filter(t =>
          (t.status === 'closed' || t.status === 'won' || t.status === 'lost') &&
          t.pnl !== null && t.pnl !== undefined &&
          t.dry_run !== true &&
          t.closed_at &&
          new Date(t.closed_at).getTime() > snap.lastSnapshotTs
        );
        const sumPnl = closedInInterval.reduce((s, t) => s + (parseFloat(t.pnl) || 0), 0);

        const expectedBalance = snap.lastSnapshotBalance + sumPnl;
        const drift = currentBalance - expectedBalance;

        log('info', 'Daily reconciliation', {
          hoursSince: +hoursSince.toFixed(1),
          startBalance: +snap.lastSnapshotBalance.toFixed(2),
          endBalance: +currentBalance.toFixed(2),
          sumPnl: +sumPnl.toFixed(2),
          expected: +expectedBalance.toFixed(2),
          drift: +drift.toFixed(2),
          closedTrades: closedInInterval.length
        });

        if (Math.abs(drift) > 0.50) {
          log('warn', `Daily reconciliation DRIFT: $${drift.toFixed(2)}`, {
            expected: +expectedBalance.toFixed(2),
            actual: +currentBalance.toFixed(2),
            closedTrades: closedInInterval.length
          });
          if (telegram) {
            const sign = drift >= 0 ? '+' : '';
            const psign = sumPnl >= 0 ? '+' : '';
            telegram.send(
              `⚠️ *Daily reconciliation drift: ${sign}$${drift.toFixed(2)}*\n\n` +
              `Prev snapshot: $${snap.lastSnapshotBalance.toFixed(2)}\n` +
              `Sum of ${closedInInterval.length} live trade pnls: ${psign}$${sumPnl.toFixed(2)}\n` +
              `Expected balance: $${expectedBalance.toFixed(2)}\n` +
              `Actual wallet:    $${currentBalance.toFixed(2)}\n\n` +
              `This means recorded pnl diverges from actual wallet change. ` +
              `Investigate before next trading session — possible causes: manual ` +
              `transfer, fee schedule change, resolution path bug, or an exit that ` +
              `didn't flow through handleLiveExit.`
            ).catch(() => {});
          }
        }

        // Save new snapshot (always — we want the baseline to keep advancing)
        db.setSetting('updown_dailyReconciliation', {
          lastSnapshotTs: now,
          lastSnapshotBalance: currentBalance
        });
      } catch (e) {
        log('warn', 'Daily reconciliation failed', { error: e.message });
      }
    };
    // First run 1min after startup (lets CLOB settle), then hourly.
    // The 20h gate inside the function ensures we only actually compare once per day.
    setTimeout(dailyReconciliation, 60 * 1000);
    dailyReconciliationInterval = setInterval(dailyReconciliation, 60 * 60 * 1000);

    startWhaleAccumulator();

    // Start DB backup rotation (hourly, keep 24)
    if (db?.startBackupRotation) db.startBackupRotation();

    // In-flight order TTL cleanup — evict stale entries every 30s
    inFlightCleanupInterval = setInterval(() => {
      const now = Date.now();
      for (const [k, ts] of _inFlightOrders) {
        if (now - ts > 60000) _inFlightOrders.delete(k);
      }
    }, 30000);

    // CLOB auto-reconnect: check every 5 minutes, re-initialize if connection lost
    clobReconnectInterval = setInterval(async () => {
      if (clobClient && !clobClient.isReady() && !clobClient._reconnecting) {
        clobClient._reconnecting = true;
        log('info', 'CLOB auto-reconnect: attempting re-initialization...');
        try {
          const ok = await clobClient.initialize();
          if (ok) log('info', 'CLOB auto-reconnect: success');
          else log('warn', 'CLOB auto-reconnect: failed — ' + (clobClient.error || 'unknown'));
        } catch (e) {
          log('warn', 'CLOB auto-reconnect error: ' + e.message);
        }
        clobClient._reconnecting = false;
      }
    }, 5 * 60 * 1000);

    // ── Telegram command interface ──
    if (telegram?.enabled) {
      telegram.setDataProviders({
        getRisk: () => riskEngine,
        getTracker: () => walletTracker,
        getBalance: async () => clobClient?.getUSDCBalance() ?? null,
        getMonitor: () => monitor,
        getSignal: () => signal,
        getScheduler: () => scheduler
      });
      telegram.startCommandPolling(5000);
    }

    // ── WebSocket periodic push (replaces frontend polling) ──
    wsPushInterval = setInterval(async () => {
      if (wsClients.size === 0) return;
      try {
        for (const [ws, info] of wsClients) {
          if (ws.readyState !== 1) continue;
          await wsPushPageData(ws, info.page);
        }
      } catch (e) { log('warn', 'WS periodic push error', { error: e.message }); }
    }, 3000);

    wsWhaleInterval = setInterval(async () => {
      if (wsClients.size === 0) return;
      try {
        const data = getWhaleAccStatus();
        if (data) wsBroadcast('whales', data);
      } catch (e) {}
    }, 30000);

    startLagDetector();
    log('info', 'All systems initialized');
    return true;
  } catch (e) {
    log('error', 'System init failed', { error: e.message, stack: e.stack?.slice(0, 300) });
    return false;
  }
}

async function shutdownSystems() {
  // Cancel all pending CLOB orders before shutting down
  if (clobClient?.isReady()) {
    try {
      log('info', 'Graceful shutdown: cancelling all open orders...');
      await clobClient.cancelAll();
      log('info', 'All open orders cancelled');
    } catch (e) {
      log('warn', 'Failed to cancel orders on shutdown: ' + e.message);
    }
  }

  // Persist monitor wallets before stopping (so they survive restart)
  try { monitor?.persistWallets(); } catch (e) {}
  try { persistAccumulator(); } catch (e) {}  // save accumulator before shutdown
  try { stopWhaleAccumulator(); } catch (e) {}
  try { walletLifecycle?.stop(); } catch (e) {}
  try { walletTracker?.stop(); } catch (e) {}
  try { exitEngine?.stop(); } catch (e) {}
  try { scheduler?.stop(); } catch (e) {}
  try { monitor?.stop(); } catch (e) {}
  try { signal?.shutdown(); } catch (e) {}
  try { riskEngine?.shutdown(); } catch (e) {}
  try { rateLimiter?.shutdown(); } catch (e) {}
  try { telegram?.shutdown(); } catch (e) {}
  try { polyWs?.shutdown(); } catch (e) {}
  try { newsSignal?.stop(); } catch (e) {}
  try { externalSignals?.stop(); } catch (e) {}
  try { updownStrategy?.stop(); } catch (e) {}
  if (routeModules) { try { await routeModules.shutdownAll(); } catch (e) { console.error('routeModules shutdown error', e); } }
  try { marketMaker?.stop(); } catch (e) {}
  try { bundleArb?.stop(); } catch (e) {}
  try { auditTrail?.systemEvent('shutdown', {}); } catch (e) {}
  try { auditTrail?.close(); } catch (e) {}
  if (bankrollSyncInterval) { clearInterval(bankrollSyncInterval); bankrollSyncInterval = null; }
  if (clobReconnectInterval) { clearInterval(clobReconnectInterval); clobReconnectInterval = null; }
  if (inFlightCleanupInterval) { clearInterval(inFlightCleanupInterval); inFlightCleanupInterval = null; }
  if (dailyReconciliationInterval) { clearInterval(dailyReconciliationInterval); dailyReconciliationInterval = null; }
  if (wsPushInterval) { clearInterval(wsPushInterval); wsPushInterval = null; }
  if (wsWhaleInterval) { clearInterval(wsWhaleInterval); wsWhaleInterval = null; }
  if (wss) {
    for (const [ws] of wsClients) { try { ws.close(); } catch (e) {} }
    wsClients.clear();
    try { wss.close(); } catch (e) {}
    wss = null;
  }
  _inFlightOrders.clear();
  try { dbModule?.stopBackupRotation(); } catch (e) {}
  try { dbModule?.flushSync(); } catch (e) {}
  log('info', 'All systems shut down');

  // Null all references so initSystems creates fresh instances on restart
  scheduler = null;
  exitEngine = null;
  walletLifecycle = null;
  walletTracker = null;
  shadowTrader = null;
  clobClient = null;
  clobReady = false;
  polyWs = null;
  newsSignal = null;
  externalSignals = null;
  updownStrategy = null;
  routeModules = null;
  marketMaker = null;
  bundleArb = null;
  monitor = null;
  signal = null;
  riskEngine = null;
  rateLimiter = null;
  telegram = null;
  auditTrail = null;
  notifier = null;
  analytics = null;
  // Reset accumulator in-memory state for clean restart
  whaleAcc.wallets = new Map();
  whaleAcc.seenIds = new Set();
  whaleAcc.totalScanned = 0;
  whaleAcc.lastPoll = null;
  // dbModule is kept — it's a stateless module, safe to reuse
}

function getVersion() {
  try { return require('./package.json').version; } catch (e) { return 'unknown'; }
}

// ── Auth middleware ──────────────────────────────────────────────────

function authMiddleware(req, res, next) {
  // Skip auth for static files and the root page
  if (!req.path.startsWith('/api/')) return next();

  // Localhost-only app — allow all local requests for read endpoints
  // Sensitive write endpoints use requireAuth() individually
  return next();
}

/**
 * Require auth token for sensitive endpoints.
 * Returns true if authorized, false (and sends 401) if not.
 *
 * The HTTP server binds to 127.0.0.1 only (see server.listen below) and CORS
 * is locked to same-origin, so every incoming connection is guaranteed local.
 * The Electron shell never actually delivers the session token to the
 * renderer (main.js loads '/' without ?_token=), so token-based auth would
 * block all write endpoints. Trust localhost connections instead.
 */
function requireAuth(req, res) {
  const remote = req.socket?.remoteAddress || req.ip || '';
  const isLocalhost =
    remote === '127.0.0.1' ||
    remote === '::1' ||
    remote === '::ffff:127.0.0.1';
  if (isLocalhost) return true;

  const token = req.headers['x-auth-token'] || req.headers['x-app-token'] || req.query.token;
  if (!token || token !== authToken) {
    res.status(401).json({ success: false, error: 'Unauthorized' });
    return false;
  }
  return true;
}

// ── App factory ─────────────────────────────────────────────────────

function createApp() {
  const a = express();

  // Restricted CORS — only allow same-origin and Electron on exact port.
  // Wrapped in an outer middleware so the origin callback can read req.method:
  // the no-origin bypass (for Electron, curl, same-origin GETs) is now limited
  // to safe methods only. Cross-origin writes always require a valid Origin
  // header that matches the allowlist, even if the attacker tries to suppress
  // it via fetch mode tricks.
  const ALLOWED_ORIGINS = ['http://localhost:3000', 'http://127.0.0.1:3000'];
  const SAFE_METHODS = new Set(['GET', 'HEAD', 'OPTIONS']);
  a.use((req, res, next) => {
    cors({
      origin: (origin, callback) => {
        if (!origin) {
          // No Origin header — only allowed for safe (read) methods.
          // Electron and curl GETs work; cross-origin POSTs without an Origin
          // header are rejected.
          if (SAFE_METHODS.has(req.method)) return callback(null, true);
          return callback(new Error('CORS: missing origin on write'));
        }
        if (ALLOWED_ORIGINS.includes(origin)) return callback(null, true);
        callback(new Error('CORS: origin not allowed'));
      },
      credentials: true
    })(req, res, next);
  });

  a.use(express.json({ limit: '10mb' }));
  a.use(authMiddleware);
  a.use(express.static(path.join(__dirname, 'src'), { index: false }));

  a.get('/', (req, res) => {
    // Inject auth token directly into the page so fetch() can use it as a header
    const token = req.query._token || '';
    const htmlPath = path.join(__dirname, 'src', 'index.html');
    let html;
    try { html = require('fs').readFileSync(htmlPath, 'utf8'); } catch (e) {
      return res.status(500).send('Failed to load UI');
    }
    // Inject token as a global variable before </head>
    const injection = `<script>window.__APP_TOKEN__="${token}";</script>`;
    html = html.replace('</head>', injection + '</head>');
    res.setHeader('Content-Type', 'text/html');
    res.setHeader('Cache-Control', 'no-store, no-cache, must-revalidate');
    res.send(html);
  });

  // ── Polymarket APIs ─────────────────────────────────────────────

  a.get('/api/markets', async (req, res) => {
    try {
      if (rateLimiter && !rateLimiter.consume('polymarket_data')) {
        return res.status(429).json({ success: false, error: 'Rate limited' });
      }
      const r = await axios.get(`${GAMMA}/markets`, { params: { limit: 50, active: true, closed: false, order: 'volume', ascending: false }, timeout: 10000 });
      if (rateLimiter) rateLimiter.clearBackoff('polymarket_data');
      log('info', 'Markets OK', { count: r.data?.length });
      res.json({ success: true, data: r.data });
    } catch (e) {
      if (rateLimiter && e.response?.status === 429) rateLimiter.reportRateLimit('polymarket_data');
      log('error', 'Markets failed', { error: e.message });
      res.status(500).json({ success: false, error: e.message });
    }
  });

  a.get('/api/leaderboard', async (req, res) => {
    // If accumulator has meaningful data, serve that — much richer than a one-shot sample
    if (whaleAcc.wallets.size >= 10) {
      const sortBy = req.query.sort || 'volume';
      const results = getWhaleResults(0, 100).sort((a, b) =>
        sortBy === 'trades' ? b.trades - a.trades : b.volume - a.volume
      );
      return res.json({
        success: true,
        data: results,
        accStatus: { wallets: whaleAcc.wallets.size, tradesScanned: whaleAcc.totalScanned, since: whaleAcc.started }
      });
    }

    // Fallback: fresh fetch from /trades (first few seconds before accumulator has data)
    try {
      if (rateLimiter && !rateLimiter.consume('polymarket_data')) {
        return res.status(429).json({ success: false, error: 'Rate limited' });
      }
      const r = await axios.get(`${DATA}/trades`, { params: { limit: 500 }, timeout: 12000 });
      if (rateLimiter) rateLimiter.clearBackoff('polymarket_data');
      const trades = r.data || [];

      const wallets = {};
      for (const t of trades) {
        const addr = t.proxyWallet;
        if (!addr) continue;
        if (!wallets[addr]) {
          wallets[addr] = { address: addr, name: t.name || t.pseudonym || addr.slice(0, 8) + '...', pseudonym: t.pseudonym || '', trades: 0, volume: 0, buys: 0, sells: 0, markets: new Set() };
        }
        const w = wallets[addr];
        w.trades++;
        const notional = parseFloat(t.usdcSize || 0) || (parseFloat(t.size || 0) * parseFloat(t.price || 0));
        w.volume += notional;
        if ((t.side || '').toUpperCase() === 'BUY') w.buys++; else w.sells++;
        if (t.title || t.question) w.markets.add((t.title || t.question).slice(0, 60));
      }

      const leaderboard = Object.values(wallets)
        .sort((a, b) => b.volume - a.volume).slice(0, 100)
        .map(w => ({ address: w.address, name: w.name, pseudonym: w.pseudonym, trades: w.trades, volume: +w.volume.toFixed(2), buys: w.buys, sells: w.sells, marketCount: w.markets.size, avgSize: w.trades > 0 ? +(w.volume / w.trades).toFixed(2) : 0, buyPct: w.trades > 0 ? Math.round((w.buys / w.trades) * 100) : 0 }));

      log('info', 'Leaderboard fallback from trades', { count: leaderboard.length });
      res.json({ success: true, data: leaderboard });
    } catch (e) {
      if (rateLimiter && e.response?.status === 429) rateLimiter.reportRateLimit('polymarket_data');
      log('error', 'Leaderboard failed', { error: e.message });
      res.status(500).json({ success: false, error: e.message });
    }
  });

  // Whale-specific endpoint — wallets filtered by accumulated volume
  a.get('/api/whales', (req, res) => {
    const minVolume = parseFloat(req.query.minVolume || 0);
    const limit = Math.min(parseInt(req.query.limit, 10) || 100, 500);
    const data = getWhaleResults(minVolume, limit);
    res.json({ success: true, data, status: getWhaleAccStatus() });
  });

  a.get('/api/whales/status', (req, res) => {
    res.json({ success: true, data: getWhaleAccStatus() });
  });

  // ── Wallet tracker endpoints (win rate, recommendations) ─────────
  a.get('/api/tracker/status', (req, res) => {
    res.json({ success: true, data: walletTracker?.getStatus() || { running: false } });
  });

  a.get('/api/tracker/wallet/:address', (req, res) => {
    if (!walletTracker) return res.json({ success: false, error: 'Tracker not running' });
    const stats = walletTracker.getWalletStats(req.params.address);
    if (!stats) return res.json({ success: false, error: 'Wallet not tracked' });
    const marketStats = walletTracker.getWalletMarketStats(req.params.address);
    res.json({ success: true, data: { stats, marketStats } });
  });

  a.get('/api/tracker/top', (req, res) => {
    if (!walletTracker) return res.json({ success: false, data: [] });
    const count = Math.min(parseInt(req.query.count, 10) || 3, 20);
    const marketFilter = req.query.market || null;
    const top = walletTracker.getTopWallets(count, { marketFilter });
    res.json({ success: true, data: top });
  });

  // Batch win-rate lookup for leaderboard — returns { address: { h24, d3, d7, d30 } }
  a.post('/api/tracker/batch-stats', (req, res) => {
    if (!walletTracker) return res.json({ success: true, data: {} });
    const addresses = req.body.addresses || [];
    const result = {};
    for (const addr of addresses.slice(0, 200)) {
      const stats = walletTracker.getWalletStats(addr);
      if (stats) {
        result[addr] = {
          h24: { wins: stats.h24.wins, losses: stats.h24.losses, winRate: stats.h24.winRate, resolved: stats.h24.resolvedTrades, pnl: stats.h24.pnl },
          d3:  { wins: stats.d3.wins,  losses: stats.d3.losses,  winRate: stats.d3.winRate,  resolved: stats.d3.resolvedTrades, pnl: stats.d3.pnl },
          d7:  { wins: stats.d7.wins,  losses: stats.d7.losses,  winRate: stats.d7.winRate,  resolved: stats.d7.resolvedTrades, pnl: stats.d7.pnl },
          d30: { wins: stats.d30.wins, losses: stats.d30.losses, winRate: stats.d30.winRate, resolved: stats.d30.resolvedTrades, pnl: stats.d30.pnl }
        };
      }
    }
    res.json({ success: true, data: result });
  });

  a.get('/api/recommendations', (req, res) => {
    const recs = scheduler?.getRecommendations() || null;
    const top = walletTracker?.getTopWallets(
      parseInt(req.query.count, 10) || 3,
      { marketFilter: req.query.market || null }
    ) || [];
    res.json({ success: true, data: { lastAuto: recs, current: top } });
  });

  a.post('/api/recommendations/activate', (req, res) => {
    const { address } = req.body;
    if (!address || !monitor || !walletTracker) {
      return res.status(400).json({ success: false, error: 'Invalid request' });
    }
    const stats = walletTracker.getWalletStats(address);
    const bestWr = Math.max(stats?.d7?.winRate || 0, stats?.d3?.winRate || 0);
    const accData = whaleAcc.wallets.get(address);

    if (!monitor.wallets.has(address)) {
      monitor.watch(address, `Manual ${address.slice(0, 8)}...`, {
        winRate: bestWr,
        volume: accData?.volume || 0,
        autoCopy: true,
        estimatedPortfolio: accData?.volume || 0
      });
    } else {
      const w = monitor.wallets.get(address);
      w.autoCopy = true;
      w.winRate = bestWr;
    }
    res.json({ success: true, message: `Activated ${address.slice(0, 12)}... (win rate: ${bestWr}%)` });
  });

  a.get('/api/balance', async (req, res) => {
    if (!clobClient) return res.json({ success: false, error: 'CLOB client not initialized' });
    const balance = await clobClient.getUSDCBalance();
    const bankroll = getDB()?.getSetting('risk_bankroll', 500) || 500;
    res.json({ success: true, data: { usdcBalance: balance, bankroll, synced: balance !== null } });
  });

  a.post('/api/tracker/track', (req, res) => {
    const { address } = req.body;
    if (!address || !walletTracker) return res.status(400).json({ success: false, error: 'Invalid address' });
    walletTracker.trackWallet(address);
    res.json({ success: true, message: `Now tracking ${address}` });
  });

  a.get('/api/trades/:address', async (req, res) => {
    try {
      if (rateLimiter && !rateLimiter.consume('polymarket_data')) {
        return res.status(429).json({ success: false, error: 'Rate limited' });
      }
      const r = await axios.get(`${DATA}/trades`, { params: { user: req.params.address, limit: 20 }, timeout: 10000 });
      if (rateLimiter) rateLimiter.clearBackoff('polymarket_data');
      res.json({ success: true, data: r.data });
    } catch (e) {
      if (rateLimiter && e.response?.status === 429) rateLimiter.reportRateLimit('polymarket_data');
      res.status(500).json({ success: false, error: e.message });
    }
  });

  // ── Trade execution (with dry run + audit) ────────────────────────

  a.post('/api/trade', async (req, res) => {
    const { tokenId, side, size, price, market, copied_from, copied_from_address, copied_from_win_rate, copied_from_volume } = req.body;

    // Rate limit trade execution
    if (rateLimiter && !rateLimiter.consume('polymarket_clob')) {
      return res.status(429).json({ success: false, error: 'Trade rate limited — too many orders' });
    }

    const finalSize = parseFloat(size) || 0;
    const finalPrice = parseFloat(price) || 0;
    if (finalSize <= 0) return res.status(400).json({ success: false, error: 'Invalid size' });

    // Input validation — prevent malformed orders (H1 security fix)
    if (finalPrice < 0.01 || finalPrice > 0.99) {
      return res.status(400).json({ success: false, error: `Invalid price $${finalPrice} — must be between $0.01 and $0.99` });
    }
    const validSides = ['YES', 'NO', 'BUY', 'SELL'];
    if (!validSides.includes((side || '').toUpperCase())) {
      return res.status(400).json({ success: false, error: `Invalid side "${side}" — must be YES, NO, BUY, or SELL` });
    }
    // Hard cap: no single trade > $500 regardless of risk engine
    if (finalSize > 500) {
      return res.status(400).json({ success: false, error: `Size $${finalSize} exceeds hard cap of $500` });
    }

    // Risk engine check
    const rsk = getRisk();
    let adjustedSize = finalSize;
    if (rsk) {
      const check = rsk.checkTrade({ market, side, size: finalSize, price, copied_from, copied_from_win_rate, copied_from_volume });
      if (!check.allowed) {
        log('warn', 'Trade blocked by risk engine', { reason: check.reason });
        return res.status(403).json({ success: false, blocked: true, reason: check.reason });
      }
      if (check.adjustSize) adjustedSize = check.adjustSize;
    }

    // Dry run mode
    const dryRun = rsk?.getConfig()?.dryRun || false;
    if (dryRun) {
      const d = getDB();
      let tradeId = null;
      if (d) {
        const r = d.logTrade({ market, side, price, size: adjustedSize, copied_from, status: 'dry_run', dry_run: true });
        tradeId = r.id;
      }
      if (auditTrail) auditTrail.dryRun({ market, side, size: adjustedSize, price, copied_from }, { mode: 'dry_run' });
      log('info', '[DRY RUN] Trade simulated', { side, size: adjustedSize, price, market });

      // Resolve conditionId via request body or Gamma API (strict match only)
      let dryConditionId = req.body.conditionId || null;
      if (!dryConditionId && market && (!rateLimiter || rateLimiter.consume('polymarket_data'))) {
        try {
          const searchTitle = market.replace(/[^a-zA-Z0-9 ]/g, ' ').slice(0, 60).trim();
          const gammaR = await axios.get('https://gamma-api.polymarket.com/markets', {
            params: { title: searchTitle, limit: 5 },
            timeout: 5000
          });
          // STRICT match — must match the exact question, no random fallback
          const titleLower = market.toLowerCase().trim();
          const match = gammaR.data?.find(m => (m.question || '').toLowerCase().trim() === titleLower);
          if (match) dryConditionId = match.condition_id;
        } catch (e) { /* best effort */ }
      }

      // Register dry-run position with risk engine so resolution watcher can track it
      try {
        const riskEngine = getRisk();
        if (riskEngine) {
          const dryId = `dry_${tradeId || Date.now()}`;
          riskEngine.openPosition({
            id: dryId, tradeId, market, side, size: adjustedSize, price,
            conditionId: dryConditionId,
            tokenId: req.body.tokenId || null,
            copied_from, copied_from_address: req.body.copied_from_address,
            dryRun: true
          });
          log('info', '[DRY RUN] Position registered for resolution tracking', { dryId, market, conditionId: dryConditionId });
        }
      } catch (e) { log('warn', '[DRY RUN] Failed to register position with risk engine', { error: e.message }); }

      return res.json({ success: true, dryRun: true, tradeId, message: 'Dry run — trade not executed' });
    }

    // CLOB client required for live trading
    if (!clobClient?.isReady()) {
      return res.status(503).json({ success: false, error: 'CLOB client not ready — configure credentials on Connect page' });
    }

    // Resolve token ID if not provided
    let resolvedTokenId = tokenId;
    let tickSize = req.body.tickSize || '0.01';
    let negRisk = req.body.negRisk || false;
    let conditionId = req.body.conditionId || null;

    if (!resolvedTokenId && market) {
      const tokens = await clobClient.resolveTokenIds(market);
      if (!tokens) return res.status(400).json({ success: false, error: 'Could not resolve token ID for this market' });
      resolvedTokenId = side === 'YES' || side === 'BUY' ? tokens.yesTokenId : tokens.noTokenId;
      tickSize = tokens.tickSize;
      negRisk = tokens.negRisk;
      conditionId = tokens.conditionId;
    }

    // In-flight duplicate check
    const flightKey = `${market}::${side}`;
    const flightTs = _inFlightOrders.get(flightKey);
    if (flightTs && Date.now() - flightTs < 30000) {
      return res.status(409).json({ error: 'Order already in-flight for this market/side' });
    }
    _inFlightOrders.set(flightKey, Date.now());

    // Idempotency: check for duplicate in-flight orders on the same market
    const riskEngine = getRisk();
    if (riskEngine) {
      const existingPos = (riskEngine.state?.openPositions || []).find(
        p => p.market === market && !p.dryRun && (Date.now() - new Date(p.openedAt || 0).getTime()) < 60000
      );
      if (existingPos) {
        _inFlightOrders.delete(flightKey);
        log('warn', 'Duplicate trade blocked — position already opening on this market', { market, existingId: existingPos.id });
        return res.status(409).json({ success: false, error: 'Duplicate trade blocked — position already exists for this market' });
      }
    }

    // Convert USD size to shares (CLOB expects shares, not USD)
    // Bug #6 from CLAUDE.md: shares = Math.floor(usdSize / price)
    const orderPrice = parseFloat(price) || 0;
    const sharesSize = orderPrice > 0 ? Math.floor(adjustedSize / orderPrice) : 0;
    if (sharesSize <= 0) {
      _inFlightOrders.delete(flightKey);
      return res.status(400).json({ success: false, error: `Cannot compute shares: $${adjustedSize} at price $${orderPrice}` });
    }

    // Re-validate market is still active before placing order
    if (clobClient && conditionId) {
      try {
        const stillActive = await clobClient.isMarketActive(conditionId);
        if (!stillActive) {
          _inFlightOrders.delete(flightKey);
          return res.status(409).json({ error: 'Market no longer active at execution time' });
        }
      } catch (e) {
        log('warn', 'Market re-validation failed, proceeding with caution', { error: e.message });
      }
    }

    // Place order via CLOB client FIRST, then log to DB on success
    // (prevents orphaned DB entries on CLOB failure)
    let result;
    try {
      result = await clobClient.placeOrder(resolvedTokenId, 'BUY', price, sharesSize, {
        tickSize, negRisk, orderType: req.body.orderType || 'GTC'
      });
    } catch (e) {
      _inFlightOrders.delete(flightKey);
      log('error', 'Trade placement threw', { error: e.message });
      return res.status(500).json({ success: false, error: e.message });
    } finally {
      _inFlightOrders.delete(flightKey);
    }

    if (result.success) {
      // Log to DB AFTER successful CLOB placement
      let tradeId = null;
      try {
        const d = getDB();
        if (d) {
          const r = d.logTrade({ market, side, price, size: adjustedSize, copied_from, status: 'open', order_id: result.orderId });
          tradeId = r.id;
        }
      } catch (e) { log('warn', 'Failed to log trade to DB', { error: e.message }); }

      try {
        getRisk()?.openPosition({
          id: result.orderId || tradeId || Date.now(), tradeId, market, side, size: adjustedSize, price,
          tokenId: resolvedTokenId, tickSize, negRisk, conditionId,
          copied_from, copied_from_address
        });
      } catch (e) {}
      if (auditTrail) auditTrail.tradeExecute({ market, side, size: adjustedSize, price, copied_from }, result.data);
      log('info', 'Trade executed via CLOB', { side, size: adjustedSize, price, market, orderId: result.orderId });
      res.json({ success: true, orderId: result.orderId, data: result.data, tradeId });
    } else {
      if (auditTrail) auditTrail.tradeExecute({ market, side, size: adjustedSize, price, copied_from }, { error: result.error });
      log('error', 'Trade failed', { error: result.error });
      res.status(500).json({ success: false, error: result.error });
    }
  });

  // ── API key validation ────────────────────────────────────────────

  a.post('/api/validate-key', async (req, res) => {
    const { apiKey, type } = req.body;
    if (!apiKey) return res.status(400).json({ success: false, error: 'No API key provided' });

    if (type === 'polymarket') {
      try {
        const r = await axios.get(`${CLOB}/auth/api-keys`, {
          headers: { 'Authorization': `Bearer ${apiKey}` },
          timeout: 8000
        });
        res.json({ success: true, valid: true, message: 'Polymarket API key is valid' });
      } catch (e) {
        const status = e.response?.status;
        if (status === 401 || status === 403) {
          res.json({ success: true, valid: false, message: 'Invalid API key' });
        } else {
          res.json({ success: true, valid: null, message: 'Could not verify — API may be down' });
        }
      }
    } else {
      res.status(400).json({ success: false, error: 'Unknown key type' });
    }
  });

  // ── Risk management API ───────────────────────────────────────────

  a.get('/api/risk/status', (req, res) => {
    try { res.json({ success: true, data: getRisk()?.getStatus() || { enabled: false, error: 'Risk engine not loaded' } }); }
    catch (e) { res.status(500).json({ success: false, error: e.message }); }
  });

  a.post('/api/risk/pause', (req, res) => {
    try { getRisk()?.pause(req.body.reason || 'manual'); res.json({ success: true, message: 'Trading paused' }); }
    catch (e) { res.status(500).json({ success: false, error: e.message }); }
  });

  a.post('/api/risk/resume', (req, res) => {
    try { getRisk()?.resume(); res.json({ success: true, message: 'Trading resumed' }); }
    catch (e) { res.status(500).json({ success: false, error: e.message }); }
  });

  a.post('/api/risk/config', (req, res) => {
    if (!requireAuth(req, res)) return;
    try {
      const r = getRisk();
      if (!r) return res.status(500).json({ success: false, error: 'Risk engine not available' });

      // Safety guard: block switching to live if circuit breaker is active
      if (req.body.dryRun === false || req.body.dryRun === 'false' || req.body.dryRun === 0) {
        const status = r.getStatus();
        if (status.circuitBreakerActive) {
          const remaining = Math.round((status.circuitBreakerUntil - Date.now()) / 60000);
          return res.status(400).json({
            success: false,
            error: `Cannot switch to LIVE mode: circuit breaker is active (${remaining} min remaining after ${status.consecutiveLosses} consecutive losses). Reset the circuit breaker first.`
          });
        }
      }

      const results = {};
      for (const [k, v] of Object.entries(req.body)) {
        results[k] = r.setSetting(k, v);
      }
      res.json({ success: true, message: 'Risk config updated', results, config: r.getConfig() });
    } catch (e) { res.status(500).json({ success: false, error: e.message }); }
  });

  a.post('/api/risk/record-result', (req, res) => {
    try { getRisk()?.recordResult(req.body.tradeId, parseFloat(req.body.pnl)); res.json({ success: true }); }
    catch (e) { res.status(500).json({ success: false, error: e.message }); }
  });

  // ── Persistence APIs (using public settings whitelist) ────────────

  a.get('/api/db/watchlist', (req, res) => {
    try { res.json({ success: true, data: getDB()?.getWatchlist() || [] }); }
    catch (e) { res.status(500).json({ success: false, error: e.message }); }
  });

  a.post('/api/db/watchlist', (req, res) => {
    try { res.json(getDB()?.addToWatchlist(req.body) || { success: false, error: 'DB not available' }); }
    catch (e) { res.status(500).json({ success: false, error: e.message }); }
  });

  a.put('/api/db/watchlist/:id', (req, res) => {
    try { res.json(getDB()?.updateWatchlistTrader(req.params.id, req.body) || { success: false }); }
    catch (e) { res.status(500).json({ success: false, error: e.message }); }
  });

  a.delete('/api/db/watchlist/:id', (req, res) => {
    try { res.json(getDB()?.removeFromWatchlist(req.params.id) || { success: false }); }
    catch (e) { res.status(500).json({ success: false, error: e.message }); }
  });

  a.get('/api/db/pinned', (req, res) => {
    try { res.json({ success: true, data: getDB()?.getPinnedMarkets() || [] }); }
    catch (e) { res.status(500).json({ success: false, error: e.message }); }
  });

  a.post('/api/db/pinned', (req, res) => {
    try { res.json(getDB()?.addPinnedMarket(req.body) || { success: false }); }
    catch (e) { res.status(500).json({ success: false, error: e.message }); }
  });

  a.delete('/api/db/pinned/:id', (req, res) => {
    try { res.json(getDB()?.removePinnedMarket(req.params.id) || { success: false }); }
    catch (e) { res.status(500).json({ success: false, error: e.message }); }
  });

  a.get('/api/db/trades', (req, res) => {
    try {
      const limit = Math.min(Math.max(1, parseInt(req.query.limit, 10) || 50), 500);
      res.json({ success: true, data: getDB()?.getTradeHistory(limit) || [], stats: getDB()?.getTradeStats() || {} });
    } catch (e) { res.status(500).json({ success: false, error: e.message }); }
  });

  a.get('/api/dashboard/stats', (req, res) => {
    try {
      const db = getDB();
      if (!db) return res.json({ success: true, data: {} });
      // getAllTrades — getTradeHistory(500) cap silently truncates 7d/all-time.
      const all = db.getAllTrades();
      const now = Date.now();
      const h24 = now - 24 * 60 * 60 * 1000;
      const d7  = now - 7  * 24 * 60 * 60 * 1000;

      function calcStats(trades) {
        const closed = trades.filter(t => (t.status === 'closed' || t.status === 'won' || t.status === 'lost') && t.pnl != null);
        if (!closed.length) return { count: 0, wins: 0, losses: 0, pnl: 0, avgPnl: 0, winRate: 0 };
        const pnls = closed.map(t => t.pnl);
        const pnl = pnls.reduce((s, p) => s + p, 0);
        const wins = pnls.filter(p => p > 0).length;
        return {
          count: closed.length, wins, losses: closed.length - wins,
          pnl: +pnl.toFixed(2),
          avgPnl: +(pnl / closed.length).toFixed(2),
          winRate: +((wins / closed.length) * 100).toFixed(1)
        };
      }

      const d30 = now - 30 * 24 * 60 * 60 * 1000;
      const trades24h = all.filter(t => new Date(t.executed_at).getTime() >= h24);
      const trades7d  = all.filter(t => new Date(t.executed_at).getTime() >= d7);
      const trades30d = all.filter(t => new Date(t.executed_at).getTime() >= d30);
      const tradesSession = all.filter(t => new Date(t.executed_at).getTime() >= _serverStartedAt);
      const openTrades = all.filter(t => t.status === 'open');

      // 7d notional volume — sum of trade.size across last 7 days (all statuses).
      const volume7d = +trades7d.reduce((s, t) => s + (parseFloat(t.size) || 0), 0).toFixed(2);

      // Deployed $ across open positions
      const deployedOpen = +openTrades.reduce((s, t) => s + (parseFloat(t.size) || 0), 0).toFixed(2);

      // System-wide Sharpe over 30d, computed from per-day P&L stream.
      // Sharpe = mean(daily_pnl) / stdev(daily_pnl) * sqrt(365). risk_free = 0.
      // Returns null if fewer than 5 days of closed trades exist.
      function calcSharpe30d(trades) {
        const closed = trades.filter(t => (t.status === 'closed' || t.status === 'won' || t.status === 'lost') && t.pnl != null);
        if (closed.length < 5) return null;
        const byDay = {};
        for (const t of closed) {
          const day = new Date(t.executed_at).toISOString().slice(0, 10);
          byDay[day] = (byDay[day] || 0) + (parseFloat(t.pnl) || 0);
        }
        const dailyPnls = Object.values(byDay);
        if (dailyPnls.length < 5) return null;
        const mean = dailyPnls.reduce((s, v) => s + v, 0) / dailyPnls.length;
        const variance = dailyPnls.reduce((s, v) => s + (v - mean) * (v - mean), 0) / dailyPnls.length;
        const stdev = Math.sqrt(variance);
        if (stdev === 0) return null;
        return +((mean / stdev) * Math.sqrt(365)).toFixed(2);
      }
      const sharpe30d = calcSharpe30d(trades30d);

      // Session card: count/wins/winRate/avgPnl from trades since server start.
      // pnl prefers risk.sessionPnL (running counter), falls back to closed sum.
      const riskStatus = getRisk()?.getStatus?.() || {};
      const sessionStats = calcStats(tradesSession);
      const sessionPnl = riskStatus.sessionPnL ?? sessionStats.pnl;

      res.json({
        success: true,
        data: {
          session: { ...sessionStats, pnl: sessionPnl },
          h24:  calcStats(trades24h),
          d7:   calcStats(trades7d),
          all:  calcStats(all),
          openPositions: openTrades.length,
          deployedOpen,
          volume7d,
          sharpe30d,
          winStreak: riskStatus.systemWinStreak ?? 0,
          bestWinStreak: riskStatus.bestWinStreak ?? 0,
          dryRun: riskStatus.dryRun ?? db.getSetting('risk_dryRun', true),
          paused: riskStatus.paused ?? false,
          pauseReason: riskStatus.pauseReason ?? null,
          consecutiveLosses: riskStatus.consecutiveLosses ?? 0,
          circuitBreakerActive: riskStatus.circuitBreakerActive ?? false,
          circuitBreakerEnabled: db.getSetting('risk_circuitBreakerEnabled', true),
          circuitBreakerUntil: riskStatus.circuitBreakerUntil ?? null
        }
      });
    } catch (e) { res.status(500).json({ success: false, error: e.message }); }
  });

  a.get('/api/db/settings', (req, res) => {
    try {
      const data = cachedJson('db_settings', 500, () => getDB()?.getAllSettings() || {});
      res.json({ success: true, data });
    }
    catch (e) { res.status(500).json({ success: false, error: e.message }); }
  });

  a.post('/api/db/settings', (req, res) => {
    if (!requireAuth(req, res)) return;
    try {
      const { key, value } = req.body;
      const db = getDB();
      if (!db) return res.status(500).json({ success: false, error: 'DB not available' });
      // Use public whitelist to prevent writing sensitive keys
      const result = db.setPublicSetting(key, value);
      if (result && result.error) return res.status(403).json({ success: false, error: result.error });
      if (auditTrail) auditTrail.configChange(key, value, 'api');
      res.json({ success: true });
    } catch (e) { res.status(500).json({ success: false, error: e.message }); }
  });

  // Dedicated credential save endpoint — uses setSettingInternal (bypasses public whitelist)
  // Only allows known credential keys to prevent arbitrary internal writes.
  a.post('/api/connect/credentials', (req, res) => {
    if (!requireAuth(req, res)) return;
    try {
      const { key, value } = req.body;
      const db = getDB();
      if (!db) return res.status(500).json({ success: false, error: 'DB not available' });

      const ALLOWED_CREDENTIAL_KEYS = [
        'private_key', 'wallet_address', 'polymarket_api_key',
        'api_secret', 'polymarket_passphrase', 'polymarket_funder_address'
      ];
      if (!ALLOWED_CREDENTIAL_KEYS.includes(key)) {
        return res.status(403).json({ success: false, error: `Key '${key}' is not a valid credential key` });
      }
      if (!value || typeof value !== 'string' || value.trim().length === 0) {
        return res.status(400).json({ success: false, error: 'Value must be a non-empty string' });
      }

      db.setSettingInternal(key, value.trim());
      // Do NOT log the actual value of sensitive credentials
      if (auditTrail) auditTrail.configChange(key, '(redacted)', 'connect-ui');
      log('info', `Credential saved: ${key}`);
      res.json({ success: true });
    } catch (e) {
      // Surface the real error so silent failures (e.g. missing db helper)
      // don't masquerade as generic save errors. Safe to log: the error is a
      // call-stack/type message, not a credential value.
      log('error', `Credential save failed: ${e.message}`);
      res.status(500).json({ success: false, error: `Failed to save credential: ${e.message}` });
    }
  });

  a.get('/api/db/info', (req, res) => {
    try { res.json({ success: true, data: getDB()?.getDBInfo() || {} }); }
    catch (e) { res.status(500).json({ success: false, error: e.message }); }
  });

  a.get('/api/db/wallet-history/:address', (req, res) => {
    try { res.json({ success: true, data: getDB()?.getWalletHistory(req.params.address, parseInt(req.query.days, 10) || 30) || [] }); }
    catch (e) { res.status(500).json({ success: false, error: e.message }); }
  });

  a.get('/api/db/activity', (req, res) => {
    try { res.json({ success: true, data: getDB()?.getRecentActivity(req.query.wallet, parseInt(req.query.limit, 10) || 20) || [] }); }
    catch (e) { res.status(500).json({ success: false, error: e.message }); }
  });

  a.get('/api/logs', (req, res) => {
    try {
      const dbLogs = getDB()?.getEventLog(parseInt(req.query.limit, 10) || 100, req.query.level) || [];
      res.json({ success: true, logs: dbLogs.length ? dbLogs : getLogs() });
    } catch (e) { res.json({ success: true, logs: getLogs() }); }
  });

  // ── Monitor API ───────────────────────────────────────────────────

  a.get('/api/monitor/status', (req, res) => {
    res.json({ success: true, data: monitor?.getStatus() || { running: false } });
  });

  a.post('/api/monitor/watch', (req, res) => {
    const { address, name, winRate, volume, autoCopy, minPositionAlert } = req.body;
    if (!address) return res.status(400).json({ success: false, error: 'address required' });
    monitor?.watch(address, name, { winRate, volume, autoCopy, minPositionAlert });
    res.json({ success: true, message: `Watching ${name || address}` });
  });

  a.post('/api/monitor/unwatch', (req, res) => {
    monitor?.unwatch(req.body.address);
    res.json({ success: true });
  });

  a.post('/api/monitor/unpause', (req, res) => {
    monitor?.unpauseWallet(req.body.address);
    res.json({ success: true });
  });

  a.post('/api/monitor/start', (req, res) => {
    scheduler?.start();
    res.json({ success: true, message: 'Scheduler and monitor started' });
  });

  a.post('/api/monitor/stop', (req, res) => {
    scheduler?.stop();
    res.json({ success: true, message: 'Scheduler and monitor stopped' });
  });

  // ── Market Scanner API (bot detection) ────────────────────────────

  a.post('/api/scanner/start', (req, res) => {
    const { marketPattern, intervalMs } = req.body;
    if (!marketPattern) return res.status(400).json({ success: false, error: 'marketPattern required (e.g. "bitcoin up or down")' });
    const interval = Math.max(3000, parseInt(intervalMs, 10) || 5000);  // min 3 seconds
    monitor?.startScanner(marketPattern, interval);
    res.json({ success: true, message: `Scanner started for "${marketPattern}" every ${interval / 1000}s` });
  });

  a.post('/api/scanner/stop', (req, res) => {
    monitor?.stopScanner();
    res.json({ success: true, message: 'Scanner stopped' });
  });

  a.get('/api/scanner/status', (req, res) => {
    res.json({ success: true, data: monitor?.getScannerStatus() || { enabled: false } });
  });

  a.get('/api/scanner/results', (req, res) => {
    const minTrades = parseInt(req.query.minTrades, 10) || 2;
    const limit = Math.min(parseInt(req.query.limit, 10) || 50, 200);
    res.json({ success: true, data: monitor?.getScannerResults(minTrades, limit) || [] });
  });

  a.post('/api/scanner/watch-top', (req, res) => {
    const count = Math.min(parseInt(req.body.count, 10) || 3, 20);
    const autoCopy = req.body.autoCopy || false;
    const added = monitor?.watchTopScannerWallets(count, autoCopy) || [];
    res.json({ success: true, message: `Added ${added.length} bot wallets to watchlist`, data: added });
  });

  // ── Exit Engine + Resolution Watcher API ─────────────────────────

  a.get('/api/exit/status', (req, res) => {
    res.json({ success: true, data: exitEngine?.getStatus() || { running: false } });
  });

  a.post('/api/exit/start', (req, res) => {
    exitEngine?.start(parseInt(req.body.intervalMs, 10) || undefined);
    res.json({ success: true, message: 'Exit engine + resolution watcher started' });
  });

  a.post('/api/exit/stop', (req, res) => {
    exitEngine?.stop();
    res.json({ success: true, message: 'Exit engine stopped' });
  });

  // ── CLOB Client API ────────────────────────────────────────────────

  a.get('/api/clob/status', (req, res) => {
    res.json({ success: true, data: clobClient?.getStatus() || { ready: false, error: 'Not initialized' } });
  });

  a.post('/api/clob/reconnect', async (req, res) => {
    try {
      const ok = await clobClient?.initialize();
      res.json({ success: true, ready: ok, error: clobClient?.error || null });
    } catch (e) { res.status(500).json({ success: false, error: e.message }); }
  });

  a.get('/api/clob/open-orders', async (req, res) => {
    try {
      const orders = await clobClient?.getOpenOrders() || [];
      res.json({ success: true, data: orders });
    } catch (e) { res.status(500).json({ success: false, error: e.message }); }
  });

  a.post('/api/clob/cancel-all', async (req, res) => {
    if (!requireAuth(req, res)) return;
    try {
      const r = await clobClient?.cancelAll();
      res.json(r || { success: false });
    } catch (e) { res.status(500).json({ success: false, error: e.message }); }
  });

  // ── Analytics API ─────────────────────────────────────────────────

  a.get('/api/analytics/report', (req, res) => {
    try { res.json({ success: true, data: analytics?.getReport(parseInt(req.query.days, 10) || 30) || {} }); }
    catch (e) { res.status(500).json({ success: false, error: e.message }); }
  });

  a.get('/api/analytics/best-wallet', (req, res) => {
    try { res.json({ success: true, data: analytics?.getBestWallet() || null }); }
    catch (e) { res.status(500).json({ success: false, error: e.message }); }
  });

  a.get('/api/analytics/best-category', (req, res) => {
    try { res.json({ success: true, data: analytics?.getBestCategory() || null }); }
    catch (e) { res.status(500).json({ success: false, error: e.message }); }
  });

  // ── Signal engine API ─────────────────────────────────────────────

  a.get('/api/signal/status', (req, res) => {
    res.json({ success: true, data: signal?.getStatus() || { enabled: false } });
  });

  a.post('/api/signal/enable', (req, res) => {
    signal?.enable(); res.json({ success: true, message: 'Signal engine enabled' });
  });

  a.post('/api/signal/disable', (req, res) => {
    signal?.disable(); res.json({ success: true, message: 'Signal engine disabled' });
  });

  a.post('/api/signal/config', (req, res) => {
    if (!requireAuth(req, res)) return;
    try {
      const results = {};
      for (const [k, v] of Object.entries(req.body)) {
        results[k] = signal?.setSetting(k, v);
      }
      res.json({ success: true, results, config: signal?.getConfig() });
    } catch (e) { res.status(500).json({ success: false, error: e.message }); }
  });

  // ── Focused Wallets & Learning API ──────────────────────────────

  a.get('/api/signal/focused-wallets', (req, res) => {
    const focused = getDB()?.getSetting('signal_focusedWallets', []) || [];
    res.json({ success: true, data: focused });
  });

  a.post('/api/signal/focused-wallets', (req, res) => {
    try {
      const { wallets } = req.body;
      if (!Array.isArray(wallets)) return res.status(400).json({ success: false, error: 'wallets must be an array of addresses' });
      // Validate and normalize
      const cleaned = wallets.map(w => (w || '').toLowerCase().trim()).filter(w => w.length > 10);
      getDB()?.setSetting('signal_focusedWallets', cleaned);
      log('info', `Focused wallets updated: ${cleaned.length} wallets`, { wallets: cleaned.map(w => w.slice(0, 12) + '...') });
      // Also ensure these wallets are being tracked and watched
      for (const addr of cleaned) {
        if (walletTracker && !walletTracker.isTracking(addr)) walletTracker.trackWallet(addr);
        if (monitor && !monitor.wallets.has(addr)) {
          monitor.watch(addr, addr.slice(0, 8) + '...', { autoCopy: true, winRate: 0, volume: 0 });
        } else if (monitor?.wallets.has(addr)) {
          const w = monitor.wallets.get(addr);
          w.autoCopy = true; // Ensure auto-copy is on for focused wallets
        }
      }
      res.json({ success: true, focused: cleaned });
    } catch (e) { res.status(500).json({ success: false, error: e.message }); }
  });

  a.get('/api/signal/find-trusted', (req, res) => {
    if (!signal) return res.json({ success: false, error: 'Signal engine not available' });
    const count = parseInt(req.query.count, 10) || 3;
    const trusted = signal.findTrustedWallets(count);
    res.json({ success: true, data: trusted });
  });

  a.get('/api/signal/learn', (req, res) => {
    if (!signal) return res.json({ success: false, error: 'Signal engine not available' });
    const analysis = signal.analyzeTradePatterns();
    res.json({ success: true, data: analysis });
  });

  a.get('/api/signal/explain/:address', (req, res) => {
    if (!signal) return res.json({ success: false, error: 'Signal engine not available' });
    // Explain what a hypothetical trade from this wallet would look like
    const explanation = signal.explainTrade({
      wallet_address: req.params.address,
      price: parseFloat(req.query.price) || 0.5,
      size: parseFloat(req.query.size) || 100,
      side: req.query.side || 'YES',
      market: req.query.market || 'hypothetical'
    });
    res.json({ success: true, data: explanation });
  });

  a.get('/api/risk/drawdown', (req, res) => {
    if (!riskEngine) return res.json({ success: false, error: 'Risk engine not available' });
    res.json({ success: true, data: riskEngine.getDrawdownStatus() });
  });

  // R2: Directional heat map endpoint
  a.get('/api/risk/direction-heat', (req, res) => {
    try {
      const db = getDB();
      const heat = riskEngine?.state?.directionHeat || {};
      const bankroll = db.getSetting('risk_bankroll', 500);
      const formatted = {};
      for (const [cat, dirs] of Object.entries(heat)) {
        formatted[cat] = {};
        for (const [dir, size] of Object.entries(dirs)) {
          formatted[cat][dir] = {
            size: size.toFixed(2),
            pctOfBankroll: ((size / bankroll) * 100).toFixed(1) + '%'
          };
        }
      }
      res.json({ success: true, directionHeat: formatted, bankroll });
    } catch (err) {
      res.status(500).json({ success: false, error: err.message });
    }
  });

  // R3: Regime-switching risk model endpoint
  a.get('/api/risk/regime', (req, res) => {
    try {
      const ctx = scheduler?._marketContext || null;
      res.json({ marketContext: ctx, multipliers: riskEngine.getRegimeMultipliers(ctx) });
    } catch (err) {
      res.status(500).json({ error: err.message });
    }
  });

  // ── Strategy Engine API ──────────────────────────────────────────

  a.get('/api/strategies', (req, res) => {
    if (!strategyEngine) return res.json({ success: false, data: [] });
    res.json({ success: true, data: strategyEngine.getComparison() });
  });

  a.post('/api/strategies/register', (req, res) => {
    if (!strategyEngine) return res.status(500).json({ success: false, error: 'Strategy engine not available' });
    const { id, params } = req.body;
    if (!id || !params) return res.status(400).json({ success: false, error: 'Need id and params' });
    strategyEngine.register(id, params);
    res.json({ success: true, message: `Strategy ${id} registered` });
  });

  // ── Market Context & Intelligence API ─────────────────────────────

  a.get('/api/market/context', (req, res) => {
    res.json({ success: true, data: scheduler?.getMarketContext() || null });
  });

  // G3: Cross-dimensional P&L attribution (wallet × category × hour-of-day)
  a.get('/api/analytics/attribution', (req, res) => {
    try {
      const db = getDB();
      const attr = db.getSetting('pnl_attribution', null);
      if (!attr) return res.json({ message: 'No attribution data yet — runs after first trade resolves' });
      res.json(attr);
    } catch (err) {
      res.status(500).json({ error: err.message });
    }
  });

  // M5: Record market creator dispute data
  a.post('/api/market/creator-dispute', express.json(), (req, res) => {
    try {
      const db = getDB();
      const { marketPattern, disputed } = req.body;
      if (!marketPattern) return res.status(400).json({ error: 'marketPattern required' });
      const stats = db.getSetting('market_creator_stats', {});
      const key = marketPattern.toLowerCase().slice(0, 30);
      if (!stats[key]) stats[key] = { total: 0, disputes: 0 };
      stats[key].total++;
      if (disputed) stats[key].disputes++;
      db.setSetting('market_creator_stats', stats);
      res.json({ success: true, stats: stats[key] });
    } catch (err) {
      res.status(500).json({ error: err.message });
    }
  });

  a.get('/api/wallets/leader-follower', (req, res) => {
    const data = scheduler?.detectLeaderFollower() || [];
    res.json({ success: true, data });
  });

  // W8: Wallet poisoning anomaly flags
  a.get('/api/wallets/anomalies', (req, res) => {
    try {
      const db = getDB();
      const flags = db.getSetting('wallet_anomaly_flags', {});
      res.json({
        anomalies: Object.entries(flags).map(([addr, f]) => ({
          address: addr, reason: f.reason, detectedAt: new Date(f.detectedAt).toISOString()
        })),
        count: Object.keys(flags).length
      });
    } catch (err) {
      res.status(500).json({ error: err.message });
    }
  });

  a.get('/api/signal/learning-state', (req, res) => {
    const db = getDB();
    if (!signal) return res.json({ success: false, error: 'Signal engine not available' });
    const maeHistory = db?.getSetting('signal_maeHistory', {}) || {};
    // Summarise MAE per wallet: median MAE fraction
    const maeSummary = {};
    for (const [addr, entries] of Object.entries(maeHistory)) {
      if (!entries.length) continue;
      const fractions = entries.map(e => e.maeFraction || 0).sort((a, b) => a - b);
      const median = fractions[Math.floor(fractions.length / 2)];
      maeSummary[addr] = { n: entries.length, medianMaeFraction: +median.toFixed(4) };
    }
    res.json({
      success: true,
      data: {
        walletAdjustments: signal._walletConfidenceAdj || {},
        priceZoneResults: signal._priceZoneResults || null,
        strategyResults: riskEngine?.getDrawdownStatus()?.strategyResults || {},
        maeByWallet: maeSummary,
        rejectedSignalAudit: db?.getSetting('signal_rejectedSignalAudit', null) || null
      }
    });
  });

  // ── ST8: Confidence Calibration API ─────────────────────────────

  a.get('/api/signal/calibration', async (req, res) => {
    try {
      const db = getDB();
      await scheduler.calibrateConfidenceScores();
      const adj = db.getSetting('signal_walletConfAdj', {});
      res.json({ success: true, adjustments: adj, walletCount: Object.keys(adj).length });
    } catch (err) {
      res.status(500).json({ error: err.message });
    }
  });

  // ── Backtesting API ──────────────────────────────────────────────

  a.get('/api/backtest', (req, res) => {
    if (!walletTracker || !signal) return res.json({ success: false, error: 'Not ready' });
    const BacktestEngine = require('./backtest');
    const bt = new BacktestEngine(walletTracker, signal);
    const result = bt.run({
      wallets: req.query.wallets ? req.query.wallets.split(',') : [],
      days: parseInt(req.query.days) || 7,
      bankroll: parseFloat(req.query.bankroll) || 500,
      kellyFraction: parseFloat(req.query.kelly) || 0.25,
      maxPositionPct: parseFloat(req.query.maxPos) || 0.10,
      minEV: parseFloat(req.query.minEV) || 0.01,
      maxEntryPrice: parseFloat(req.query.maxPrice) || 0.80
    });
    res.json({ success: true, data: result });
  });

  a.post('/api/backtest/compare', (req, res) => {
    if (!walletTracker || !signal) return res.json({ success: false, error: 'Not ready' });
    const BacktestEngine = require('./backtest');
    const bt = new BacktestEngine(walletTracker, signal);
    const variants = req.body.variants || [];
    if (!variants.length) return res.status(400).json({ success: false, error: 'Provide variants array' });
    const results = bt.compare(variants);
    res.json({ success: true, data: results });
  });

  // ── Wallet Lifecycle API ─────────────────────────────────────────

  a.get('/api/lifecycle/status', (req, res) => {
    if (!walletLifecycle) return res.json({ success: false, error: 'Lifecycle manager not available' });
    const states = walletLifecycle.getAllStates();
    res.json({
      success: true,
      data: {
        active: states.ACTIVE,
        passive: states.PASSIVE,
        discarded: states.DISCARDED,
        counts: {
          active: states.ACTIVE.length,
          passive: states.PASSIVE.length,
          discarded: states.DISCARDED.length,
        },
      }
    });
  });

  a.get('/api/lifecycle/evaluate', (req, res) => {
    if (!walletLifecycle) return res.json({ success: false, error: 'Lifecycle manager not available' });
    const result = walletLifecycle.evaluate();
    res.json({ success: true, data: result });
  });

  a.get('/api/lifecycle/explain/:address', (req, res) => {
    if (!walletLifecycle) return res.json({ success: false, error: 'Lifecycle manager not available' });
    const result = walletLifecycle.explain(req.params.address);
    res.json({ success: true, data: result });
  });

  a.get('/api/lifecycle/log', (req, res) => {
    if (!walletLifecycle) return res.json({ success: false, error: 'Lifecycle manager not available' });
    const limit = parseInt(req.query.limit, 10) || 50;
    res.json({ success: true, data: walletLifecycle.getTransitionLog(limit) });
  });

  a.get('/api/lifecycle/config', (req, res) => {
    if (!walletLifecycle) return res.json({ success: false, error: 'Lifecycle manager not available' });
    res.json({ success: true, data: walletLifecycle.getConfig() });
  });

  a.post('/api/lifecycle/config', (req, res) => {
    if (!walletLifecycle) return res.status(500).json({ success: false, error: 'Lifecycle manager not available' });
    const applied = walletLifecycle.updateConfig(req.body);
    res.json({ success: true, applied });
  });

  a.post('/api/lifecycle/force-state', (req, res) => {
    if (!walletLifecycle) return res.status(500).json({ success: false, error: 'Lifecycle manager not available' });
    const { address, state, reason } = req.body;
    if (!address || !state) return res.status(400).json({ success: false, error: 'address and state required' });
    try {
      const result = walletLifecycle.forceState(address, state, reason || 'Manual override via API');
      res.json({ success: true, data: result });
    } catch (e) {
      res.status(400).json({ success: false, error: e.message });
    }
  });

  a.get('/api/lifecycle/rankings', (req, res) => {
    if (!walletLifecycle) return res.json({ success: false, error: 'Lifecycle manager not available' });
    const ranked = walletLifecycle.rankAllWallets();
    res.json({
      success: true,
      data: ranked.map(w => ({
        address: w.address.slice(0, 12) + '...',
        fullAddress: w.address,
        score: w.score,
        rank: w.rank,
        state: w.state,
        valid: w.valid,
        factors: w.factors,
      }))
    });
  });

  // W7: Probationary wallets endpoint
  a.get('/api/lifecycle/probationary', (req, res) => {
    if (!walletLifecycle) return res.json({ success: false, error: 'Lifecycle manager not available' });
    try {
      const db = getDB();
      const states = walletLifecycle.getAllStates();
      const allWallets = [...states.ACTIVE, ...states.PASSIVE, ...states.DISCARDED];
      const probationary = allWallets
        .filter(w => w.probationary || (w.scoreFactors && w.scoreFactors.probationary))
        .map(w => ({
          address: w.address,
          state: w.state,
          reason: w.lastTransitionReason,
          tradesNeeded: Math.max(0, (w.probationaryTarget || 0) - (w.probationaryTradesStart || 0)),
          since: w.lastTransition ? new Date(w.lastTransition).toISOString() : null,
        }));

      // Also pull directly from in-memory states for accuracy
      const probationaryDirect = [];
      const rawStates = db.getSetting('wallet_lifecycle_states', {});
      for (const [addr, s] of Object.entries(rawStates)) {
        if (s.probationary) {
          probationaryDirect.push({
            address: addr,
            state: s.state,
            reason: s.lastTransitionReason,
            tradesNeeded: Math.max(0, (s.probationaryTarget || 0) - (s.probationaryTradesStart || 0)),
            since: s.lastTransition ? new Date(s.lastTransition).toISOString() : null,
          });
        }
      }

      const result = probationaryDirect.length > 0 ? probationaryDirect : probationary;
      res.json({ success: true, probationary: result, count: result.length });
    } catch (err) {
      res.status(500).json({ success: false, error: err.message });
    }
  });

  // ── Notifications API ─────────────────────────────────────────────

  a.get('/api/notifications', (req, res) => {
    res.json({ success: true, data: notifier?.getHistory(parseInt(req.query.limit, 10) || 20) || [], unread: notifier?.getUnreadCount() || 0 });
  });

  a.post('/api/notifications/read', (req, res) => {
    notifier?.markAllRead(); res.json({ success: true });
  });

  a.post('/api/notifications/settings', (req, res) => {
    for (const [k, v] of Object.entries(req.body)) {
      notifier?.updateSettings(k, v);  // whitelist enforced inside
    }
    res.json({ success: true });
  });

  // ── Telegram API ──────────────────────────────────────────────────

  a.get('/api/telegram/status', (req, res) => {
    res.json({ success: true, data: telegram?.getStatus() || { enabled: false, configured: false } });
  });

  a.post('/api/telegram/configure', async (req, res) => {
    const { token, chatId } = req.body;
    if (!token || !chatId) return res.status(400).json({ success: false, error: 'token and chatId required' });
    if (!telegram) { const T = require('./telegram'); telegram = new T(getDB(), rateLimiter); }
    telegram.configure(token, chatId);
    // Wire up command polling if not already active
    if (!telegram._pollTimer) {
      telegram.setDataProviders({
        getRisk: () => riskEngine,
        getTracker: () => walletTracker,
        getBalance: async () => clobClient?.getUSDCBalance() ?? null,
        getMonitor: () => monitor,
        getSignal: () => signal,
        getScheduler: () => scheduler
      });
      telegram.startCommandPolling(5000);
    }
    const test = await telegram.test();
    res.json({ success: test.success, message: test.success ? 'Telegram configured! Commands: /status /top3 /balance /positions /help' : 'Config saved but test failed: ' + test.error });
  });

  a.post('/api/telegram/send', async (req, res) => {
    if (!telegram?.enabled) return res.status(400).json({ success: false, error: 'Telegram not configured' });
    const r = await telegram.send(req.body.message);
    res.json(r);
  });

  a.post('/api/telegram/enable', (req, res) => { telegram?.enable(); res.json({ success: true }); });
  a.post('/api/telegram/disable', (req, res) => { telegram?.disable(); res.json({ success: true }); });

  // ── Audit trail API ───────────────────────────────────────────────

  a.get('/api/audit/recent', (req, res) => {
    res.json({ success: true, data: auditTrail?.getRecent(parseInt(req.query.count, 10) || 50) || [] });
  });

  a.get('/api/audit/verify', (req, res) => {
    res.json({ success: true, data: auditTrail?.verify() || { valid: false, error: 'Audit trail not available' } });
  });

  a.get('/api/audit/info', (req, res) => {
    res.json({ success: true, data: auditTrail?.getInfo() || {} });
  });

  // ── Trade journal ────────────────────────────────────────────────

  a.get('/api/journal', (req, res) => {
    const limit = Math.min(parseInt(req.query.limit, 10) || 50, 500);
    const entries = getDB()?.getJournal(limit) || [];
    res.json({ success: true, data: entries });
  });

  // ── Signal activity feed (accepted + rejected, in-memory) ─────────
  a.get('/api/signal/activity', (req, res) => {
    const limit = Math.min(parseInt(req.query.limit, 10) || 100, 500);
    // Merge copy-trade signal rejections with updown strategy signal events.
    // The UI renders any entry with the shape { timestamp, market, side, size,
    // marketPrice, action, rejectReason, walletName }, so updown events that
    // already match this shape can be merged in directly.
    const rejections = signal?.getRecentRejections(limit) || [];
    const updownEvents = updownStrategy?.getRecentEvents(limit) || [];
    const merged = [...rejections, ...updownEvents]
      .sort((a, b) => (b.timestamp || 0) - (a.timestamp || 0))
      .slice(0, limit);
    res.json({ success: true, data: merged, count: merged.length });
  });

  // ── Wallet tracker advanced endpoints ───────────────────────────

  a.get('/api/tracker/wallet/:address/streaks', (req, res) => {
    if (!walletTracker) return res.json({ success: false, error: 'Tracker not running' });
    const streaks = walletTracker.getStreaks(req.params.address);
    res.json({ success: true, data: streaks });
  });

  a.get('/api/tracker/wallet/:address/roi', (req, res) => {
    if (!walletTracker) return res.json({ success: false, error: 'Tracker not running' });
    const roi = walletTracker.getWalletROI(req.params.address);
    res.json({ success: true, data: roi });
  });

  a.get('/api/tracker/wallet/:address/sharpe', (req, res) => {
    if (!walletTracker) return res.json({ success: false, error: 'Tracker not running' });
    const sharpe = walletTracker.getSharpeRatio(req.params.address);
    res.json({ success: true, data: { sharpe } });
  });

  a.get('/api/tracker/wallet/:address/time-of-day', (req, res) => {
    if (!walletTracker) return res.json({ success: false, error: 'Tracker not running' });
    const data = walletTracker.getTimeOfDayPerformance(req.params.address);
    res.json({ success: true, data });
  });

  a.get('/api/tracker/correlations', (req, res) => {
    if (!walletTracker) return res.json({ success: false, data: [] });
    const minCorrelation = parseFloat(req.query.min) || 0.7;
    const data = walletTracker.getCorrelatedWallets(minCorrelation);
    res.json({ success: true, data });
  });

  // ── Circuit breaker status ──────────────────────────────────────

  a.get('/api/risk/circuit-breaker', (req, res) => {
    const r = riskEngine;
    if (!r) return res.json({ success: true, data: { active: false } });
    const status = r.getStatus();
    res.json({
      success: true,
      data: {
        active: !!(status.circuitBreakerUntil && Date.now() < status.circuitBreakerUntil),
        consecutiveLosses: status.consecutiveLosses || 0,
        resumesAt: status.circuitBreakerUntil || null,
        remainingMs: status.circuitBreakerUntil ? Math.max(0, status.circuitBreakerUntil - Date.now()) : 0,
        circuitBreakerEnabled: getDB()?.getSetting('risk_circuitBreakerEnabled', true) ?? true
      }
    });
  });

  a.post('/api/risk/reset-circuit-breaker', (req, res) => {
    try {
      const r = getRisk();
      if (!r) return res.status(500).json({ success: false, error: 'Risk engine not available' });
      r.state.circuitBreakerUntil = null;
      r.state.consecutiveLosses = 0;
      r.state.paused = false;
      r.state.pauseReason = null;
      r._persistNow?.();

      // Also clear the CLOB order circuit breaker (separate state in clob.js).
      // These are two different breakers but the UI exposes one button for both:
      //   - risk breaker: consecutive losses / drawdown
      //   - clob breaker: 3 consecutive SDK order failures
      // Eric's workflow: paper never trips either, so in live mode one reset
      // button clears whichever tripped.
      let clobWasActive = false;
      try {
        if (clobClient && typeof clobClient.resetOrderCircuitBreaker === 'function') {
          const cr = clobClient.resetOrderCircuitBreaker();
          clobWasActive = !!cr?.wasActive;
        }
      } catch (e) {
        log('warn', 'CLOB breaker reset failed: ' + e.message);
      }

      log('info', `Circuit breaker manually reset (clobWasActive=${clobWasActive})`);
      res.json({ success: true, message: 'Circuit breaker cleared', clobWasActive });
    } catch (e) { res.status(500).json({ success: false, error: e.message }); }
  });

  // Re-enable live trading after smoke test passes.
  // Runs runResolveTokenIdsSmokeTest fresh against a live Gamma/CLOB fetch and
  // only flips risk_dryRun=false on a 'pass' result. Skipped / failed results
  // leave dryRun untouched so the operator can retry once Gamma is healthy.
  // This is the recovery path for the "dryRun stuck" class of bugs where a
  // transient smoke test failure defensively flipped the flag at startup.
  a.post('/api/risk/enable-live', async (req, res) => {
    try {
      if (!clobClient) {
        return res.status(500).json({ success: false, error: 'CLOB client not initialized' });
      }
      log('info', 'enable-live: running resolveTokenIds smoke test...');
      const smokeResult = await runResolveTokenIdsSmokeTest(clobClient, log);
      if (smokeResult.status === 'pass') {
        try { db.setSetting('risk_dryRun', false); } catch (e) {
          return res.status(500).json({ success: false, error: 'setSetting failed: ' + e.message });
        }
        log('info', `enable-live: smoke test passed (${smokeResult.verified} markets verified) — risk_dryRun set to false`);
        try { notifier?.send?.('Live Trading Enabled', `Smoke test passed (${smokeResult.verified} markets). Live mode active.`, { type: 'info', priority: 'high' }); } catch (_) {}
        try { telegram?.send?.(`Live trading enabled via API. Smoke test passed (${smokeResult.verified} markets).`); } catch (_) {}
        return res.json({ success: true, smokeResult, message: 'Live trading enabled' });
      }
      // skipped or fail: do NOT flip the flag
      log('warn', `enable-live: smoke test did not pass (${smokeResult.status}) — live mode NOT enabled. Reason: ${smokeResult.reason || smokeResult.error || 'unknown'}`);
      return res.status(409).json({
        success: false,
        smokeResult,
        error: `Smoke test did not pass (status=${smokeResult.status}), live mode NOT enabled`
      });
    } catch (e) {
      log('error', 'enable-live threw: ' + e.message);
      res.status(500).json({ success: false, error: e.message });
    }
  });

  // ── Rate limiter status ───────────────────────────────────────────

  a.get('/api/rate-limit/status', (req, res) => {
    res.json({ success: true, data: rateLimiter?.getStatus() || {} });
  });

  // ── Full system status ────────────────────────────────────────────

  a.get('/api/system/tos-status', (req, res) => {
    try {
      const db = getDB();
      res.json({
        tosHash: db.getSetting('tos_hash', null),
        lastChecked: db.getSetting('tos_hash_date', null)
      });
    } catch (err) {
      res.status(500).json({ error: err.message });
    }
  });

  a.get('/api/system/status', (req, res) => {
    const data = cachedJson('system_status', 500, () => ({
      server: 'running',
      version: getVersion(),
      serverStartedAt: _serverStartedAt,
      risk: riskEngine?.getStatus() || null,
      monitor: monitor?.getStatus() || null,
      signal: signal?.getStatus() || null,
      scheduler: scheduler?.getStatus() || null,
      db: getDB()?.getDBInfo() || null,
      notifications: { unread: notifier?.getUnreadCount() || 0 },
      telegram: telegram?.getStatus() || null,
      rateLimiter: rateLimiter?.getStatus() || null,
      audit: auditTrail?.getInfo() || null,
      clob: clobClient?.getStatus() || null,
      exitEngine: exitEngine?.getStatus() || null,
      websocket: polyWs ? {
        connected: polyWs.isConnected(),
        latencyMs: polyWs.getLatencyMs(),
        fallbackToREST: !!polyWs.fallbackToREST
      } : null
    }));
    res.json({ success: true, data });
  });

  // ── Shadow trader endpoints ───────────────────────────────────────────

  a.get('/api/shadow/performance', (req, res) => {
    try {
      if (!shadowTrader) return res.json({ success: true, data: { enabled: false, reason: 'shadow trader not initialised' } });
      res.json({ success: true, data: shadowTrader.getStatus() });
    } catch (e) { res.status(500).json({ success: false, error: e.message }); }
  });

  a.get('/api/shadow/config', (req, res) => {
    try {
      const db = getDB();
      const cfg = Object.assign(
        { kellyFraction: 0.30, confidenceThreshold: 50, maxBankrollPct: 0.08, enabled: true },
        db ? db.getSetting('shadow_config', {}) : {}
      );
      res.json({ success: true, data: cfg });
    } catch (e) { res.status(500).json({ success: false, error: e.message }); }
  });

  a.post('/api/shadow/config', (req, res) => {
    try {
      const db = getDB();
      if (!db) return res.status(500).json({ success: false, error: 'DB not available' });
      const allowed = ['kellyFraction', 'confidenceThreshold', 'maxBankrollPct', 'enabled'];
      const current = db.getSetting('shadow_config', {});
      const updates = {};
      for (const key of allowed) {
        if (req.body && key in req.body) updates[key] = req.body[key];
      }
      db.setSetting('shadow_config', Object.assign({}, current, updates));
      log('info', 'Shadow config updated', updates);
      res.json({ success: true, data: db.getSetting('shadow_config', {}) });
    } catch (e) { res.status(500).json({ success: false, error: e.message }); }
  });

  // Adopt shadow params into the live signal engine config
  a.post('/api/shadow/promote', (req, res) => {
    try {
      const db = getDB();
      if (!db) return res.status(500).json({ success: false, error: 'DB not available' });
      const pending = db.getSetting('shadow_promote_pending', null);
      if (!pending) return res.status(400).json({ success: false, error: 'No pending shadow promotion — shadow has not outperformed for 3+ weeks yet' });
      const cfg = pending.proposedConfig || {};
      // Apply shadow Kelly fraction to live signal settings
      if (cfg.kellyFraction) db.setSetting('signal_kellyFraction', cfg.kellyFraction);
      if (cfg.confidenceThreshold) db.setSetting('signal_minConvictionPct', cfg.confidenceThreshold);
      db.setSetting('shadow_promote_pending', null);  // clear flag
      log('info', 'Shadow params promoted to live', cfg);
      res.json({ success: true, message: 'Shadow parameters adopted for live trading', applied: cfg });
    } catch (e) { res.status(500).json({ success: false, error: e.message }); }
  });

  // ── News signal engine endpoints ───────────────────────────────────────

  a.get('/api/news/status', (req, res) => {
    try {
      if (!newsSignal) return res.json({ success: true, data: { enabled: false, reason: 'news engine not loaded' } });
      res.json({ success: true, data: { ...newsSignal.getStats(), config: newsSignal.getConfig() } });
    } catch (e) { res.status(500).json({ success: false, error: e.message }); }
  });

  a.get('/api/updown/status', (req, res) => {
    try {
      if (!updownStrategy) return res.json({ success: true, data: { enabled: false, reason: 'updown strategy not loaded' } });
      res.json({ success: true, data: updownStrategy.getStats() });
    } catch (e) { res.status(500).json({ success: false, error: e.message }); }
  });

  a.get('/api/mm/status', (req, res) => {
    try {
      if (!marketMaker) return res.json({ success: true, data: { enabled: false, reason: 'market maker not loaded' } });
      res.json({ success: true, data: { ...marketMaker.getStats(), config: marketMaker.getConfig() } });
    } catch (e) { res.status(500).json({ success: false, error: e.message }); }
  });

  a.get('/api/external/status', (req, res) => {
    try {
      if (!externalSignals) return res.json({ success: true, data: { enabled: false, reason: 'external signals not loaded' } });
      res.json({ success: true, data: externalSignals.getStats() });
    } catch (e) { res.status(500).json({ success: false, error: e.message }); }
  });

  // ── Arb engine endpoints ──────────────────────────────────────────────

  a.get('/api/arb/stats', (req, res) => {
    try {
      if (!arbEngine) return res.json({ success: true, data: { enabled: false, reason: 'arb engine not initialised' } });
      res.json({ success: true, data: arbEngine.getStats() });
    } catch (e) { res.status(500).json({ success: false, error: e.message }); }
  });

  a.get('/api/arb/positions', (req, res) => {
    try {
      if (!arbEngine) return res.json({ success: true, data: { open: [], recent: [] } });
      res.json({ success: true, data: {
        open:   [...arbEngine.openArbs.values()],
        recent: arbEngine.completedArbs.slice(-20)
      }});
    } catch (e) { res.status(500).json({ success: false, error: e.message }); }
  });

  a.get('/api/bundle-arb/stats', (req, res) => {
    try {
      if (!bundleArb) return res.json({ success: true, data: { enabled: false, reason: 'bundle arb not initialised' } });
      res.json({ success: true, data: bundleArb.getStats() });
    } catch (e) { res.status(500).json({ success: false, error: e.message }); }
  });

  return a;
}

function startServer(port) {
  // Generate auth token for this session
  authToken = crypto.randomBytes(32).toString('hex');

  return new Promise((resolve, reject) => {
    try {
      app = createApp();
      server = http.createServer(app);

      // ── WebSocket server (real-time frontend push) ──
      wss = new WebSocketServer({ server });
      wss.on('connection', (ws) => {
        wsClients.set(ws, { page: 'dashboard' });
        ws.on('message', (raw) => {
          try {
            const msg = JSON.parse(raw);
            if (msg.type === 'subscribe' && msg.page) {
              wsClients.set(ws, { page: msg.page });
            }
          } catch (e) {}
        });
        ws.on('close', () => wsClients.delete(ws));
        ws.on('error', () => wsClients.delete(ws));
        // Send initial state on connect
        wsPushPageData(ws, 'dashboard');
      });

      server.on('error', (e) => { log('error', 'Server error', { error: e.message }); reject(e); });
      server.listen(port, '127.0.0.1', () => {  // Bind to localhost only
        log('info', `Server started on port ${port}`);
        setTimeout(async () => {
          const ok = await initSystems();
          if (!ok) log('error', 'System initialization had errors — some features may be unavailable');

          try {
            const db = getDB();
            // Default to auto-start for hands-off operation
            if (db?.getSetting('scheduler_autoStart', true) !== false) {
              scheduler?.start();
              log('info', 'Scheduler auto-started');
            }
          } catch (e) {}
        }, 1000);
        resolve();
      });
    } catch (e) { reject(e); }
  });
}

async function stopServer() {
  try { await shutdownSystems(); } catch (e) { log('warn', 'Shutdown error: ' + e.message); }
  return new Promise((resolve) => {
    if (server) {
      server.close(() => { server = null; app = null; resolve(); });
      setTimeout(() => { if (server) { server = null; app = null; resolve(); } }, 5000);
    } else {
      resolve();
    }
  });
}

function getAuthToken() { return authToken; }

function getNotifier() { return notifier; }
function getSchedulerRef() { return scheduler; }

module.exports = { startServer, stopServer, getLogs, clearLogs, getAuthToken, getNotifier, getSchedulerRef };
