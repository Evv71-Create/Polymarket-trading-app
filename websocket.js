/**
 * WebSocket module for Polymarket CLOB real-time data.
 *
 * Subscribes to market price updates and user fills via persistent WebSocket.
 * Does NOT count against the REST API rate limit (80 req/min).
 *
 * Endpoint: wss://ws-subscriptions-clob.polymarket.com/ws/market
 * Fallback: REST polling continues if WS disconnects for >60s.
 */
'use strict';

const WebSocket = require('ws');

const WS_URL = 'wss://ws-subscriptions-clob.polymarket.com/ws/market';
const HEARTBEAT_INTERVAL = 30000; // 30s
const RECONNECT_MAX_DELAY = 30000; // 30s cap
const FALLBACK_TIMEOUT = 60000; // 60s before flagging REST fallback

class PolymarketWebSocket {
  constructor({ db, log } = {}) {
    this.db = db;
    this._log = log || ((level, msg) => console.log(`[WS] [${level}] ${msg}`));

    this._ws = null;
    this._connected = false;
    this._subscribedAssets = new Set();
    this._priceCache = new Map(); // tokenId -> { price, ts }
    this._reconnectAttempt = 0;
    this._heartbeatTimer = null;
    this._reconnectTimer = null;
    this._priceCacheCleanupTimer = null;
    this._disconnectedAt = null;
    this._callbacks = { price: [], trade: [], error: [] };
    this._lastMessageTime = 0;
    this._lastPingAt = 0;            // ms timestamp of most recent ping send
    this._lastLatencyMs = null;      // RTT measured on most recent pong
    this.fallbackToREST = false;
    this._priceCacheCleanupTimer = setInterval(() => { // Stale price cleanup
      const cutoff = Date.now() - 5 * 60 * 1000;
      for (const [k, v] of this._priceCache) {
        if (v.ts < cutoff) this._priceCache.delete(k);
      }
    }, 2 * 60 * 1000);
  }

  // ── Public API ──────────────────────────────────────────────────────

  on(event, callback) {
    if (this._callbacks[event]) this._callbacks[event].push(callback);
  }

  /**
   * Subscribe to price updates for given token IDs.
   * Lazy-connects on first call.
   */
  subscribe(assetIds) {
    if (!Array.isArray(assetIds)) assetIds = [assetIds];
    for (const id of assetIds) this._subscribedAssets.add(id);

    if (!this._ws) {
      this._connect();
    } else if (this._connected) {
      this._sendSubscription(assetIds);
    }
  }

  unsubscribe(assetIds) {
    if (!Array.isArray(assetIds)) assetIds = [assetIds];
    for (const id of assetIds) this._subscribedAssets.delete(id);
    // No need to send unsubscribe — just stop tracking
  }

  /**
   * Get cached price for a token. Returns null if not available or stale.
   * Price is from the last WS update (real-time).
   *
   * @param {string} tokenId
   * @param {number} maxAgeMs - Reject cached prices older than this. Default 120000
   *   (2 minutes) for legacy callers. Strategies with tight time windows should
   *   pass a smaller value — e.g. updown uses 5000 for 5-min candles because a
   *   stale price from 30s ago can be a completely different candle.
   */
  getCachedPrice(tokenId, maxAgeMs = 120000) {
    const entry = this._priceCache.get(tokenId);
    if (!entry) return null;
    if (Date.now() - entry.ts > maxAgeMs) return null;
    return entry.price;
  }

  isConnected() {
    return this._connected;
  }

  /** Returns most recent ping→pong RTT in ms, or null if not yet measured. */
  getLatencyMs() {
    return this._lastLatencyMs;
  }

  /** Returns data health status for trading logic to check */
  getDataHealth() {
    const now = Date.now();
    const lastUpdate = this._lastMessageTime || 0;
    const secondsSinceUpdate = Math.round((now - lastUpdate) / 1000);
    return {
      isFallback: !!this.fallbackToREST,
      secondsSinceLastUpdate: secondsSinceUpdate,
      isStale: this.fallbackToREST && secondsSinceUpdate > 30
    };
  }

  shutdown() {
    if (this._heartbeatTimer) clearInterval(this._heartbeatTimer);
    if (this._reconnectTimer) clearTimeout(this._reconnectTimer);
    if (this._priceCacheCleanupTimer) clearInterval(this._priceCacheCleanupTimer);
    this._heartbeatTimer = null;
    this._reconnectTimer = null;
    this._priceCacheCleanupTimer = null;
    if (this._ws) {
      try { this._ws.close(1000, 'shutdown'); } catch (_) {}
      this._ws = null;
    }
    this._connected = false;
    this._log('info', 'WebSocket shut down');
  }

  // ── Internal ───────────────────────────────────────────────────────

  _connect() {
    if (this._ws) return;

    try {
      this._ws = new WebSocket(WS_URL);
    } catch (e) {
      this._log('error', `WebSocket creation failed: ${e.message}`);
      this._scheduleReconnect();
      return;
    }

    this._ws.onopen = () => {
      this._connected = true;
      this._reconnectAttempt = 0;
      this._disconnectedAt = null;
      this.fallbackToREST = false;
      this._log('info', `WebSocket connected (${this._subscribedAssets.size} assets)`);

      // Subscribe to all tracked assets
      if (this._subscribedAssets.size > 0) {
        this._sendSubscription([...this._subscribedAssets]);
      }

      // Start heartbeat
      if (this._heartbeatTimer) clearInterval(this._heartbeatTimer);
      this._heartbeatTimer = setInterval(() => {
        if (this._ws?.readyState === WebSocket.OPEN) {
          try {
            this._lastPingAt = Date.now();
            this._ws.send(JSON.stringify({ type: 'ping' }));
          } catch (_) {}
        }
      }, HEARTBEAT_INTERVAL);
    };

    this._ws.onmessage = (event) => {
      try {
        const data = typeof event.data === 'string' ? JSON.parse(event.data) : event.data;
        this._lastMessageTime = Date.now();
        this._handleMessage(data);
      } catch (e) {
        // Non-JSON message or parse error — ignore
      }
    };

    this._ws.onerror = (err) => {
      this._log('warn', `WebSocket error: ${err.message || 'unknown'}`);
      this._emit('error', err);
    };

    this._ws.onclose = (event) => {
      this._connected = false;
      this._ws = null;
      if (this._heartbeatTimer) { clearInterval(this._heartbeatTimer); this._heartbeatTimer = null; }

      if (!this._disconnectedAt) this._disconnectedAt = Date.now();

      // Check if we should flag REST fallback
      if (Date.now() - this._disconnectedAt > FALLBACK_TIMEOUT) {
        if (!this.fallbackToREST) {
          this.fallbackToREST = true;
          this._log('warn', 'WebSocket disconnected >60s, falling back to REST');
        }
      }

      this._log('info', `WebSocket closed (code: ${event.code}). Reconnecting...`);
      this._scheduleReconnect();
    };
  }

  _sendSubscription(assetIds) {
    if (!this._ws || this._ws.readyState !== WebSocket.OPEN) return;
    try {
      this._ws.send(JSON.stringify({
        type: 'market',
        assets_ids: assetIds
      }));
    } catch (e) {
      this._log('warn', `Failed to send subscription: ${e.message}`);
    }
  }

  _handleMessage(data) {
    // Polymarket WS sends price/trade updates in various formats
    // Handle the common patterns:

    if (data.type === 'pong') {
      // Measure RTT — only count if we have a valid send timestamp
      if (this._lastPingAt > 0) {
        const rtt = Date.now() - this._lastPingAt;
        if (rtt >= 0 && rtt < 60000) this._lastLatencyMs = rtt;
      }
      return; // heartbeat response
    }

    // Price book update
    if (data.asset_id && (data.price || data.best_ask || data.best_bid)) {
      const tokenId = data.asset_id;
      const price = parseFloat(data.price || data.best_ask || data.best_bid) || 0;
      if (price > 0) {
        this._priceCache.set(tokenId, { price, ts: Date.now() });
        if (this._priceCache.size > 1000) { // FIFO cap
          const iter = this._priceCache.keys();
          while (this._priceCache.size > 800) this._priceCache.delete(iter.next().value);
        }
        this._emit('price', { tokenId, price, bid: data.best_bid, ask: data.best_ask });
      }
    }

    // Trade/fill event
    if (data.event_type === 'trade' || data.type === 'trade') {
      this._emit('trade', data);
    }

    // Book snapshot or update — extract best prices
    if (Array.isArray(data)) {
      for (const item of data) {
        if (item.asset_id && (item.price || item.best_ask)) {
          const price = parseFloat(item.price || item.best_ask) || 0;
          if (price > 0) {
            this._priceCache.set(item.asset_id, { price, ts: Date.now() });
          }
        }
      }
      if (this._priceCache.size > 1000) { // FIFO cap
        const iter = this._priceCache.keys();
        while (this._priceCache.size > 800) this._priceCache.delete(iter.next().value);
      }
    }
  }

  _scheduleReconnect() {
    if (this._reconnectTimer) return;

    const delay = Math.min(
      1000 * Math.pow(2, this._reconnectAttempt),
      RECONNECT_MAX_DELAY
    );
    this._reconnectAttempt++;

    this._reconnectTimer = setTimeout(() => {
      this._reconnectTimer = null;
      this._log('info', `WebSocket reconnecting (attempt ${this._reconnectAttempt}, delay ${delay}ms)`);
      this._connect();
    }, delay);
  }

  _emit(event, data) {
    const handlers = this._callbacks[event] || [];
    for (const fn of handlers) {
      try { fn(data); } catch (_) {}
    }
  }
}

module.exports = PolymarketWebSocket;
