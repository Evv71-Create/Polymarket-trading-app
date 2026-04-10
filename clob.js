/**
 * Polymarket CLOB Client Wrapper
 * Handles: authentication, token ID resolution, order placement,
 *          price checking, order status, position exits
 */

// @polymarket/clob-client is ESM-only — must use dynamic import()
let ClobClient = null;
// viem helpers are ESM-only too — loaded lazily alongside the SDK
let viemCreateWalletClient = null;
let viemHttp = null;
let viemPrivateKeyToAccount = null;
let viemPolygonChain = null;
const { ethers } = require('ethers');
const axios = require('axios');

const GAMMA = 'https://gamma-api.polymarket.com';
const CLOB_URL = 'https://clob.polymarket.com';
const CHAIN_ID = 137; // Polygon

// Polymarket signature types (from @polymarket/clob-client SignatureType enum)
const SIG_TYPE_EOA = 0;
const SIG_TYPE_POLY_PROXY = 1;       // Old Polymarket proxy wallet (pre-Gnosis Safe migration)
const SIG_TYPE_POLY_GNOSIS_SAFE = 2; // Newer email/Magic accounts using a Gnosis Safe proxy

// Known Polymarket proxy wallet implementation address. Any minimal-proxy
// (EIP-1167) on Polygon that delegates to this impl is a POLY_PROXY account.
const POLY_PROXY_IMPL = '0x44e999d5c2f66ef0861317f9a4805ac2e90aeb4f';

class PolymarketCLOB {
  constructor(db, rateLimiter) {
    this.db = db;
    this.rateLimiter = rateLimiter;
    this.client = null;
    this.ready = false;
    this.error = null;
    this._signatureType = SIG_TYPE_EOA; // updated by initialize() based on funder type

    // Token ID cache: market question/title -> { yesTokenId, noTokenId, conditionId, tickSize, negRisk }
    this.tokenCache = new Map();
    // 60s TTL — UpDown markets live only 5-15 minutes, so a 3 min cache can
    // easily serve stale entries from prior (wrong) fuzzy matches. Keep fresh.
    this.tokenCacheTTL = 60 * 1000;
    // Counter for cache entries rejected on validation re-check. Surfaces
    // silent re-fetches that would otherwise look invisible in logs.
    this._stats = this._stats || {};
    this._stats.resolveCacheRejects = 0;

    // Raw Gamma date-range response cache. Distinct from tokenCache (which
    // stores validated per-market resolutions). Used by resolveTokenIds to
    // avoid hammering Gamma with identical /markets?end_date_min=... calls.
    // 60s TTL — short-horizon markets churn quickly.
    this._dateRangeCache = null; // { data: markets[], ts: ms }
    this._dateRangeCacheTTL = 60 * 1000;
  }

  /**
   * Validate that a candidate market title actually matches the query.
   * Factored out so we can run the same check at fresh-fetch time AND on
   * every cache hit — otherwise cached entries bypass Option B validation.
   * Returns true if both Layer 1 (asset keyword) and Layer 2 (jaccard) pass.
   */
  _isResolveTokenMatchValid(queryLc, titleLc) {
    if (!queryLc || !titleLc) return false;

    // Layer 1 — asset-keyword check
    const ASSET_KEYWORDS = [
      'bitcoin', 'ethereum', 'solana', 'dogecoin', 'xrp', 'bnb',
      'hyperliquid', 'hype', 'avalanche', 'polygon', 'chainlink',
      'pepe', 'shiba', 'trump', 'litecoin', 'cardano', 'tron',
      'sui', 'ripple', 'doge', 'btc', 'eth', 'sol'
    ];
    const queryAssets = ASSET_KEYWORDS.filter(k => queryLc.includes(k));
    const missingAssets = queryAssets.filter(k => !titleLc.includes(k));
    if (missingAssets.length > 0) return false;

    // Layer 2 — Jaccard word-overlap floor
    const STOPWORDS = new Set([
      'up', 'or', 'down', 'the', 'a', 'an', 'to', 'of', 'in', 'on',
      'at', 'is', 'for', 'and'
    ]);
    const tokenize = (s) => {
      const set = new Set();
      for (const w of s.split(/[^a-z0-9]+/)) {
        if (w.length < 3) continue;
        if (STOPWORDS.has(w)) continue;
        set.add(w);
      }
      return set;
    };
    const qSet = tokenize(queryLc);
    const tSet = tokenize(titleLc);
    let intersect = 0;
    for (const w of qSet) if (tSet.has(w)) intersect++;
    const unionSize = qSet.size + tSet.size - intersect;
    const jaccard = unionSize > 0 ? intersect / unionSize : 0;
    return jaccard >= 0.35;
  }

  // ── Initialization ──────────────────────────────────────────────────

  async initialize() {
    if (!this.db) {
      this.error = 'No database available';
      return false;
    }

    // Lazy-load ESM modules. The Polymarket SDK is ESM-only, and we need viem
    // to construct a wallet client the SDK actually accepts: clob-client v5.x
    // detects ethers signers via the ethers v5 `_signTypedData` method, but the
    // project uses ethers v6 (which renamed the method to `signTypedData`).
    // Passing an ethers v6 wallet falls through to the SDK's viem-WalletClient
    // branch and dies on a missing `account.address` field. The fix is to give
    // the SDK an actual viem WalletClient.
    if (!ClobClient) {
      try {
        const mod = await import('@polymarket/clob-client');
        ClobClient = mod.ClobClient;
        const viem = await import('viem');
        const viemAccounts = await import('viem/accounts');
        const viemChains = await import('viem/chains');
        viemCreateWalletClient = viem.createWalletClient;
        viemHttp = viem.http;
        viemPrivateKeyToAccount = viemAccounts.privateKeyToAccount;
        viemPolygonChain = viemChains.polygon;
      } catch (e) {
        this.error = 'Failed to load CLOB client: ' + e.message;
        this.log('error', this.error);
        return false;
      }
    }

    const privateKey = this.db.getSettingInternal('private_key');
    const apiKey = this.db.getSettingInternal('polymarket_api_key');
    const apiSecret = this.db.getSettingInternal('api_secret');
    const passphrase = this.db.getSettingInternal('polymarket_passphrase');
    // Funder address = Polymarket proxy wallet for email/Magic login accounts.
    // Could be either the older POLY_PROXY type (sig type 1) or the newer
    // POLY_GNOSIS_SAFE type (sig type 2). We autodetect by inspecting the
    // proxy bytecode at the funder address.
    const funderAddress = this.db.getSettingInternal('polymarket_funder_address');

    if (!privateKey) {
      this.error = 'Missing private key — configure wallet private key on the Connect page';
      this.log('warn', 'CLOB client not initialized: missing private key');
      return false;
    }

    // Build a viem wallet client (the SDK requires this — see comment above)
    let walletClient;
    try {
      const account = viemPrivateKeyToAccount(privateKey.startsWith('0x') ? privateKey : '0x' + privateKey);
      walletClient = viemCreateWalletClient({
        account,
        chain: viemPolygonChain,
        transport: viemHttp()
      });
      this.log('info', 'Wallet client created', { address: account.address });
    } catch (e) {
      this.error = 'Invalid private key — could not construct wallet client: ' + e.message;
      this.log('error', this.error);
      return false;
    }

    // Detect signature type from the funder's on-chain bytecode
    let signatureType = null;
    if (funderAddress) {
      signatureType = await this._detectSignatureType(funderAddress);
      if (signatureType === null) {
        this.error = `Could not determine signature type for funder ${funderAddress}. Either the address has no contract code (wrong address, or Polymarket account not deployed yet — deposit USDC first), or all Polygon RPCs are unreachable. You can set polymarket_signature_type=1 for POLY_PROXY or =2 for POLY_GNOSIS_SAFE to override.`;
        this.log('error', this.error);
        return false;
      }
      this.log('info', 'Detected signature type', { signatureType, funder: funderAddress });
    }

    let effectiveApiKey = apiKey;
    let effectiveApiSecret = apiSecret;
    let effectivePassphrase = passphrase;

    // Credential derivation: if API key/secret missing, derive from private key.
    // Pass signatureType + funder so the L2 credential is bound to the proxy
    // wallet (otherwise Polymarket creates an EOA-only L2 identity that has no
    // visibility into the proxy's positions).
    if (!apiKey || !apiSecret) {
      this.log('info', 'API credentials missing — attempting to derive from private key');
      try {
        const tempClient = funderAddress
          ? new ClobClient(CLOB_URL, CHAIN_ID, walletClient, undefined, signatureType, funderAddress)
          : new ClobClient(CLOB_URL, CHAIN_ID, walletClient);
        let creds;
        try {
          creds = await tempClient.deriveApiKey();
          // SDK returns credentials as { key, secret, passphrase }.
          // Accept either field name to tolerate any future SDK rename.
          const k = creds?.key || creds?.apiKey;
          if (!k || !creds?.secret || !creds?.passphrase) throw new Error('incomplete derivation');
          this.log('info', 'Derived API credentials from private key');
        } catch {
          creds = await tempClient.createApiKey();
          this.log('info', 'Created new API credentials from private key');
        }
        const derivedKey = creds?.key || creds?.apiKey;
        if (derivedKey && creds?.secret) {
          effectiveApiKey = derivedKey;
          effectiveApiSecret = creds.secret;
          effectivePassphrase = creds.passphrase || '';
          // Persist so we don't re-derive every startup
          this.db.setSettingInternal('polymarket_api_key', effectiveApiKey);
          this.db.setSettingInternal('api_secret', effectiveApiSecret);
          this.db.setSettingInternal('polymarket_passphrase', effectivePassphrase);
          this.log('info', 'Persisted derived API credentials to DB');
        } else {
          this.error = 'Could not derive or create API credentials from private key';
          this.log('warn', this.error);
          return false;
        }
      } catch (e) {
        this.error = 'Credential derivation failed: ' + e.message;
        this.log('warn', this.error);
        return false;
      }
    }

    try {
      if (funderAddress) {
        this.client = new ClobClient(
          CLOB_URL,
          CHAIN_ID,
          walletClient,
          { key: effectiveApiKey, secret: effectiveApiSecret, passphrase: effectivePassphrase || '' },
          signatureType,
          funderAddress
        );
        const modeName = signatureType === SIG_TYPE_POLY_GNOSIS_SAFE ? 'Gnosis Safe' : 'POLY_PROXY';
        this.log('info', `CLOB client configured in ${modeName} mode`, { funder: funderAddress, signatureType });
        // Cache for use by Safe-routing helpers (_isSafeMode etc.)
        this._signatureType = signatureType;
      } else {
        this.client = new ClobClient(
          CLOB_URL,
          CHAIN_ID,
          walletClient,
          { key: effectiveApiKey, secret: effectiveApiSecret, passphrase: effectivePassphrase || '' }
        );
        this.log('info', 'CLOB client configured in EOA mode (no funder set)');
        this._signatureType = SIG_TYPE_EOA;
      }

      // Verify credentials with a lightweight call
      try {
        await this.client.getOpenOrders();
        this.log('info', 'CLOB client authenticated successfully');
      } catch (e) {
        // getOpenOrders might fail if no orders — check if it's an auth error
        if (e.message?.includes('401') || e.message?.includes('403') || e.message?.includes('Unauthorized')) {
          this.error = 'Authentication failed — check your API key, secret, and passphrase';
          this.log('error', 'CLOB auth failed');
          this.client = null;
          return false;
        }
        // Other errors are OK — API is reachable, auth worked
        this.log('info', 'CLOB client initialized (auth check returned non-critical error)');
      }

      this.ready = true;
      this.error = null;
      return true;
    } catch (e) {
      // Sanitize error — never log raw ethers errors that may contain key material
      this.error = 'CLOB client init failed — check private key format and network connectivity';
      this.log('error', 'CLOB client init failed');
      this.client = null;
      return false;
    }
  }

  isReady() { return this.ready && this.client !== null; }

  // ── Token ID Resolution ─────────────────────────────────────────────

  /**
   * Resolve a market name/question to CLOB token IDs.
   * Searches Gamma API by title, caches results.
   * Returns { yesTokenId, noTokenId, conditionId, tickSize, negRisk } or null.
   */
  async resolveTokenIds(marketName) {
    if (!marketName) return null;

    // Check cache — and re-validate on hit. Option B validation only ran
    // at fresh-fetch time historically, so a bad entry persisted for the
    // full TTL. Now we re-run the same asset-keyword + jaccard check on
    // every hit; any failure evicts and falls through to a fresh fetch.
    const cacheKey = marketName.toLowerCase().trim();
    const cached = this.tokenCache.get(cacheKey);
    if (cached && Date.now() - cached._ts < this.tokenCacheTTL) {
      const cachedTitleLc = (cached.question || '').toLowerCase();
      if (this._isResolveTokenMatchValid(cacheKey, cachedTitleLc)) {
        return cached;
      }
      // Cached entry fails validation — purge and re-fetch
      this._stats.resolveCacheRejects = (this._stats.resolveCacheRejects || 0) + 1;
      this.tokenCache.delete(cacheKey);
      this.log('warn', 'resolveTokenIds: cache entry failed re-validation, evicting', {
        query: cacheKey.slice(0, 60),
        cachedTitle: cachedTitleLc.slice(0, 60)
      });
    }

    try {
      if (this.rateLimiter && !this.rateLimiter.consume('polymarket_data')) {
        this.log('warn', 'Rate limited — skipping token resolution');
        // Don't serve stale cache on rate-limit: if we just got here, the
        // cache was already either missing, expired, or failed validation.
        return null;
      }

      // ── Date-range primitive ─────────────────────────────────────────
      // Gamma's /markets?title=<q> endpoint is fulltext-fuzzy and returns
      // completely unrelated markets (e.g. Russia-Ukraine / Kardashian /
      // Biden-COVID for a Bitcoin Up/Down query). Instead, fetch all
      // non-closed markets whose end_date falls within a 7-day horizon
      // (covers all short-term markets without pulling history) and do
      // a strict exact-title match against that result set. Exact match
      // against real Gamma titles can only succeed on real markets.
      const searchTerm = marketName.slice(0, 80);
      const target = searchTerm.toLowerCase();
      let best = null;

      let dateRangeMarkets = null;
      if (this._dateRangeCache && (Date.now() - this._dateRangeCache.ts) < this._dateRangeCacheTTL) {
        dateRangeMarkets = this._dateRangeCache.data;
      } else {
        const nowIso = new Date().toISOString();
        const horizonIso = new Date(Date.now() + 7 * 24 * 60 * 60 * 1000).toISOString();
        try {
          const r = await axios.get(`${GAMMA}/markets`, {
            params: {
              limit: 500,
              closed: false,
              active: true,
              end_date_min: nowIso,
              end_date_max: horizonIso
            },
            timeout: 10000
          });
          dateRangeMarkets = r.data || [];
          this._dateRangeCache = { data: dateRangeMarkets, ts: Date.now() };
        } catch (e) {
          this.log('warn', 'resolveTokenIds: date-range fetch failed', { error: e.message });
          dateRangeMarkets = [];
        }
      }

      // Exact title match (lowercased, trimmed) — no fuzzy fallback.
      const queryLc = marketName.toLowerCase().trim();
      best = dateRangeMarkets.find(m => {
        const title = (m.question || m.title || '').toLowerCase().trim();
        return title === queryLc;
      }) || null;

      // Slug fallback — kept for non-updown markets that may not appear in
      // the 7-day horizon window (e.g. longer-dated markets).
      if (!best) {
        if (this.rateLimiter && !this.rateLimiter.consume('polymarket_data')) {
          this.log('warn', 'Rate limited — skipping slug fallback resolution');
        } else {
          const slug = marketName.toLowerCase().replace(/[^a-z0-9]+/g, '-').slice(0, 60);
          try {
            const r2 = await axios.get(`${GAMMA}/markets`, {
              params: { slug: slug, limit: 1 },
              timeout: 8000
            });
            if (r2.data?.length) best = r2.data[0];
          } catch (e) {}
        }
      }

      if (!best) {
        this.log('warn', `Could not resolve token IDs for: "${searchTerm}"`);
        return null;
      }

      // ── Strict match validation (Option B) ───────────────────────────
      // Gamma's /markets?title= endpoint is fuzzy and frequently returns
      // totally unrelated markets. Fail safely instead of guessing.
      // Validation logic lives in _isResolveTokenMatchValid so the same
      // check runs on fresh fetches AND on cache hits.
      {
        const titleLc = (best.question || best.title || '').toLowerCase();
        if (!this._isResolveTokenMatchValid(target, titleLc)) {
          this.log('warn', 'resolveTokenIds: rejected fuzzy mismatch', {
            query: searchTerm,
            rejected: (best.question || best.title || '').slice(0, 80)
          });
          return null;
        }
        this.log('info', 'resolveTokenIds: validated match', {
          query: searchTerm.slice(0, 60),
          matched: (best.question || best.title || '').slice(0, 60)
        });
      }

      // Gamma returns clobTokenIds as a JSON string, not an array.
      // Parse first; using it raw would index string characters (e.g. "[") as token IDs,
      // which slip past falsy-checks and get rejected by the CLOB SDK as "Invalid token id".
      let clobTokenIds = best.clobTokenIds;
      if (typeof clobTokenIds === 'string') {
        try { clobTokenIds = JSON.parse(clobTokenIds); } catch (_) { clobTokenIds = null; }
      }
      if (!Array.isArray(clobTokenIds) || clobTokenIds.length < 2 || !clobTokenIds[0] || !clobTokenIds[1]) {
        this.log('warn', `Could not resolve token IDs for: "${searchTerm}"`);
        return null;
      }

      // Stale market check — reject resolved/closed markets
      if (best.closed || best.resolved) {
        this.log('warn', `Market is already resolved/closed: "${(best.question || best.title || '').slice(0, 50)}"`);
        return null;
      }

      const resolved = {
        yesTokenId: clobTokenIds[0],
        noTokenId: clobTokenIds[1],
        conditionId: best.conditionId,
        question: best.question || best.title,
        tickSize: best.minimumTickSize || '0.01',
        negRisk: best.negRisk || false,
        active: !best.closed && !best.resolved,
        endDate: best.endDate || best.end_date_iso || null,
        _ts: Date.now()
      };

      this.tokenCache.set(cacheKey, resolved);
      this.log('info', 'Resolved token IDs', {
        market: searchTerm.slice(0, 50),
        yesToken: resolved.yesTokenId?.slice(0, 20) + '...',
        conditionId: resolved.conditionId?.slice(0, 20) + '...'
      });

      return resolved;
    } catch (e) {
      this.log('error', 'Token resolution failed', { market: marketName.slice(0, 50), error: e.message });
      // Never serve stale cache on error — a failed fetch is not permission
      // to hand back an entry that may already be wrong or expired. The
      // caller is responsible for handling null (typically: skip the trade).
      return null;
    }
  }

  /**
   * Check order book depth for a token.
   * Returns { bidLiquidity, askLiquidity, spread, sufficient }
   */
  async checkLiquidity(tokenId, minLiquidity = 500) {
    if (!this.isReady()) return { sufficient: true }; // Can't check, proceed

    try {
      const book = await this.client.getOrderBook(tokenId);
      if (!book) return { sufficient: true };

      // Sum top 5 levels of bids and asks
      const bids = (book.bids || []).slice(0, 5);
      const asks = (book.asks || []).slice(0, 5);

      const bidLiquidity = bids.reduce((s, b) => s + (parseFloat(b.size) || 0) * (parseFloat(b.price) || 0), 0);
      const askLiquidity = asks.reduce((s, a) => s + (parseFloat(a.size) || 0) * (parseFloat(a.price) || 0), 0);

      const bestBid = bids.length > 0 ? parseFloat(bids[0].price) || 0 : 0;
      const bestAsk = asks.length > 0 ? parseFloat(asks[0].price) || 0 : 0;
      const spread = bestAsk > 0 && bestBid > 0 ? ((bestAsk - bestBid) / bestAsk) * 100 : 0;

      const sufficient = bidLiquidity >= minLiquidity || askLiquidity >= minLiquidity;

      return {
        bidLiquidity: +bidLiquidity.toFixed(2),
        askLiquidity: +askLiquidity.toFixed(2),
        spread: +spread.toFixed(2),
        bestBid, bestAsk,
        sufficient
      };
    } catch (e) {
      this.log('warn', 'Liquidity check failed', { error: e.message });
      return { sufficient: true }; // On error don't block
    }
  }

  /**
   * Get raw order book for a token.
   * Proxy to the underlying ClobClient — signal.js calls this directly.
   */
  async getOrderBook(tokenId) {
    if (!this.isReady() || !this.client) return null;
    try {
      return await this.client.getOrderBook(tokenId);
    } catch (e) {
      this.log('warn', 'getOrderBook failed', { tokenId: tokenId?.slice(0, 12), error: e.message });
      return null;
    }
  }

  /**
   * Check if a market is still active (not closed/resolved) before placing orders.
   * Returns true if active, false if stale/resolved.
   */
  async isMarketActive(conditionId) {
    if (!conditionId) return true; // can't check, assume active
    if (this.rateLimiter && !this.rateLimiter.consume('polymarket_data')) {
      this.log('warn', 'Rate limited — skipping market active check');
      return true; // don't block on rate limit
    }
    try {
      // Gamma silently ignores `condition_id` (singular) and returns random
      // markets — must use `condition_ids` (plural). No `closed` filter here
      // because we want to see the market regardless of state, then inspect
      // the `closed`/`resolved` flags below.
      const r = await axios.get(`${GAMMA}/markets`, {
        params: { condition_ids: conditionId, limit: 1 },
        timeout: 8000
      });
      const market = r.data?.[0];
      if (!market) return false;
      return !market.closed && !market.resolved;
    } catch (e) {
      return true; // on error, don't block — let the order attempt proceed
    }
  }

  // ── Order Placement ─────────────────────────────────────────────────

  /**
   * Place a limit order.
   * @param {string} tokenId - CLOB token ID
   * @param {string} side - 'BUY' or 'SELL'
   * @param {number} price - 0.00 to 1.00
   * @param {number} size - Number of shares
   * @param {object} opts - { tickSize, negRisk, orderType }
   * @returns {{ success, orderId, data, error }}
   */
  async placeOrder(tokenId, side, price, size, opts = {}) {
    if (!this.isReady()) {
      return { success: false, error: this.error || 'CLOB client not initialized' };
    }

    // Order circuit breaker — block orders if too many consecutive failures
    if (this.isOrderCircuitBreakerActive()) {
      const remaining = Math.round((this._orderCircuitBreakerUntil - Date.now()) / 60000);
      return { success: false, error: `Order circuit breaker active — ${remaining} min remaining` };
    }

    try {
      const tickSize = opts.tickSize || '0.01';
      const negRisk = opts.negRisk || false;
      const orderType = opts.orderType || 'GTC';

      // Pre-flight allowance check for live orders
      if (!opts._skipAllowanceCheck) {
        const usdNeeded = (parseFloat(price) || 0) * (parseFloat(size) || 0);
        if (usdNeeded > 0) {
          const allowanceResult = await this.ensureAllowance(usdNeeded, negRisk);
          if (!allowanceResult.sufficient) {
            this.log('error', 'Allowance check failed — cannot place order', { error: allowanceResult.error });
            return { success: false, error: 'USDC allowance insufficient: ' + (allowanceResult.error || 'approval failed') };
          }
          if (allowanceResult.approved) {
            this.log('info', 'USDC auto-approved for exchange', { txHash: allowanceResult.txHash });
          }
        }
      }

      this.log('info', 'Placing order', { side, price, size, tokenId: tokenId.slice(0, 20) + '...' });

      const result = await this.client.createAndPostOrder({
        tokenID: tokenId,
        price: price,
        side: side.toUpperCase(),
        size: size
      }, {
        tickSize: tickSize,
        negRisk: negRisk
      }, orderType);

      const orderId = result?.orderID || result?.id || null;

      // SDK's throwOnError is off by default, so HTTP 400/4xx/5xx come back as
      // a plain object instead of an exception. Without this check, clob.js
      // would mark failed orders as success and updown-strategy would log the
      // generic "no orderId in response" — hiding the real CLOB error (e.g.
      // minimum order size, tick size mismatch, insufficient balance).
      if (!orderId) {
        const apiErr =
          result?.error ||
          result?.errorMsg ||
          result?.error_msg ||
          result?.message ||
          (typeof result === 'string' ? result : null) ||
          `CLOB rejected order (status ${result?.status ?? 'unknown'})`;
        this.log('error', 'Order rejected by CLOB', {
          error: apiErr,
          sdkStatus: result?.status ?? null,
          sdkResponse: result,
          tokenId: tokenId?.slice(0, 20) + '...',
          negRisk,
          tickSize,
          orderType,
          side,
          price,
          size
        });
        this.recordOrderFailure(apiErr);
        return { success: false, error: apiErr, data: result };
      }

      this.log('info', 'Order placed', { orderId, status: result?.status });

      this.recordOrderSuccess();

      return {
        success: true,
        orderId,
        data: result
      };
    } catch (e) {
      // Full diagnostic: the SDK's "Invalid token id" and similar errors are opaque
      // without the exact tokenId, negRisk, tickSize, orderType, and underlying stack.
      // Previous log dropped all of those, making live-mode debugging impossible.
      this.log('error', 'Order placement failed', {
        error: e.message,
        stack: e.stack?.split('\n').slice(0, 4).join(' | '),
        sdkResponse: e.response?.data || e.response?.body || null,
        sdkStatus: e.response?.status || null,
        tokenId,
        negRisk: opts.negRisk || false,
        tickSize: opts.tickSize || '0.01',
        orderType: opts.orderType || 'GTC',
        side,
        price,
        size
      });
      this.recordOrderFailure(e.message);
      return { success: false, error: e.message };
    }
  }

  /**
   * Place a market order (fill-or-kill).
   */
  async placeMarketOrder(tokenId, side, size, opts = {}) {
    if (!this.isReady()) {
      return { success: false, error: this.error || 'CLOB client not initialized' };
    }

    if (this.isOrderCircuitBreakerActive()) {
      const remaining = Math.round((this._orderCircuitBreakerUntil - Date.now()) / 60000);
      return { success: false, error: `Order circuit breaker active — ${remaining} min remaining` };
    }

    try {
      const tickSize = opts.tickSize || '0.01';
      const negRisk = opts.negRisk || false;

      // Get current price first
      const priceData = await this.client.getPrice(tokenId, side.toUpperCase());
      const price = parseFloat(priceData?.price || 0);
      if (price <= 0) {
        return { success: false, error: 'Could not get current price for market order' };
      }

      this.log('info', 'Placing market order (FAK)', { side, size, price, tokenId: tokenId.slice(0, 20) + '...' });

      const result = await this.client.createAndPostOrder({
        tokenID: tokenId,
        price: price,
        side: side.toUpperCase(),
        size: size
      }, {
        tickSize: tickSize,
        negRisk: negRisk
      }, 'FAK');

      this.recordOrderSuccess();
      return {
        success: true,
        orderId: result?.orderID || result?.id || null,
        price,
        data: result
      };
    } catch (e) {
      this.log('error', 'Market order failed', { error: e.message });
      this.recordOrderFailure(e.message);
      return { success: false, error: e.message };
    }
  }

  // ── Order fill verification ─────────────────────────────────────────

  /**
   * Place an order and verify it fills within a timeout.
   * If not filled, cancel and optionally retry at market price.
   * Returns { success, orderId, filledSize, filledPrice, data, error }
   */
  async placeAndVerify(tokenId, side, price, size, opts = {}) {
    const timeout = opts.verifyTimeoutMs || 15000; // 15 seconds
    const pollInterval = 2000; // Check every 2 seconds
    const retryAtMarket = opts.retryAtMarket !== false; // Default: retry

    // Place the initial order
    const result = await this.placeOrder(tokenId, side, price, size, opts);
    if (!result.success) return result;

    const orderId = result.orderId;
    if (!orderId) return result; // Can't verify without order ID

    // Poll for fill
    const startTime = Date.now();
    while (Date.now() - startTime < timeout) {
      await new Promise(r => setTimeout(r, pollInterval));

      const order = await this.getOrderStatus(orderId);
      if (!order) continue;

      const status = (order.status || '').toLowerCase();

      if (status === 'matched' || status === 'filled') {
        const filledSize = parseFloat(order.size_matched || order.fillSize || size);
        const filledPrice = parseFloat(order.price || price);
        this.log('info', 'Order verified filled', { orderId, filledSize, filledPrice });
        return {
          success: true, orderId, filledSize, filledPrice,
          partialFill: filledSize < size,
          data: order
        };
      }

      if (status === 'cancelled' || status === 'expired') {
        this.log('warn', 'Order cancelled/expired before fill', { orderId });
        return { success: false, error: 'Order cancelled/expired', orderId };
      }
    }

    // Timeout — order didn't fill
    this.log('warn', 'Order not filled within timeout, cancelling', { orderId, timeout });
    await this.cancelOrder(orderId);

    if (!retryAtMarket) {
      return { success: false, error: 'Order timed out and was cancelled', orderId };
    }

    // Retry as FAK at current market price
    this.log('info', 'Retrying as market order (FAK)', { tokenId: tokenId.slice(0, 20) + '...' });
    const retryResult = await this.placeMarketOrder(tokenId, side, size, opts);
    if (retryResult.success) {
      return {
        success: true,
        orderId: retryResult.orderId,
        filledSize: size,
        filledPrice: retryResult.price,
        retried: true,
        data: retryResult.data
      };
    }

    return { success: false, error: 'Fill verification failed: ' + (retryResult.error || 'unknown'), orderId };
  }

  // ── Price & Order Status ────────────────────────────────────────────

  async getPrice(tokenId, side = 'SELL') {
    if (!this.isReady()) return null;
    try {
      const r = await this.client.getPrice(tokenId, side);
      return parseFloat(r?.price || 0);
    } catch (e) {
      this.log('warn', 'getPrice failed', { error: e.message });
      return null;
    }
  }

  async getMidpoint(tokenId) {
    if (!this.isReady()) return null;
    try {
      const r = await this.client.getMidpoint(tokenId);
      return parseFloat(r?.mid || 0);
    } catch (e) {
      return null;
    }
  }

  async getOrderStatus(orderId) {
    if (!this.isReady()) return null;
    try {
      return await this.client.getOrder(orderId);
    } catch (e) {
      this.log('warn', 'getOrderStatus failed', { orderId, error: e.message });
      return null;
    }
  }

  async getOpenOrders() {
    if (!this.isReady()) return [];
    try {
      const orders = await this.client.getOpenOrders();
      return orders || [];
    } catch (e) {
      return [];
    }
  }

  async cancelOrder(orderId) {
    if (!this.isReady()) return { success: false, error: 'Not ready' };
    try {
      await this.client.cancelOrder(orderId);
      this.log('info', 'Order cancelled', { orderId });
      return { success: true };
    } catch (e) {
      return { success: false, error: e.message };
    }
  }

  async cancelAll() {
    if (!this.isReady()) return { success: false, error: 'Not ready' };
    try {
      await this.client.cancelAll();
      this.log('info', 'All orders cancelled');
      return { success: true };
    } catch (e) {
      return { success: false, error: e.message };
    }
  }

  // ── Balance ──────────────────────────────────────────────────────────

  /**
   * Get USDC balance for the configured wallet on Polygon.
   * Uses a public Polygon RPC to call balanceOf on the USDC contract.
   */
  async getUSDCBalance() {
    if (!this.db) return null;

    const privateKey = this.db.getSettingInternal('private_key');
    if (!privateKey) return null;

    try {
      const wallet = new ethers.Wallet(privateKey);
      // Safe-mode: balance lives on the Gnosis Safe proxy, not the EOA signer.
      const address = this._isSafeMode() ? this._getFunder() : wallet.address;

      // Polygon USDC contract (bridged USDC.e) and native USDC
      const USDC_CONTRACTS = [
        '0x2791Bca1f2de4661ED88A30C99A7a9449Aa84174', // USDC.e (bridged, 6 decimals)
        '0x3c499c542cEF5E3811e1192ce70d8cC03d5c3359'  // Native USDC (6 decimals)
      ];
      // ERC-20 balanceOf ABI encoded: balanceOf(address) = 0x70a08231
      const balanceOfSig = '0x70a08231000000000000000000000000' + address.slice(2).toLowerCase();

      let totalBalance = 0;

      for (const contract of USDC_CONTRACTS) {
        try {
          const r = await axios.post('https://polygon-rpc.com', {
            jsonrpc: '2.0', method: 'eth_call',
            params: [{ to: contract, data: balanceOfSig }, 'latest'],
            id: 1
          }, { timeout: 8000 });

          if (r.data?.result && r.data.result !== '0x') {
            const raw = BigInt(r.data.result);
            totalBalance += Number(raw) / 1e6; // USDC has 6 decimals
          }
        } catch (e) {
          // Skip this contract, try next
        }
      }

      this.log('info', 'USDC balance fetched', { address: address.slice(0, 10) + '...', balance: totalBalance.toFixed(2) });
      return +totalBalance.toFixed(2);
    } catch (e) {
      this.log('warn', 'Failed to fetch USDC balance', { error: e.message });
      return null;
    }
  }

  // ── Conditional Token Redemption ─────────────────────────────────────
  // After a market resolves, winning tokens must be redeemed on-chain
  // to convert back to USDC. Without this, USDC stays locked forever.

  // Polymarket contract addresses on Polygon
  static CTF_ADDRESS = '0x4D97DCd97eC945f40cF65F87097ACe5EA0476045';
  static NEG_RISK_ADAPTER = '0xC5d563A36AE78145C45a50134d48A1215220f80a';
  static USDC_E = '0x2791Bca1f2de4661ED88A30C99A7a9449Aa84174';
  static POLYGON_RPC = 'https://polygon-rpc.com';

  // Minimal ABI for ConditionalTokens.redeemPositions + balanceOf
  static CTF_ABI = [
    'function redeemPositions(address collateralToken, bytes32 parentCollectionId, bytes32 conditionId, uint256[] indexSets)',
    'function balanceOf(address owner, uint256 positionId) view returns (uint256)',
    'function payoutDenominator(bytes32 conditionId) view returns (uint256)',
    'function payoutNumerators(bytes32 conditionId, uint256 index) view returns (uint256)'
  ];

  static NEG_RISK_ABI = [
    'function redeemPositions(bytes32 conditionId, uint256[] indexSets)'
  ];

  // ERC-20 ABI for USDC allowance checks
  static ERC20_ABI = [
    'function allowance(address owner, address spender) view returns (uint256)',
    'function approve(address spender, uint256 amount) returns (bool)',
    'function balanceOf(address account) view returns (uint256)'
  ];

  // Polymarket CTF Exchange (where CLOB orders settle)
  static CTF_EXCHANGE = '0x4bFb41d5B3570DeFd03C39a9A4D8dE6Bd8B8982E';
  static NEG_RISK_CTF_EXCHANGE = '0xC5d563A36AE78145C45a50134d48A1215220f80a';

  // Minimal Gnosis Safe ABI for execTransaction routing (Polymarket email/Magic accounts)
  static SAFE_ABI = [
    'function execTransaction(address to, uint256 value, bytes data, uint8 operation, uint256 safeTxGas, uint256 baseGas, uint256 gasPrice, address gasToken, address refundReceiver, bytes signatures) payable returns (bool)',
    'function nonce() view returns (uint256)',
    'function getOwners() view returns (address[])'
  ];

  // ── Safe-mode helpers ────────────────────────────────────────────────

  /** Polymarket proxy wallet address when set, else null. */
  _getFunder() {
    return this.db?.getSettingInternal('polymarket_funder_address') || null;
  }

  /** True if the user is a Polymarket Magic account using a Gnosis Safe proxy. */
  _isGnosisSafeMode() {
    return this._signatureType === SIG_TYPE_POLY_GNOSIS_SAFE;
  }

  /** True if the user is a Polymarket Magic account using either proxy type. */
  _isProxyMode() {
    return this._signatureType === SIG_TYPE_POLY_PROXY || this._signatureType === SIG_TYPE_POLY_GNOSIS_SAFE;
  }

  /** Legacy alias kept for the rest of clob.js — true if any funder is configured. */
  _isSafeMode() {
    return !!this._getFunder();
  }

  // Polygon RPC endpoints in fallback order. We try each until one succeeds,
  // because a wrong signature type will cause orders to sign incorrectly at
  // live-trading time, so silently defaulting is not acceptable.
  static POLYGON_RPCS = [
    'https://polygon-bor-rpc.publicnode.com',
    'https://polygon-rpc.com',
    'https://rpc.ankr.com/polygon',
    'https://polygon.llamarpc.com',
    'https://1rpc.io/matic'
  ];

  /**
   * Detect a Polymarket proxy wallet's signature type by inspecting its bytecode.
   * Returns:
   *   1 (POLY_PROXY) — old Polymarket proxy implementation
   *   2 (POLY_GNOSIS_SAFE) — Gnosis Safe minimal proxy or full Safe deployment
   *   null — no contract code at the address (predicted/undeployed, wrong addr,
   *          OR every RPC in the fallback list failed — we do NOT guess)
   */
  async _detectSignatureType(funderAddress) {
    // 1. Manual override via setting — lets users force the type if autodetect
    //    is wrong or RPCs are unavailable. Accepts '1'/'2' or 'poly_proxy'/'gnosis_safe'.
    const override = this.db?.getSetting('polymarket_signature_type');
    if (override) {
      const n = String(override).toLowerCase();
      if (n === '1' || n === 'poly_proxy') {
        this.log('info', 'Signature type: POLY_PROXY (manual override)');
        return SIG_TYPE_POLY_PROXY;
      }
      if (n === '2' || n === 'gnosis_safe' || n === 'gnosis') {
        this.log('info', 'Signature type: POLY_GNOSIS_SAFE (manual override)');
        return SIG_TYPE_POLY_GNOSIS_SAFE;
      }
    }

    // 2. Autodetect by querying bytecode across a fallback list of RPCs.
    let lastErr = null;
    for (const rpc of PolymarketCLOB.POLYGON_RPCS) {
      try {
        const r = await axios.post(rpc, {
          jsonrpc: '2.0', id: 1, method: 'eth_getCode',
          params: [funderAddress, 'latest']
        }, { timeout: 6000 });
        const code = r.data?.result;
        if (typeof code !== 'string') {
          lastErr = new Error('RPC returned non-string code');
          continue;
        }
        if (code === '0x' || code === '') return null; // no contract at this address

        // EIP-1167 minimal proxy bytecode embeds the implementation address at
        // hex offset 22..62 (20-byte impl).
        // Pattern: 363d3d373d3d3d363d73<20-byte impl>5af43d82803e903d91602b57fd5bf3
        const lower = code.toLowerCase();
        if (lower.startsWith('0x363d3d373d3d3d363d73')) {
          const impl = '0x' + lower.slice(22, 62);
          if (impl === POLY_PROXY_IMPL.toLowerCase()) {
            this.log('info', 'Signature type: POLY_PROXY (autodetected via bytecode)', { rpc });
            return SIG_TYPE_POLY_PROXY;
          }
          this.log('info', 'Signature type: POLY_GNOSIS_SAFE (EIP-1167 with non-POLY_PROXY impl)', { rpc, impl });
          return SIG_TYPE_POLY_GNOSIS_SAFE;
        }
        // Non-minimal-proxy contract — assume a fully-deployed Gnosis Safe.
        this.log('info', 'Signature type: POLY_GNOSIS_SAFE (full contract, not EIP-1167)', { rpc });
        return SIG_TYPE_POLY_GNOSIS_SAFE;
      } catch (e) {
        lastErr = e;
        // Try next RPC
      }
    }

    // Every RPC failed — do NOT guess. Return null so the caller errors out
    // and the user can set polymarket_signature_type manually.
    this.log('error', 'Signature type autodetect failed on all RPCs', { error: lastErr?.message });
    return null;
  }

  /**
   * Build a Gnosis Safe "pre-validated" signature for a 1-of-1 Safe where the
   * EOA submitting the tx is also the sole owner. Saves us from doing EIP-712.
   * Format: 32-byte owner (left-padded) || 32 zero bytes || 1-byte v=1
   */
  _buildSafePreValidatedSignature(ownerAddress) {
    const r = ethers.zeroPadValue(ownerAddress, 32);
    const s = ethers.ZeroHash;
    const v = '0x01';
    return ethers.concat([r, s, v]);
  }

  /**
   * Execute an arbitrary call through the user's Polymarket Gnosis Safe.
   * Uses the EOA signer to submit + a pre-validated signature (cheap, no EIP-712).
   * Requires the EOA to hold a small amount of MATIC for gas.
   */
  async _execThroughSafe(to, data, { gasLimit = 400000 } = {}) {
    const conn = this._getProviderAndSigner();
    if (!conn) return { success: false, error: 'No wallet configured' };

    const funder = this._getFunder();
    if (!funder) return { success: false, error: 'No Polymarket funder/Safe address configured' };

    try {
      const ownerAddress = await conn.signer.getAddress();
      const safe = new ethers.Contract(funder, PolymarketCLOB.SAFE_ABI, conn.signer);
      const signatures = this._buildSafePreValidatedSignature(ownerAddress);
      const gasPrice = await this._getGasPrice();

      const tx = await safe.execTransaction(
        to,
        0n,             // value
        data,
        0,              // operation: CALL
        0n,             // safeTxGas (let Safe estimate)
        0n,             // baseGas
        0n,             // gasPrice (no refund)
        ethers.ZeroAddress, // gasToken
        ethers.ZeroAddress, // refundReceiver
        signatures,
        { gasPrice, gasLimit }
      );

      this.log('info', 'Safe execTransaction submitted', { to, txHash: tx.hash, funder: funder.slice(0, 10) + '...' });
      const receipt = await tx.wait(1);
      this.log('info', 'Safe execTransaction confirmed', { txHash: tx.hash, blockNumber: receipt.blockNumber });
      return { success: true, txHash: tx.hash, blockNumber: receipt.blockNumber, gasUsed: Number(receipt.gasUsed || 0) };
    } catch (e) {
      this.log('error', 'Safe execTransaction failed', { error: e.message, to });
      return { success: false, error: e.message };
    }
  }

  /**
   * Get an ethers Provider + Signer for Polygon on-chain calls.
   * Caches the provider to avoid repeated connections.
   */
  _getProviderAndSigner() {
    if (!this._provider) {
      // Iterate the fallback list; use staticNetwork to skip ethers' async
      // auto-detect probe on construction (polygon-rpc.com has been flaky).
      const staticNet = ethers.Network.from(137);
      for (const url of PolymarketCLOB.POLYGON_RPCS) {
        try {
          this._provider = new ethers.JsonRpcProvider(url, staticNet, { staticNetwork: staticNet });
          break;
        } catch (e) {
          this.log('warn', 'Polygon RPC provider construction failed', { url, error: e.message });
        }
      }
      if (!this._provider) {
        this._provider = new ethers.JsonRpcProvider(PolymarketCLOB.POLYGON_RPCS[0]);
      }
    }
    const privateKey = this.db?.getSettingInternal('private_key');
    if (!privateKey) return null;
    const signer = new ethers.Wallet(privateKey, this._provider);
    return { provider: this._provider, signer };
  }

  /**
   * Redeem winning conditional tokens for a resolved market.
   * @param {string} conditionId - The market's conditionId
   * @param {boolean} negRisk - Whether this is a negRisk market
   * @param {string} winningSide - 'YES' or 'NO'
   * @returns {{ success, txHash, error, redeemed }}
   */
  async redeemPositions(conditionId, negRisk = false, winningSide = 'YES') {
    const conn = this._getProviderAndSigner();
    if (!conn) return { success: false, error: 'No wallet configured' };

    const { signer } = conn;

    try {
      // Determine which indexSet to redeem
      // YES = outcome index 0 → indexSet 1 (binary 01)
      // NO = outcome index 1 → indexSet 2 (binary 10)
      const indexSets = winningSide === 'YES' ? [1] : [2];

      // Estimate gas before sending
      const gasPrice = await this._getGasPrice();

      // Build the calldata for redeemPositions on the target contract
      const targetAddress = negRisk ? PolymarketCLOB.NEG_RISK_ADAPTER : PolymarketCLOB.CTF_ADDRESS;
      const targetAbi = negRisk ? PolymarketCLOB.NEG_RISK_ABI : PolymarketCLOB.CTF_ABI;
      const targetIface = new ethers.Interface(targetAbi);
      const redeemData = negRisk
        ? targetIface.encodeFunctionData('redeemPositions', [conditionId, indexSets])
        : targetIface.encodeFunctionData('redeemPositions', [
            PolymarketCLOB.USDC_E,
            ethers.ZeroHash, // parentCollectionId = 0 for root positions
            conditionId,
            indexSets
          ]);

      // Gnosis Safe mode: route the redeem call through Safe.execTransaction
      if (this._isGnosisSafeMode()) {
        this.log('info', 'Redemption via Safe exec', {
          conditionId: conditionId.slice(0, 16) + '...',
          side: winningSide,
          negRisk
        });
        const safeResult = await this._execThroughSafe(targetAddress, redeemData, { gasLimit: 500000 });
        if (safeResult.success) {
          return {
            success: true,
            txHash: safeResult.txHash,
            gasUsed: safeResult.gasUsed,
            blockNumber: safeResult.blockNumber,
            redeemed: true
          };
        }
        // Fall through to the catch handler's revert-detection logic
        throw new Error(safeResult.error || 'Safe exec failed');
      }

      // POLY_PROXY mode: the old Polymarket proxy wallet implementation
      // (impl 0x44e999d5c2f66ef0861317f9a4805ac2e90aeb4f) uses its own
      // `proxy(...)` entry point to forward arbitrary calls. The ABI for
      // that entry point is NOT currently defined in this codebase — see
      // PolymarketCLOB.SAFE_ABI for the Gnosis-Safe template we'd mirror.
      //
      // Implementing this safely requires: (1) fetching the proxy impl
      // bytecode and confirming the function selector, (2) adding a
      // POLY_PROXY_ABI constant with the exact signature (likely
      // `proxy((address,uint256,bytes,uint8)[] calldata txns)` batched or
      // a simpler `proxy(address,uint256,bytes)` single-call variant —
      // the two known historical versions differ), (3) writing a
      // `_execThroughPolyProxy(to, data)` helper analogous to
      // `_execThroughSafe`. Guessing the ABI will silently encode wrong
      // calldata and burn real MATIC + possibly corrupt the proxy state,
      // so we fail closed and require manual redemption until the ABI is
      // verified on-chain.
      if (this._signatureType === SIG_TYPE_POLY_PROXY) {
        const msg = 'POLY_PROXY proxy ABI not yet implemented — need to add the proxy.proxy(addr, value, data) call. Blocked on: (1) confirming exact function selector from impl 0x44e999d5c2f66ef0861317f9a4805ac2e90aeb4f bytecode, (2) adding POLY_PROXY_ABI constant, (3) writing _execThroughPolyProxy helper mirroring _execThroughSafe. Until then, redeem winning positions manually via polymarket.com → Portfolio.';
        this.log('warn', 'Automated redemption unavailable for POLY_PROXY (ABI not verified)', {
          conditionId: conditionId.slice(0, 16) + '...',
          impl: POLY_PROXY_IMPL
        });
        return { success: false, error: msg };
      }

      // EOA mode (MetaMask / WalletConnect): call the contract directly
      let tx;
      if (negRisk) {
        const adapter = new ethers.Contract(
          PolymarketCLOB.NEG_RISK_ADAPTER,
          PolymarketCLOB.NEG_RISK_ABI,
          signer
        );
        tx = await adapter.redeemPositions(conditionId, indexSets, {
          gasPrice,
          gasLimit: 300000
        });
      } else {
        const ctf = new ethers.Contract(
          PolymarketCLOB.CTF_ADDRESS,
          PolymarketCLOB.CTF_ABI,
          signer
        );
        tx = await ctf.redeemPositions(
          PolymarketCLOB.USDC_E,
          ethers.ZeroHash,  // parentCollectionId = 0 for root positions
          conditionId,
          indexSets,
          { gasPrice, gasLimit: 300000 }
        );
      }

      this.log('info', 'Redemption tx submitted', {
        conditionId: conditionId.slice(0, 16) + '...',
        side: winningSide,
        negRisk,
        txHash: tx.hash
      });

      // Wait for confirmation (up to 60 seconds)
      const receipt = await tx.wait(1);
      const gasUsed = receipt.gasUsed ? Number(receipt.gasUsed) : 0;

      this.log('info', 'Redemption confirmed', {
        txHash: tx.hash,
        gasUsed,
        blockNumber: receipt.blockNumber
      });

      return {
        success: true,
        txHash: tx.hash,
        gasUsed,
        blockNumber: receipt.blockNumber,
        redeemed: true
      };
    } catch (e) {
      // "execution reverted" often means no tokens to redeem (already redeemed or zero balance)
      if (e.message?.includes('execution reverted') || e.message?.includes('revert')) {
        this.log('info', 'Redemption skipped (no tokens to redeem or already redeemed)', {
          conditionId: conditionId.slice(0, 16) + '...'
        });
        return { success: true, redeemed: false, error: 'No tokens to redeem' };
      }
      this.log('error', 'Redemption failed', { conditionId: conditionId.slice(0, 16) + '...', error: e.message });
      return { success: false, error: e.message };
    }
  }

  /**
   * Sweep all resolved positions and redeem winning tokens.
   * Called by scheduler on a timer. Returns summary of redemptions.
   */
  async sweepRedemptions(resolvedPositions) {
    if (!resolvedPositions || !resolvedPositions.length) return { swept: 0, redeemed: 0, errors: 0 };

    let redeemed = 0, errors = 0;
    const results = [];

    // Deduplicate by conditionId (multiple positions in same market only need one redemption)
    const byCondition = new Map();
    for (const pos of resolvedPositions) {
      if (!pos.conditionId) continue;
      if (!byCondition.has(pos.conditionId)) {
        byCondition.set(pos.conditionId, pos);
      }
    }

    for (const [conditionId, pos] of byCondition) {
      try {
        const result = await this.redeemPositions(
          conditionId,
          pos.negRisk || false,
          pos.winningSide || pos.side || 'YES'
        );

        if (result.success && result.redeemed) {
          redeemed++;
          results.push({ conditionId, txHash: result.txHash, status: 'redeemed' });
        } else if (result.success) {
          results.push({ conditionId, status: 'no_tokens' });
        } else {
          errors++;
          results.push({ conditionId, status: 'error', error: result.error });
        }

        // Brief delay between redemptions to avoid nonce conflicts
        await new Promise(r => setTimeout(r, 2000));
      } catch (e) {
        errors++;
        results.push({ conditionId, status: 'error', error: e.message });
      }
    }

    this.log('info', 'Redemption sweep complete', { swept: byCondition.size, redeemed, errors });
    return { swept: byCondition.size, redeemed, errors, results };
  }

  // ── USDC Allowance Management ──────────────────────────────────────
  // The CLOB exchange contract needs USDC approval before it can transfer
  // tokens on your behalf. Without this, orders silently fail.

  /**
   * Check current USDC allowance for the CLOB exchange contract.
   * Returns allowance in USDC (6-decimal adjusted).
   */
  async checkAllowance() {
    const conn = this._getProviderAndSigner();
    if (!conn) return null;

    try {
      const usdc = new ethers.Contract(PolymarketCLOB.USDC_E, PolymarketCLOB.ERC20_ABI, conn.signer);
      // In Safe mode, USDC lives in the Gnosis Safe proxy; the approval is granted
      // by the Safe, not the EOA. Query the funder's allowance instead.
      const address = this._isSafeMode()
        ? this._getFunder()
        : await conn.signer.getAddress();

      // Check allowance for both exchanges
      const [regularAllowance, negRiskAllowance] = await Promise.all([
        usdc.allowance(address, PolymarketCLOB.CTF_EXCHANGE).catch(() => 0n),
        usdc.allowance(address, PolymarketCLOB.NEG_RISK_CTF_EXCHANGE).catch(() => 0n)
      ]);

      return {
        regular: Number(regularAllowance) / 1e6,
        negRisk: Number(negRiskAllowance) / 1e6
      };
    } catch (e) {
      this.log('warn', 'Allowance check failed', { error: e.message });
      return null;
    }
  }

  /**
   * Approve USDC spending for the CLOB exchange contracts.
   * Uses max uint256 approval (standard for DeFi) to avoid repeated approvals.
   * @param {boolean} negRisk - If true, approve the negRisk exchange. If false, regular.
   * @returns {{ success, txHash, error }}
   */
  async approveUSDC(negRisk = false) {
    const conn = this._getProviderAndSigner();
    if (!conn) return { success: false, error: 'No wallet configured' };

    const spender = negRisk
      ? PolymarketCLOB.NEG_RISK_CTF_EXCHANGE
      : PolymarketCLOB.CTF_EXCHANGE;

    try {
      const maxApproval = ethers.MaxUint256;

      // Gnosis Safe mode: the Safe owns the USDC, so the approval call must
      // originate from the Safe via execTransaction. Encode the approve() and route it.
      if (this._isGnosisSafeMode()) {
        const iface = new ethers.Interface(PolymarketCLOB.ERC20_ABI);
        const approveData = iface.encodeFunctionData('approve', [spender, maxApproval]);
        this.log('info', 'USDC approval via Safe exec', { spender: negRisk ? 'negRisk' : 'regular' });
        const result = await this._execThroughSafe(PolymarketCLOB.USDC_E, approveData, { gasLimit: 200000 });
        if (result.success) {
          this.log('info', 'USDC approval confirmed (Safe)', { txHash: result.txHash });
          return { success: true, txHash: result.txHash };
        }
        return { success: false, error: result.error };
      }

      // POLY_PROXY mode: the old proxy handles approvals via its own `proxy()`
      // entry point. Polymarket sets these up automatically on first deposit, so
      // for users on this path the approval should already be in place — orders
      // will fill regardless of what this function reports. Skip with a warning.
      if (this._signatureType === SIG_TYPE_POLY_PROXY) {
        this.log('warn', 'POLY_PROXY accounts: approvals are managed by Polymarket. Skipping local approve.');
        return { success: true, error: 'Approval skipped (POLY_PROXY managed by Polymarket)' };
      }

      // EOA mode: direct approve from the signer
      const usdc = new ethers.Contract(PolymarketCLOB.USDC_E, PolymarketCLOB.ERC20_ABI, conn.signer);
      const gasPrice = await this._getGasPrice();

      const tx = await usdc.approve(spender, maxApproval, {
        gasPrice,
        gasLimit: 100000
      });

      this.log('info', 'USDC approval tx submitted', { spender: negRisk ? 'negRisk' : 'regular', txHash: tx.hash });

      const receipt = await tx.wait(1);
      this.log('info', 'USDC approval confirmed', { txHash: tx.hash, blockNumber: receipt.blockNumber });

      return { success: true, txHash: tx.hash };
    } catch (e) {
      this.log('error', 'USDC approval failed', { error: e.message });
      return { success: false, error: e.message };
    }
  }

  /**
   * Ensure USDC allowance is sufficient before placing an order.
   * Auto-approves if allowance is below the required amount.
   * @param {number} requiredUSD - Amount in USD needed
   * @param {boolean} negRisk - Whether this is a negRisk market
   * @returns {{ sufficient, approved, error }}
   */
  async ensureAllowance(requiredUSD, negRisk = false) {
    try {
      // Proxy-mode short-circuit: for POLY_PROXY / POLY_GNOSIS_SAFE accounts,
      // funds and approvals live on the Polymarket-managed funder wallet, not
      // the EOA. Skip EOA balance/approval RPC entirely.
      if (this._isProxyMode()) {
        return { sufficient: true, reason: 'proxy-mode: approvals managed by Polymarket' };
      }
      const allowance = await this.checkAllowance();
      if (!allowance) return { sufficient: false, error: 'Could not check allowance' };

      const current = negRisk ? allowance.negRisk : allowance.regular;

      if (current >= requiredUSD) {
        return { sufficient: true, approved: false };
      }

      this.log('info', `Allowance insufficient ($${current.toFixed(2)} < $${requiredUSD}), auto-approving...`);
      const result = await this.approveUSDC(negRisk);

      if (result.success) {
        return { sufficient: true, approved: true, txHash: result.txHash };
      }
      return { sufficient: false, error: result.error };
    } catch (e) {
      return { sufficient: false, error: e.message };
    }
  }

  // ── Gas Price Management ───────────────────────────────────────────
  // Polygon transactions need MATIC for gas. Uses gas floor from settings.

  /**
   * Get a safe gas price for Polygon transactions.
   * Enforces a minimum floor to prevent stuck transactions.
   */
  async _getGasPrice() {
    const conn = this._getProviderAndSigner();
    if (!conn) return ethers.parseUnits('50', 'gwei'); // default fallback

    try {
      const feeData = await conn.provider.getFeeData();
      const estimated = feeData.gasPrice || ethers.parseUnits('30', 'gwei');

      // Enforce gas floor from settings (defaults: 30 gwei priority, 60 gwei max)
      const minGwei = this.db?.getSetting('min_gas_price_gwei', 35) || 35;
      const floor = ethers.parseUnits(String(minGwei), 'gwei');

      const gasPrice = estimated > floor ? estimated : floor;
      return gasPrice;
    } catch (e) {
      return ethers.parseUnits('50', 'gwei'); // safe fallback
    }
  }

  /**
   * Check MATIC balance for gas. Returns balance in MATIC.
   */
  async getMATICBalance() {
    const conn = this._getProviderAndSigner();
    if (!conn) return null;
    try {
      const address = await conn.signer.getAddress();
      const balance = await conn.provider.getBalance(address);
      return parseFloat(ethers.formatEther(balance));
    } catch (e) {
      return null;
    }
  }

  // ── Order Failure Circuit Breaker ──────────────────────────────────
  // Pauses live trading after consecutive CLOB order failures to prevent
  // cascading issues from draining the bankroll.

  _orderFailureCount = 0;
  _orderFailureThreshold = 3;
  _orderCircuitBreakerUntil = null;

  /**
   * Record an order failure. If threshold exceeded, activate circuit breaker.
   */
  recordOrderFailure(error) {
    this._orderFailureCount++;
    this.log('warn', `Order failure #${this._orderFailureCount}: ${error}`);

    if (this._orderFailureCount >= this._orderFailureThreshold) {
      this._orderCircuitBreakerUntil = Date.now() + 30 * 60 * 1000; // 30 min pause
      this.log('error', `ORDER CIRCUIT BREAKER ACTIVATED — ${this._orderFailureThreshold} consecutive failures. Paused for 30 minutes.`);

      // Send notifications
      if (this._notifier) {
        this._notifier.send('Order Circuit Breaker', `${this._orderFailureThreshold} consecutive order failures. Trading paused for 30 minutes. Last error: ${error}`, { type: 'error', priority: 'critical' });
      }
      if (this._telegram) {
        this._telegram.send(`🚨 ORDER CIRCUIT BREAKER: ${this._orderFailureThreshold} consecutive failures.\nLast error: ${error}\nTrading paused for 30 minutes.`);
      }
    }
  }

  /**
   * Record a successful order. Resets failure counter.
   */
  recordOrderSuccess() {
    this._orderFailureCount = 0;
  }

  /**
   * Manually clear the order circuit breaker state.
   * Called by the dashboard reset button via server.js:2804.
   */
  resetOrderCircuitBreaker() {
    const wasActive = this.isOrderCircuitBreakerActive();
    this._orderFailureCount = 0;
    this._orderCircuitBreakerUntil = null;
    if (wasActive) {
      this.log('info', 'Order circuit breaker manually reset');
    }
    return { wasActive };
  }

  /**
   * Check if order circuit breaker is active.
   */
  isOrderCircuitBreakerActive() {
    if (!this._orderCircuitBreakerUntil) return false;
    if (Date.now() >= this._orderCircuitBreakerUntil) {
      this._orderCircuitBreakerUntil = null;
      this._orderFailureCount = 0;
      this.log('info', 'Order circuit breaker released — trading resumed');
      return false;
    }
    return true;
  }

  /**
   * Set notifier/telegram references for circuit breaker alerts.
   */
  setNotifiers(notifier, telegram) {
    this._notifier = notifier;
    this._telegram = telegram;
  }

  // ── Position Reconciliation ────────────────────────────────────────
  // Compares internal position state against CLOB open orders to detect
  // orphaned or missing positions.

  /**
   * Reconcile internal positions with CLOB state.
   * Returns { synced, orphanedOrders, missingOrders, mismatches }
   */
  async reconcilePositions(internalPositions) {
    if (!this.isReady()) return { synced: false, error: 'CLOB not ready' };

    try {
      const clobOrders = await this.getOpenOrders();
      const clobOrderIds = new Set(clobOrders.map(o => o.id || o.orderID));

      const orphanedOrders = []; // On CLOB but not in our system
      const missingOrders = [];  // In our system but not on CLOB (may have filled/cancelled)

      // Check CLOB orders against internal
      const internalOrderIds = new Set(
        (internalPositions || [])
          .map(p => p.orderId || p.id)
          .filter(Boolean)
      );

      for (const order of clobOrders) {
        const oid = order.id || order.orderID;
        if (!internalOrderIds.has(oid)) {
          orphanedOrders.push({
            orderId: oid,
            tokenId: order.asset_id,
            side: order.side,
            size: order.original_size,
            price: order.price,
            status: order.status
          });
        }
      }

      // Check internal positions against CLOB (only for non-resolved, live positions)
      for (const pos of (internalPositions || [])) {
        const oid = pos.orderId || pos.id;
        if (oid && !clobOrderIds.has(String(oid)) && !pos.dryRun && pos.status !== 'resolved') {
          // Order not on CLOB — it may have filled, been cancelled, or never placed
          missingOrders.push({
            posId: pos.id,
            market: pos.market,
            orderId: oid,
            side: pos.side,
            size: pos.size
          });
        }
      }

      const synced = orphanedOrders.length === 0 && missingOrders.length === 0;

      if (!synced) {
        this.log('warn', 'Position reconciliation mismatch', {
          orphanedOrders: orphanedOrders.length,
          missingOrders: missingOrders.length
        });
      } else {
        this.log('info', 'Position reconciliation OK', { positions: (internalPositions || []).length });
      }

      return { synced, orphanedOrders, missingOrders };
    } catch (e) {
      this.log('error', 'Reconciliation failed', { error: e.message });
      return { synced: false, error: e.message };
    }
  }

  // ── Status ──────────────────────────────────────────────────────────

  getStatus() {
    return {
      ready: this.ready,
      error: this.error,
      tokenCacheSize: this.tokenCache.size,
      orderCircuitBreaker: this.isOrderCircuitBreakerActive(),
      orderFailures: this._orderFailureCount
    };
  }

  log(level, message, data) {
    console.log(`[CLOB] [${level}] ${message}`, data || '');
    if (this.db) {
      try { this.db.logEvent(level, '[CLOB] ' + message, data); } catch (e) {}
    }
  }
}

module.exports = PolymarketCLOB;
