/**
 * Scheduler
 * Fixes: direct function calls (no self-HTTP), reliable daily summary timing,
 *        auto-watch wallet cap/cleanup, decay checking, stale position cleanup
 */

const axios = require('axios');
const ApiCache = require('./api-cache'); // I3: API response caching

const GAMMA = 'https://gamma-api.polymarket.com';
const DATA  = 'https://data-api.polymarket.com';

class Scheduler {
  constructor({ db, risk, monitor, signal, notifier, analytics, rateLimiter, audit, telegram }) {
    this.db = db;
    this.risk = risk;
    this.monitor = monitor;
    this.signal = signal;
    this.notifier = notifier;
    this.analytics = analytics;
    this.rateLimiter = rateLimiter;
    this.audit = audit;
    this.telegram = telegram;
    this.tasks = new Map();
    this.running = false;
    this._dailySummaryTimer = null;
    this._apiCache = new ApiCache(); // I3: shared response cache
  }

  start() {
    if (this.running) return;
    this.running = true;
    this.log('info', 'Scheduler started');

    if (this.monitor) this.monitor.start(); // uses monitor's default (30s)

    // Leaderboard refresh — every 15 minutes (direct API call, no self-HTTP)
    this.schedule('leaderboard', 15 * 60 * 1000, () => this.refreshLeaderboard());

    // Health check — every 2 minutes
    this.schedule('health', 2 * 60 * 1000, () => this.healthCheck());

    // Risk daily reset — every minute
    this.schedule('riskReset', 60 * 1000, () => { if (this.risk) this.risk.checkDailyReset(); });

    // Stale position cleanup — every 3 minutes
    this.schedule('stalePositions', 3 * 60 * 1000, () => { if (this.risk) this.risk.closeStalePositions(); });

    // Wallet decay check — every hour
    this.schedule('decayCheck', 60 * 60 * 1000, () => this.checkWalletDecay());

    // Auto-watch cleanup — every 30 minutes
    this.schedule('autoWatchCleanup', 30 * 60 * 1000, () => this.cleanupAutoWatch());

    // Position exit monitoring — every 60 seconds
    this.schedule('positionExits', 60 * 1000, () => this.checkPositionExits());

    // Auto-recommend top wallets — every 30 minutes
    this.schedule('autoRecommend', 30 * 60 * 1000, () => this.autoRecommendWallets());

    // Focused wallet rotation — every 15 minutes
    this.schedule('focusedWalletRotation', 15 * 60 * 1000, () => this.rotateFocusedWallets());

    // Market context analysis — every 5 minutes
    this.schedule('marketContext', 5 * 60 * 1000, () => this.analyzeMarketContext());

    // Unrealized P&L tracking — every 5 minutes (feeds drawdown protection)
    this.schedule('unrealizedPnL', 5 * 60 * 1000, () => this.updateUnrealizedPnL());

    // Hourly performance data for time-of-day confidence scoring — runs daily
    this.schedule('hourlyPerf', 24 * 60 * 60 * 1000, () => this.computeHourlyPerformance());

    // Funding rates for crypto confidence prior — every 15 minutes
    this.schedule('fundingRates', 15 * 60 * 1000, () => this.fetchFundingRates());

    // Rejected signal audit — every 6 hours (opportunity cost analysis)
    this.schedule('rejectedSignalAudit', 6 * 60 * 60 * 1000, () => this.auditRejectedSignals());

    // High-water-mark / withdrawal threshold check — weekly
    this.schedule('withdrawalCheck', 7 * 24 * 60 * 60 * 1000, () => this.checkWithdrawalThreshold());

    // G5: Weekly ToS monitoring
    if (this._tosTimer) clearInterval(this._tosTimer);
    this._tosTimer = setInterval(() => this.checkTosChanges(), 7 * 24 * 60 * 60 * 1000);
    this._startupTimers = this._startupTimers || [];
    this._startupTimers.push(setTimeout(() => this.checkTosChanges(), 5 * 60 * 1000));

    // ST8: Confidence calibration curve — weekly (30d overflows 32-bit int → 1ms loop)
    this.schedule('confidenceCalibration', 7 * 24 * 60 * 60 * 1000, () => this.calibrateConfidenceScores());
    // Also run once on startup after 60 seconds (tracker fully populated by then)
    this._startupTimers.push(setTimeout(() => this.calibrateConfidenceScores(), 60 * 1000));

    // G3: Daily P&L attribution (wallet × category × hour-of-day)
    this.schedule('pnlAttribution', 24 * 60 * 60 * 1000, () => this.attributePnL());
    this._startupTimers.push(setTimeout(() => this.attributePnL(), 90 * 1000)); // run 90s after startup

    // I3: Evict expired API cache entries every 5 minutes to prevent memory growth
    this.schedule('apiCacheEvict', 5 * 60 * 1000, () => this._apiCache?.evictExpired());

    // Redemption sweep — every 10 minutes, redeem winning conditional tokens to USDC
    this.schedule('redemptionSweep', 10 * 60 * 1000, () => this.sweepRedemptions());
    // Also run 2 minutes after startup to catch positions that resolved while app was down
    this._startupTimers = this._startupTimers || [];
    this._startupTimers.push(setTimeout(() => this.sweepRedemptions(), 2 * 60 * 1000));

    // Position reconciliation — every hour, verify internal state matches CLOB
    this.schedule('positionReconciliation', 60 * 60 * 1000, () => this.reconcilePositions());
    // Run 5 minutes after startup
    this._startupTimers.push(setTimeout(() => this.reconcilePositions(), 5 * 60 * 1000));

    // On-chain reconciliation — catches silent-corruption bugs where local
    // positions don't have matching on-chain trades (phantoms) or on-chain
    // trades exist without local records (orphans). Fast cadence (2 min) so
    // drift is caught before it can compound. Runs 30s after startup.
    const reconcileInterval = this.db?.getSetting?.('reconcile_intervalMs', 2 * 60 * 1000) || 2 * 60 * 1000;
    this.schedule('reconcileOnChain', reconcileInterval, () => this.reconcileOnChain());
    this._startupTimers.push(setTimeout(() => this.reconcileOnChain(), 30 * 1000));

    // Schedule daily summary at 23:55
    this._scheduleDailySummary();

    // Startup tasks — store handles so stop() can cancel them
    this._startupTimers.push(setTimeout(() => this.refreshLeaderboard(), 5000));
    this._startupTimers.push(setTimeout(() => this.healthCheck(), 3000));
    this._startupTimers.push(setTimeout(() => this.autoRecommendWallets(), 2 * 60 * 1000));
    this._startupTimers.push(setTimeout(() => this.rotateFocusedWallets(), 3 * 60 * 1000));
    this._startupTimers.push(setTimeout(() => this.auditRejectedSignals(), 10 * 60 * 1000));

    // Auto-enable signal engine for auto-copy pipeline
    if (this.signal && !this.signal.enabled) {
      this.signal.enable();
      this.log('info', 'Signal engine auto-enabled by scheduler');
    }

    this.log('info', 'All scheduled tasks running');
  }

  stop() {
    for (const [name, task] of this.tasks.entries()) {
      clearInterval(task);
      this.log('info', `Stopped task: ${name}`);
    }
    this.tasks.clear();
    if (this._dailySummaryTimer) { clearTimeout(this._dailySummaryTimer); this._dailySummaryTimer = null; }
    if (this._tosTimer) { clearInterval(this._tosTimer); this._tosTimer = null; }
    if (this._startupTimers) { this._startupTimers.forEach(t => clearTimeout(t)); this._startupTimers = []; }
    if (this.monitor) this.monitor.stop();
    this.running = false;
    this.log('info', 'Scheduler stopped');
  }

  schedule(name, intervalMs, fn) {
    const interval = setInterval(async () => {
      try { await fn(); }
      catch (e) { this.log('error', `Task ${name} failed`, { error: e.message }); }
    }, intervalMs);
    this.tasks.set(name, interval);
  }

  // ── Daily summary — reliable scheduling via setTimeout chain ──────

  _scheduleDailySummary() {
    const now = new Date();
    const target = new Date(now);
    target.setHours(23, 55, 0, 0);
    if (target <= now) target.setDate(target.getDate() + 1);

    const delay = target.getTime() - now.getTime();
    this._dailySummaryTimer = setTimeout(() => {
      this.sendDailySummary();
      // Re-schedule for tomorrow
      this._scheduleDailySummary();
    }, delay);

    this.log('info', `Daily summary scheduled in ${Math.round(delay / 60000)} minutes`);
  }

  // ── Leaderboard — direct API call, no self-HTTP ───────────────────

  async refreshLeaderboard() {
    if (this.rateLimiter && !this.rateLimiter.consume('polymarket_data')) {
      this.log('warn', 'Rate limited — skipping leaderboard refresh');
      return;
    }

    try {
      // /leaderboard endpoint is gone (404) — aggregate from /trades instead
      const r = await axios.get(`${DATA}/trades`, { params: { limit: 200 }, timeout: 15000 });
      if (this.rateLimiter) this.rateLimiter.clearBackoff('polymarket_data');

      const trades = r.data || [];
      if (!trades.length) return;

      // Aggregate by wallet
      const wallets = {};
      for (const t of trades) {
        const addr = t.proxyWallet;
        if (!addr) continue;
        if (!wallets[addr]) wallets[addr] = { address: addr, name: t.name || t.pseudonym || addr.slice(0, 8) + '...', trades: 0, volume: 0 };
        wallets[addr].trades++;
        wallets[addr].volume += parseFloat(t.usdcSize || 0) || (parseFloat(t.size || 0) * parseFloat(t.price || 0));
      }

      const traders = Object.values(wallets).sort((a, b) => b.volume - a.volume).slice(0, 20);

      // Save snapshots
      if (this.db) {
        traders.slice(0, 10).forEach((t, i) => {
          try {
            this.db.saveWalletSnapshot({
              address: t.address, name: t.name,
              roi: 0, win_rate: 0,
              volume: t.volume,
              trade_count: t.trades, rank: i + 1
            });
          } catch (e) {}
        });
      }

      // Auto-watch top wallets if configured
      if (this.monitor && this.db) {
        const autoWatch = this.db.getSetting('scheduler_autoWatchTop', false);
        const maxAutoWatch = this.db.getSetting('scheduler_maxAutoWatchWallets', 10);

        if (autoWatch && this.monitor.wallets.size < maxAutoWatch) {
          traders
            .slice(0, Math.max(0, maxAutoWatch - this.monitor.wallets.size))
            .forEach(t => {
              if (t.address && !this.monitor.wallets.has(t.address)) {
                this.monitor.watch(t.address, t.name, {
                  winRate: 0,
                  volume: t.volume,
                  autoCopy: this.db.getSetting('scheduler_autoCopy', false)
                });
              }
            });
        }
      }

      this.log('info', `Leaderboard refreshed — ${traders.length} wallets`);
    } catch (e) {
      if (this.rateLimiter && e.response?.status === 429) {
        this.rateLimiter.reportRateLimit('polymarket_data');
      }
      this.log('warn', 'Leaderboard refresh failed', { error: e.message });
    }
  }

  // ── Health check — direct API call ────────────────────────────────

  async healthCheck() {
    if (this.rateLimiter && !this.rateLimiter.consume('polymarket_data')) return;

    try {
      const r = await axios.get(`${GAMMA}/markets`, {
        params: { limit: 1, active: true }, timeout: 8000
      });
      if (this.rateLimiter) this.rateLimiter.clearBackoff('polymarket_data');
      this.log('info', 'Health check OK');
    } catch (e) {
      if (this.rateLimiter && e.response?.status === 429) {
        this.rateLimiter.reportRateLimit('polymarket_data');
      }
      this.log('error', 'Health check failed', { error: e.message });
      if (this.notifier) this.notifier.serverError(`Health check failed: ${e.message}`);
    }
  }

  // ── Wallet decay check ────────────────────────────────────────────

  checkWalletDecay() {
    if (!this.monitor) return;
    const windowDays = this.db?.getSetting('monitor_decayWindowDays', 7) || 7;
    const minTrades = this.db?.getSetting('monitor_decayMinTrades', 5) || 5;
    const thresholdPct = this.db?.getSetting('monitor_decayThresholdPct', 15) || 15;

    // Build protected set from current focused wallets
    const _focusedDecay = this.db?.getSetting('signal_focusedWallets', []) || [];
    const _protectedDecay = new Set(_focusedDecay.map(w => w.toLowerCase()));

    const decayed = this.monitor.checkDecay(windowDays, minTrades, thresholdPct);
    for (const info of decayed) {
      // Never disable a focused (protected) wallet via decay check
      if (_protectedDecay.has((info.address || '').toLowerCase())) continue;

      // Auto-pause copying for declining wallets
      const wallet = this.monitor.wallets.get(info.address);
      if (wallet && wallet.autoCopy) {
        wallet.autoCopy = false;
        this.log('warn', `Auto-copy DISABLED for ${info.name} due to performance decay`, {
          historicalWinRate: info.historicalWinRate,
          recentWinRate: info.recentWinRate,
          dropPct: info.dropPct
        });
      }

      if (this.notifier) {
        this.notifier.walletAlert(info.name,
          `Performance decay: win rate dropped from ${info.historicalWinRate}% to ${info.recentWinRate}% — auto-copy paused`
        );
      }
      if (this.telegram?.enabled) {
        try {
          this.telegram.send(
            `⚠️ *Wallet Decay: ${info.name}*\n` +
            `Win rate: ${info.historicalWinRate}% → ${info.recentWinRate}%\n` +
            `Auto-copy paused for this wallet`
          );
        } catch (e) {}
      }
    }

    // Also check via wallet tracker if available
    if (this._walletTracker) {
      this._checkTrackerDecay();
    }
  }

  /**
   * Check wallet tracker's 3-day vs 7-day win rates for smarter decay detection.
   */
  _checkTrackerDecay() {
    if (!this._walletTracker || !this.monitor) return;

    // Never disable focused wallets via decay checks
    const _focusedTracker = this.db?.getSetting('signal_focusedWallets', []) || [];
    const _protectedTracker = new Set(_focusedTracker.map(w => w.toLowerCase()));

    for (const [addr, wallet] of this.monitor.wallets) {
      if (!wallet.autoCopy) continue;

      // Skip protected wallets
      if (_protectedTracker.has(addr.toLowerCase())) continue;

      const stats = this._walletTracker.getWalletStats(addr);
      if (!stats) continue;

      // If 3-day win rate is significantly worse than 7-day AND has enough data
      if (stats.d3.resolvedTrades >= 5 && stats.d7.resolvedTrades >= 5 &&
          stats.d3.winRate !== null && stats.d7.winRate !== null) {
        const decline = stats.d7.winRate - stats.d3.winRate;
        if (decline >= 15) {
          wallet.autoCopy = false;
          this.log('warn', `Auto-copy DISABLED for ${wallet.name}: 3d win rate ${stats.d3.winRate}% vs 7d ${stats.d7.winRate}%`);
          if (this.notifier) {
            this.notifier.walletAlert(wallet.name,
              `3-day decline: ${stats.d7.winRate}% → ${stats.d3.winRate}% — auto-copy paused`
            );
          }
        }
      }

      // If 24h shows zero activity but wallet was supposed to be active
      if (stats.h24.totalTrades === 0 && stats.d3.totalTrades > 5) {
        this.log('info', `Wallet ${wallet.name} inactive for 24h (was active in 3d window)`);
      }
    }
  }

  // ── Auto-watch cleanup — remove wallets that fell off leaderboard ─

  async cleanupAutoWatch() {
    if (!this.monitor || !this.db) return;
    const autoWatch = this.db.getSetting('scheduler_autoWatchTop', false);
    if (!autoWatch) return;

    const maxAutoWatch = this.db.getSetting('scheduler_maxAutoWatchWallets', 10);
    if (this.monitor.wallets.size <= maxAutoWatch) return;

    // Remove wallets with lowest win rates that exceed the cap
    const wallets = [...this.monitor.wallets.entries()]
      .sort((a, b) => (a[1].winRate || 0) - (b[1].winRate || 0));

    const toRemove = wallets.slice(0, this.monitor.wallets.size - maxAutoWatch);
    for (const [addr, w] of toRemove) {
      this.monitor.unwatch(addr);
      this.log('info', `Auto-removed low-performing wallet: ${w.name}`);
    }
  }

  // ── Auto-recommend & activate top wallets ────────────────────────

  /**
   * Periodically evaluates tracked wallets and auto-activates the best performers.
   *
   * Flow:
   * 1. Get top 3 wallets from the tracker
   * 2. For wallets already watched: update their autoCopy based on current performance
   * 3. For new top wallets: auto-watch + auto-copy if they meet the quality bar
   * 4. Log recommendations with full reasoning
   *
   * The quality bar: must have 3d win rate >= minWinRateCopy (default 60%)
   * and at least 5 resolved trades in the 7d window.
   */
  autoRecommendWallets() {
    if (!this._walletTracker || !this.monitor) return;

    const autoActivate = this.db?.getSetting('scheduler_autoActivateTop', true) ?? true;
    const marketFilter = this.db?.getSetting('scheduler_marketFilter', null) || null;
    const minWinRate = this.risk?.getConfig()?.minWinRateCopy || 60;
    const maxAutoWatch = this.db?.getSetting('scheduler_maxAutoWatchWallets', 10) || 10;

    const top = this._walletTracker.getTopWallets(3, {
      minResolved3d: 3,
      minResolved7d: 5,
      marketFilter
    });

    if (top.length === 0) {
      this.log('info', 'Auto-recommend: not enough tracked data yet');
      return;
    }

    // Store recommendations for the UI
    this._lastRecommendations = {
      timestamp: new Date().toISOString(),
      wallets: top,
      marketFilter,
      autoActivated: []
    };

    this.log('info', `Top wallet recommendations (${top.length}):`, {
      wallets: top.map(w => ({
        rank: w.rank,
        address: w.address.slice(0, 10) + '...',
        score: w.score,
        d3WinRate: w.d3.winRate,
        d7WinRate: w.d7.winRate,
        reasons: w.reasons.slice(0, 3)
      }))
    });

    if (!autoActivate) return;

    for (const rec of top) {
      // Quality gate: must have good 3d OR 7d win rate
      const wr3d = rec.d3.winRate;
      const wr7d = rec.d7.winRate;
      const bestWr = Math.max(wr3d || 0, wr7d || 0);

      if (bestWr < minWinRate) {
        this.log('info', `Skipping ${rec.address.slice(0, 10)}... — best win rate ${bestWr}% < ${minWinRate}%`);
        continue;
      }

      // Already watched?
      const existing = this.monitor.wallets.get(rec.address);
      if (existing) {
        // Update win rate estimate and ensure autoCopy is on for top performers
        if (!existing.autoCopy && bestWr >= minWinRate) {
          existing.autoCopy = true;
          existing.winRate = bestWr;
          this.log('info', `Re-enabled autoCopy for ${existing.name} (win rate ${bestWr}%)`);
          this._lastRecommendations.autoActivated.push(rec.address);
        }
        // Update win rate estimate from tracker
        existing.winRate = bestWr;
        continue;
      }

      // New wallet — add to watchlist + autoCopy if under cap
      if (this.monitor.wallets.size < maxAutoWatch) {
        // Get volume estimate from accumulator data
        const accData = this._getAccumulatorData?.(rec.address);
        const volume = accData?.volume || rec.d7.volume || 0;

        this.monitor.watch(rec.address, `Top${rec.rank} ${rec.address.slice(0, 8)}...`, {
          winRate: bestWr,
          volume,
          autoCopy: true,
          estimatedPortfolio: volume
        });

        this._lastRecommendations.autoActivated.push(rec.address);

        this.log('info', `Auto-activated wallet: Top${rec.rank} ${rec.address.slice(0, 10)}...`, {
          winRate: bestWr, volume: volume.toFixed(0),
          reasons: rec.reasons.slice(0, 3)
        });

        if (this.notifier) {
          this.notifier.send(
            `New Top Wallet Activated (#${rec.rank})`,
            `Win rate: ${bestWr}% | Volume: $${volume.toFixed(0)}\n${rec.reasons.slice(0, 2).join(' | ')}`,
            { type: 'info', priority: 'high' }
          );
        }
        if (this.telegram?.enabled) {
          try {
            this.telegram.send(
              `🏆 *New Top Wallet Activated (#${rec.rank})*\n` +
              `Address: \`${rec.address.slice(0, 12)}...\`\n` +
              `Win rate: ${bestWr}% | Volume: $${volume.toFixed(0)}\n` +
              rec.reasons.slice(0, 3).map(r => `• ${r}`).join('\n')
            );
          } catch (e) {}
        }
      }
    }

    // Disable autoCopy for wallets that have fallen out of the top AND are declining
    // BUT never disable focused (protected) wallets — they are managed separately
    const _focusedNow = this.db?.getSetting('signal_focusedWallets', []) || [];
    const _protectedInRecommend = new Set(_focusedNow.map(w => w.toLowerCase()));

    for (const [addr, wallet] of this.monitor.wallets) {
      if (!wallet.autoCopy) continue;

      // Never auto-disable a focused wallet here — lifecycle/rotation manages them
      if (_protectedInRecommend.has(addr.toLowerCase())) continue;

      const isInTop = top.some(t => t.address === addr);
      if (isInTop) continue;

      // Check if this wallet is still performing well
      const stats = this._walletTracker.getWalletStats(addr);
      if (stats && stats.d3.winRate !== null && stats.d3.resolvedTrades >= 3 && stats.d3.winRate < minWinRate) {
        wallet.autoCopy = false;
        this.log('info', `Disabled autoCopy for ${wallet.name} — fell out of top, 3d win rate ${stats.d3.winRate}%`);
      }
    }
  }

  getRecommendations() {
    return this._lastRecommendations || null;
  }

  // ── Focused wallet rotation — swap underperformers with better passive wallets ─

  /**
   * Compares the current focused wallets against all passively tracked wallets.
   * If a passive wallet clearly outperforms one of the focused wallets, swap them.
   *
   * "Clearly outperforms" means:
   *   - Higher score from signal.findTrustedWallets() scoring
   *   - Score gap of at least 15 points (avoids noisy swaps with unknown wallets)
   *   - The candidate must have at least 15 resolved trades
   *   - The candidate must have a win rate of at least 35%
   *   - The candidate must have made at least 3 trades in the last 7 days
   *   - The wallet being evicted must not be in the PROTECTED_WALLETS list
   *
   * Runs every 15 minutes. Max 1 swap per cycle to avoid thrashing.
   */
  rotateFocusedWallets() {
    if (!this.signal || !this.signal.walletTracker) return;

    // Protect ALL currently-configured focused wallets dynamically — prevents evicting
    // recently-added active wallets before they build lifecycle history
    const _currentFocused = this.db?.getSetting('signal_focusedWallets', []) || [];
    const PROTECTED_WALLETS = new Set(_currentFocused.map(w => w.toLowerCase()));

    const focused = this.db?.getSetting('signal_focusedWallets', null);
    if (!focused || !Array.isArray(focused) || focused.length === 0) {
      this.log('info', 'Focused wallet rotation: no focused wallets configured — skipping');
      return;
    }

    // Get scored candidates from ALL tracked wallets (more than 3 so we see non-focused ones)
    const allCandidates = this.signal.findTrustedWallets(20);
    if (allCandidates.length === 0) {
      this.log('info', 'Focused wallet rotation: not enough tracked data for comparison');
      return;
    }

    // Separate into focused and non-focused
    const focusedSet = new Set(focused.map(f => f.toLowerCase()));
    const focusedScored = [];
    const passiveScored = [];

    for (const c of allCandidates) {
      if (focusedSet.has(c.address.toLowerCase())) {
        focusedScored.push(c);
      } else {
        passiveScored.push(c);
      }
    }

    // For focused wallets that didn't make it into candidates (too few trades, low WR), give them score 0
    for (const addr of focused) {
      const already = focusedScored.some(f => f.address.toLowerCase() === addr.toLowerCase());
      if (!already) {
        const stats = this.signal.walletTracker.getWalletStats(addr);
        focusedScored.push({
          address: addr,
          score: 0,
          winRate: stats?.d7?.winRate ?? stats?.d3?.winRate ?? 0,
          pnl: stats?.d7?.pnl ?? 0,
          resolved: Math.max(stats?.d3?.resolvedTrades ?? 0, stats?.d7?.resolvedTrades ?? 0),
          stats
        });
      }
    }

    if (passiveScored.length === 0) {
      this.log('info', 'Focused wallet rotation: no passive candidates available for comparison');
      return;
    }

    // Sort focused by score ascending (worst first), skipping protected wallets
    // Protected wallets are pushed to the end so they are never the eviction candidate
    focusedScored.sort((a, b) => {
      const aProtected = PROTECTED_WALLETS.has(a.address.toLowerCase()) ? 1 : 0;
      const bProtected = PROTECTED_WALLETS.has(b.address.toLowerCase()) ? 1 : 0;
      if (aProtected !== bProtected) return aProtected - bProtected;
      return a.score - b.score;
    });
    passiveScored.sort((a, b) => b.score - a.score);

    const worstFocused = focusedScored[0];
    const bestPassive = passiveScored[0];

    const MIN_SCORE_GAP = 15;

    this.log('info', 'Focused wallet rotation check:', {
      worstFocused: {
        address: worstFocused.address.slice(0, 10) + '...',
        score: worstFocused.score,
        winRate: worstFocused.winRate,
        pnl: worstFocused.pnl,
        protected: PROTECTED_WALLETS.has(worstFocused.address.toLowerCase())
      },
      bestPassive: {
        address: bestPassive.address.slice(0, 10) + '...',
        score: bestPassive.score,
        winRate: bestPassive.winRate,
        pnl: bestPassive.pnl
      },
      scoreGap: +(bestPassive.score - worstFocused.score).toFixed(2)
    });

    // Never evict a protected wallet
    if (PROTECTED_WALLETS.has(worstFocused.address.toLowerCase())) {
      this.log('info', `Rotation blocked: ${worstFocused.address.slice(0, 10)}... is a protected wallet — no eviction allowed`);
      return;
    }

    // Only swap if the passive wallet is clearly better (raised from 5 to 15)
    if (bestPassive.score - worstFocused.score < MIN_SCORE_GAP) {
      this.log('info', 'Focused wallet rotation: no swap needed — gap too small');
      return;
    }

    // Require candidate to have substantial resolved-trade history (raised from 5 to 15)
    if ((bestPassive.resolved || 0) < 15) {
      this.log('info', `Rotation blocked: ${bestPassive.address.slice(0, 10)}... only has ${bestPassive.resolved} resolved trades (need 15)`);
      return;
    }

    // Require candidate to have a meaningful win rate
    if ((bestPassive.winRate || 0) < 35) {
      this.log('info', `Rotation blocked: ${bestPassive.address.slice(0, 10)}... only has ${bestPassive.winRate}% win rate (need 35%)`);
      return;
    }

    // Require candidate to have traded recently (at least 3 trades in the last 7 days)
    const passiveStats = this.signal.walletTracker.getWalletStats(bestPassive.address);
    const recentTrades = passiveStats?.d7?.totalTrades ?? 0;
    if (recentTrades < 3) {
      this.log('info', `Rotation blocked: ${bestPassive.address.slice(0, 10)}... only has ${recentTrades} trades in the last 7 days (need 3)`);
      return;
    }

    // Perform the swap
    const newFocused = focused.filter(f => f.toLowerCase() !== worstFocused.address.toLowerCase());
    newFocused.push(bestPassive.address);

    this.db.setSetting('signal_focusedWallets', newFocused);

    // Ensure the new wallet is watched + autoCopy
    if (this.monitor && !this.monitor.wallets.has(bestPassive.address)) {
      this.monitor.watch(bestPassive.address, `Rotated ${bestPassive.address.slice(0, 8)}...`, {
        winRate: bestPassive.winRate,
        autoCopy: true
      });
    } else if (this.monitor) {
      const w = this.monitor.wallets.get(bestPassive.address);
      if (w) w.autoCopy = true;
    }

    // Don't unwatch the removed wallet — keep tracking passively
    if (this.monitor) {
      const removed = this.monitor.wallets.get(worstFocused.address);
      if (removed) removed.autoCopy = false;
    }

    const swapMsg = `Swapped out ${worstFocused.address.slice(0, 10)}... (score: ${worstFocused.score}, WR: ${worstFocused.winRate}%, P&L: $${worstFocused.pnl}) ` +
      `→ ${bestPassive.address.slice(0, 10)}... (score: ${bestPassive.score}, WR: ${bestPassive.winRate}%, P&L: $${bestPassive.pnl})`;

    this.log('info', `FOCUSED WALLET ROTATION: ${swapMsg}`);

    if (this.notifier) {
      this.notifier.send(
        'Focused Wallet Rotated',
        swapMsg,
        { type: 'info', priority: 'high', sound: true }
      );
    }

    if (this.telegram?.enabled) {
      try {
        this.telegram.send(
          `🔄 *Focused Wallet Rotation*\n\n` +
          `❌ Removed: \`${worstFocused.address.slice(0, 12)}...\`\n` +
          `   Score: ${worstFocused.score} | WR: ${worstFocused.winRate}% | P&L: $${worstFocused.pnl}\n\n` +
          `✅ Added: \`${bestPassive.address.slice(0, 12)}...\`\n` +
          `   Score: ${bestPassive.score} | WR: ${bestPassive.winRate}% | P&L: $${bestPassive.pnl}`
        );
      } catch (e) {}
    }
  }

  sendDailySummary() {
    if (!this.analytics || !this.notifier) return;
    try {
      const summary = this.analytics.getSummary(1);
      this.notifier.dailySummary({
        trades: summary.totalTrades || 0, wins: summary.wins || 0,
        losses: summary.losses || 0, totalPnL: summary.totalPnL || 0
      });
      this.log('info', 'Daily summary sent');
    } catch (e) {
      this.log('warn', 'Daily summary failed', { error: e.message });
    }
  }

  // ── Position exit monitoring ──────────────────────────────────────

  async checkPositionExits() {
    if (!this.risk) return;

    const status = this.risk.getStatus();
    if (!status.openPositionDetails || status.openPositionDetails.length === 0) return;

    // Fetch current prices for all open position markets
    const priceMap = {};
    const marketsToFetch = [...new Set(status.openPositionDetails.map(p => p.market))];

    for (const market of marketsToFetch) {
      try {
        const price = await this.fetchMarketPrice(market);
        if (price !== null) priceMap[market] = price;
      } catch (e) {
        this.log('warn', `Failed to fetch price for: ${market}`, { error: e.message });
      }
    }

    if (Object.keys(priceMap).length === 0) return;

    // Check all positions against current prices
    const exits = this.risk.checkAllExits(priceMap);

    for (const exit of exits) {
      const pos = exit.position;
      // Skip if this position is already being closed by another subsystem
      if (this.risk._closingPositions?.has(pos.id)) continue;

      this.log('info', `Position exit triggered: ${exit.reason}`, {
        market: pos.market, side: pos.side, pnlPct: exit.pnlPct?.toFixed(1),
        entryPrice: pos.entryPrice, currentPrice: priceMap[pos.market]
      });

      // Notify
      if (this.notifier) {
        const reasonLabels = {
          stop_loss: 'Stop Loss',
          take_profit: 'Take Profit',
          trailing_stop: 'Trailing Stop'
        };
        this.notifier.send(
          `${reasonLabels[exit.reason] || exit.reason}: ${pos.side}`,
          `${pos.market.slice(0, 50)} — P&L: ${exit.pnlPct >= 0 ? '+' : ''}${exit.pnlPct.toFixed(1)}%`,
          { type: exit.pnlPct >= 0 ? 'success' : 'warning', priority: 'high', sound: true }
        );
      }

      // PnL for logging only — exit-engine is the sole authority for recording exits
      const _sideMultiplier = (pos.side || '').toUpperCase() === 'NO' ? -1 : 1;
      const pnlUsd = _sideMultiplier * (priceMap[pos.market] - (parseFloat(pos.entryPrice || pos.price) || 0)) * (parseFloat(pos.size) || 0);

      // Update trade in DB
      if (this.db) {
        try {
          this.db.updateTrade(pos.tradeId, {
            status: 'closed',
            pnl: +pnlUsd.toFixed(2),
            close_reason: exit.reason,
            closed_at: new Date().toISOString()
          });
        } catch (e) {}
      }

      // Record in audit trail
      if (this.audit) {
        this.audit.positionClose(pos, exit.reason);
      }

      // Notify wallet monitor for decay tracking
      if (this.monitor && pos.copied_from_address) {
        this.monitor.recordWalletResult(pos.copied_from_address, pnlUsd);
      }

      // Post-trade learning loop: update signal engine confidence scores
      if (this.signal?.postTradeUpdate) {
        this.signal.postTradeUpdate({
          wallet_address: pos.copied_from_address,
          pnl: pnlUsd,
          entryPrice: pos.entryPrice || pos.price,
          side: pos.side,
          market: pos.market,
          strategyId: pos.strategyId || null
        });
      }

      // Send Telegram alert for exits
      if (this.telegram?.enabled) {
        try {
          const reasonLabels = { stop_loss: 'Stop Loss', take_profit: 'Take Profit', trailing_stop: 'Trailing Stop' };
          await this.telegram.send(
            `${exit.pnlPct >= 0 ? '📈' : '📉'} *Position Exit: ${reasonLabels[exit.reason] || exit.reason}*\n` +
            `📊 ${pos.side} on:\n_${pos.market.slice(0, 50)}_\n\n` +
            `💰 P&L: ${exit.pnlPct >= 0 ? '+' : ''}${exit.pnlPct.toFixed(1)}% ($${pnlUsd >= 0 ? '+' : ''}${pnlUsd.toFixed(2)})`
          );
        } catch (e) {}
      }
    }

    if (exits.length > 0) {
      this.log('info', `Position exit check: ${exits.length} exits triggered out of ${status.openPositionDetails.length} open`);
    }
  }

  /**
   * Parse an end time from a market title containing a time range.
   * E.g. "Will Bitcoin go up between 10:00AM-10:15AM ET on March 25?"
   *       → returns a Date for 10:15 AM ET on March 25 of the current year.
   * Returns null if no parseable time range found.
   */
  _parseMarketEndTime(title) {
    if (!title) return null;
    try {
      // Match patterns like "10:00AM-10:15AM ET", "2:30PM-2:45PM ET"
      const rangeMatch = title.match(/(\d{1,2}:\d{2}\s*[AP]M)\s*[-–]\s*(\d{1,2}:\d{2}\s*[AP]M)\s*(ET|EST|EDT)/i);
      if (!rangeMatch) return null;

      const endTimeStr = rangeMatch[2].replace(/\s/g, '').toUpperCase(); // e.g. "10:15AM"
      const tz = rangeMatch[3].toUpperCase();

      // Parse the date from the title — look for "March 25", "Mar 25", "on March 25", etc.
      const dateMatch = title.match(/(Jan(?:uary)?|Feb(?:ruary)?|Mar(?:ch)?|Apr(?:il)?|May|Jun(?:e)?|Jul(?:y)?|Aug(?:ust)?|Sep(?:tember)?|Oct(?:ober)?|Nov(?:ember)?|Dec(?:ember)?)\s+(\d{1,2})/i);

      const now = new Date();
      let month, day;
      if (dateMatch) {
        const monthNames = { jan: 0, feb: 1, mar: 2, apr: 3, may: 4, jun: 5, jul: 6, aug: 7, sep: 8, oct: 9, nov: 10, dec: 11 };
        month = monthNames[dateMatch[1].slice(0, 3).toLowerCase()];
        day = parseInt(dateMatch[2]);
      } else {
        // No date found — assume today
        month = now.getMonth();
        day = now.getDate();
      }

      // Parse end time
      const timeMatch = endTimeStr.match(/(\d{1,2}):(\d{2})(AM|PM)/);
      if (!timeMatch) return null;
      let hours = parseInt(timeMatch[1]);
      const minutes = parseInt(timeMatch[2]);
      const ampm = timeMatch[3];
      if (ampm === 'PM' && hours !== 12) hours += 12;
      if (ampm === 'AM' && hours === 12) hours = 0;

      // Build the date in ET — detect DST dynamically for "ET"
      let etOffset;
      if (tz === 'EDT') { etOffset = 4; }
      else if (tz === 'EST') { etOffset = 5; }
      else {
        try {
          const testDate = new Date(Date.UTC(now.getFullYear(), month, day, 12, 0, 0));
          const etStr = testDate.toLocaleString('en-US', { timeZone: 'America/New_York', hour: 'numeric', hour12: false });
          const utcHour = testDate.getUTCHours();
          const etHour = parseInt(etStr);
          etOffset = ((utcHour - etHour) + 24) % 24;
        } catch (_) { etOffset = 5; }
      }
      const year = now.getFullYear();
      const utcDate = new Date(Date.UTC(year, month, day, hours + etOffset, minutes, 0));
      return utcDate;
    } catch (e) {
      return null;
    }
  }

  /**
   * Update unrealized P&L for all open positions so the risk engine can see
   * paper losses before they close. Feeds risk.checkDrawdown() correctly.
   */
  async updateUnrealizedPnL() {
    if (!this.risk) return;
    const positions = this.risk.state?.openPositions || [];
    if (positions.length === 0) {
      this.risk.state.unrealizedPnL = 0;
      return;
    }
    let totalUnrealized = 0;
    for (const pos of positions) {
      try {
        const currentPrice = await this.fetchMarketPrice(pos.market);
        if (currentPrice !== null) {
          const entry = parseFloat(pos.entryPrice || pos.price) || 0;
          const size = parseFloat(pos.size || 0);
          const _sideMul = (pos.side || '').toUpperCase() === 'NO' ? -1 : 1;
          const unrealized = _sideMul * (currentPrice - entry) * size;
          totalUnrealized += unrealized;

          // ── R4: Max Adverse Excursion (MAE) tracking ──
          // Track the worst intra-trade drawdown so we can learn the typical
          // worst-case loss before positions recover or close.
          if (unrealized < 0) {
            if (pos._mae === undefined || unrealized < pos._mae) {
              pos._mae = unrealized; // most negative value seen
              pos._maePrice = currentPrice;
            }
          }
        }
      } catch (e) { /* skip on error */ }
    }
    this.risk.state.unrealizedPnL = totalUnrealized;
  }

  /**
   * Record MAE for a closed position into the per-wallet MAE history.
   * Called by exit-engine after a position closes.
   * The MAE history feeds into position sizing — wallets with large typical
   * MAE get smaller Kelly fractions since their trades swing further against us.
   */
  recordPositionMAE(position) {
    if (!position || position._mae === undefined) return;
    const walletAddr = position.copied_from_address;
    if (!walletAddr || !this.db) return;

    try {
      const history = this.db.getSetting('signal_maeHistory', {}) || {};
      if (!history[walletAddr]) history[walletAddr] = [];

      // Store the MAE as a fraction of entry price (normalised)
      const entry = parseFloat(position.entryPrice || position.price) || 0.5;
      const maeFraction = entry > 0 ? Math.abs(position._mae / (entry * parseFloat(position.size || 1))) : 0;
      history[walletAddr].push({ ts: Date.now(), maeFraction, maeUsd: position._mae });

      // Keep last 50 trades per wallet
      if (history[walletAddr].length > 50) history[walletAddr] = history[walletAddr].slice(-50);

      this.db.setSetting('signal_maeHistory', history);
    } catch (e) { /* non-fatal */ }
  }

  /**
   * Fetch current market price from Polymarket.
   * Searches by market name/question since we don't store token IDs in positions.
   * Returns the midpoint price or null if not found.
   */
  async fetchMarketPrice(marketName) {
    // BUG 6.1: If the market title contains a time range that has already ended,
    // don't bother fetching a price — let the resolution watcher handle it.
    const endTime = this._parseMarketEndTime(marketName);
    if (endTime) {
      const now = new Date();
      const graceMs = 5 * 60 * 1000; // 5-minute grace period
      if (now.getTime() > endTime.getTime() + graceMs) {
        this.log('info', `Market ended — skipping price fetch: ${marketName.slice(0, 50)}`, { endTime: endTime.toISOString() });
        return null;
      }
    }

    // I3: Cache market prices for 30 seconds to avoid duplicate Gamma API calls
    // during updateUnrealizedPnL (called with same market for multiple positions)
    const cacheKey = `market_price:${marketName}`;
    const cached = this._apiCache?._store?.get(cacheKey);
    if (cached && Date.now() < cached.expiresAt) return cached.value;

    if (this.rateLimiter && !this.rateLimiter.consume('polymarket_data')) {
      return null; // Skip if rate limited rather than blocking
    }

    try {
      // Search for the market by name via Gamma API
      const r = await axios.get(`${GAMMA}/markets`, {
        params: {
          limit: 5,
          active: true,
          closed: false,
          // Use first 60 chars of market name as search
          title: marketName.slice(0, 60)
        },
        timeout: 8000
      });

      if (this.rateLimiter) this.rateLimiter.clearBackoff('polymarket_data');

      const markets = r.data || [];
      if (markets.length === 0) return null;

      // Find best match — STRICT matching only (no random fallback)
      const normalizedTarget = marketName.toLowerCase().trim();
      const match = markets.find(m =>
        (m.question || m.title || '').toLowerCase().trim() === normalizedTarget
      ) || markets.find(m => {
        const q = (m.question || m.title || '').toLowerCase().trim();
        // Both must significantly overlap — not just any substring
        return (q.length > 20 && normalizedTarget.includes(q)) ||
               (normalizedTarget.length > 20 && q.includes(normalizedTarget));
      });

      if (!match) return null; // No confident match — do NOT fall back to random market

      // Extract price — use outcomePrices if available, otherwise bestBid/bestAsk midpoint
      let fetchedPrice = null;
      if (match.outcomePrices) {
        try {
          const prices = JSON.parse(match.outcomePrices);
          fetchedPrice = parseFloat(prices[0]) || null;
        } catch (e) {}
      }
      if (fetchedPrice === null && match.bestBid && match.bestAsk) {
        fetchedPrice = (parseFloat(match.bestBid) + parseFloat(match.bestAsk)) / 2;
      }
      if (fetchedPrice === null && match.lastTradePrice) {
        fetchedPrice = parseFloat(match.lastTradePrice);
      }

      // I3: Store in cache with 30-second TTL
      if (fetchedPrice !== null && this._apiCache) {
        this._apiCache._store.set(cacheKey, { value: fetchedPrice, expiresAt: Date.now() + 30_000 });
      }

      return fetchedPrice;
    } catch (e) {
      if (this.rateLimiter && e.response?.status === 429) {
        this.rateLimiter.reportRateLimit('polymarket_data');
      }
      this.log('warn', `Price fetch failed for: ${marketName.slice(0, 40)}`, { error: e.message });
      return null;
    }
  }

  // ── Market Context Awareness ─────────────────────────────────────────

  /**
   * Analyze current market conditions to adjust strategy.
   * Detects: momentum regime, volatility level, and overall market health.
   * Stores context for signal engine to use in confidence scoring.
   */
  async analyzeMarketContext() {
    if (this.rateLimiter && !this.rateLimiter.consume('polymarket_data')) return;

    try {
      // Fetch recent trades across all markets to gauge activity
      const axios = require('axios');
      const r = await axios.get('https://data-api.polymarket.com/trades', {
        params: { limit: 100 }, timeout: 10000
      });
      if (this.rateLimiter) this.rateLimiter.clearBackoff('polymarket_data');

      const trades = r.data || [];
      if (trades.length < 10) return;

      const now = Date.now();
      const fiveMinAgo = now - 5 * 60 * 1000;
      const fifteenMinAgo = now - 15 * 60 * 1000;

      // Activity analysis
      const recent5m = trades.filter(t => new Date(t.timestamp || t.created_at).getTime() > fiveMinAgo);
      const recent15m = trades.filter(t => new Date(t.timestamp || t.created_at).getTime() > fifteenMinAgo);

      // Volume analysis
      const totalVolume5m = recent5m.reduce((s, t) => s + (parseFloat(t.usdcSize || 0) || (parseFloat(t.size || 0) * parseFloat(t.price || 0))), 0);
      const totalVolume15m = recent15m.reduce((s, t) => s + (parseFloat(t.usdcSize || 0) || (parseFloat(t.size || 0) * parseFloat(t.price || 0))), 0);

      // Price movement analysis — look for directional bias
      const pricesByMarket = {};
      for (const t of trades) {
        const market = t.market || t.title || 'unknown';
        if (!pricesByMarket[market]) pricesByMarket[market] = [];
        pricesByMarket[market].push({
          price: parseFloat(t.price) || 0,
          time: new Date(t.timestamp || t.created_at).getTime(),
          size: parseFloat(t.usdcSize || 0) || (parseFloat(t.size || 0) * parseFloat(t.price || 0))
        });
      }

      // Volatility: average price range within markets
      let totalRange = 0;
      let marketCount = 0;
      for (const [, prices] of Object.entries(pricesByMarket)) {
        if (prices.length < 3) continue;
        const vals = prices.map(p => p.price).filter(p => p > 0 && p < 1);
        if (vals.length < 3) continue;
        const range = Math.max(...vals) - Math.min(...vals);
        totalRange += range;
        marketCount++;
      }
      const avgVolatility = marketCount > 0 ? totalRange / marketCount : 0;

      // Determine regime
      let regime = 'normal';
      let volumeLevel = 'normal';

      if (avgVolatility > 0.15) regime = 'high_volatility';
      else if (avgVolatility < 0.03) regime = 'low_volatility';

      if (totalVolume5m > 50000) volumeLevel = 'high';
      else if (totalVolume5m < 5000) volumeLevel = 'low';

      // Activity trend: is volume accelerating or decelerating?
      const avgVol5m = recent5m.length > 0 ? totalVolume5m / (5/15) : 0; // normalize to 15m equivalent
      const activityTrend = totalVolume15m > 0 ? avgVol5m / totalVolume15m : 1;

      const context = {
        timestamp: new Date().toISOString(),
        regime,
        volatility: +avgVolatility.toFixed(4),
        volumeLevel,
        volume5m: +totalVolume5m.toFixed(0),
        volume15m: +totalVolume15m.toFixed(0),
        trades5m: recent5m.length,
        trades15m: recent15m.length,
        activityTrend: +activityTrend.toFixed(2), // >1 = accelerating, <1 = decelerating
        marketsActive: marketCount
      };

      this._marketContext = context;

      // Store for signal engine to access
      if (this.db) {
        try { this.db.setSetting('market_context', context); } catch (e) {}
      }

      // Adjust signal engine behavior based on context
      if (this.signal) {
        this.signal._marketContext = context;
      }

      // Warn if conditions are unfavorable
      if (regime === 'high_volatility' && this.notifier) {
        this.notifier.send('Market Alert', `High volatility detected (${(avgVolatility * 100).toFixed(1)}% avg range). Position sizes auto-reduced.`, { type: 'warning', priority: 'medium' });
      }

      this.log('info', 'Market context updated', context);
    } catch (e) {
      if (this.rateLimiter && e.response?.status === 429) {
        this.rateLimiter.reportRateLimit('polymarket_data');
      }
      this.log('warn', 'Market context analysis failed', { error: e.message });
    }
  }

  getMarketContext() {
    return this._marketContext || null;
  }

  // ── Leader/Follower Wallet Detection ─────────────────────────────────

  /**
   * Detect which wallets are leaders (originate trades) vs followers (copy others).
   * Leaders trade first, followers trade the same markets within minutes.
   *
   * Uses wallet tracker data: for each market, find the first wallet to enter.
   * Wallets that are consistently first = leaders. Consistently second = followers.
   */
  detectLeaderFollower() {
    if (!this._walletTracker) return [];

    // Collect all trades grouped by market
    const marketEntries = {}; // market -> [{ wallet, timestamp }]

    for (const [addr, trades] of this._walletTracker.walletTrades) {
      for (const t of trades) {
        if (t.action !== 'BUY') continue;
        const market = t.market || '';
        if (!market) continue;
        if (!marketEntries[market]) marketEntries[market] = [];
        marketEntries[market].push({
          wallet: addr,
          timestamp: new Date(t.timestamp).getTime(),
          price: t.price || 0
        });
      }
    }

    // For each market with multiple wallets, determine order of entry
    const walletTimingStats = {}; // wallet -> { first: n, follower: n, avgLag: ms }

    for (const [, entries] of Object.entries(marketEntries)) {
      if (entries.length < 2) continue;

      // Sort by time — earliest first
      entries.sort((a, b) => a.timestamp - b.timestamp);

      // Unique wallets only (first entry per wallet per market)
      const seen = new Set();
      const unique = [];
      for (const e of entries) {
        if (!seen.has(e.wallet)) {
          seen.add(e.wallet);
          unique.push(e);
        }
      }
      if (unique.length < 2) continue;

      // First wallet is leader, rest are followers
      const leader = unique[0];
      if (!walletTimingStats[leader.wallet]) {
        walletTimingStats[leader.wallet] = { first: 0, follower: 0, totalLag: 0, lagCount: 0 };
      }
      walletTimingStats[leader.wallet].first++;

      for (let i = 1; i < unique.length; i++) {
        const fw = unique[i].wallet;
        if (!walletTimingStats[fw]) {
          walletTimingStats[fw] = { first: 0, follower: 0, totalLag: 0, lagCount: 0 };
        }
        walletTimingStats[fw].follower++;
        walletTimingStats[fw].totalLag += unique[i].timestamp - leader.timestamp;
        walletTimingStats[fw].lagCount++;
      }
    }

    // Score wallets: leader ratio = first / (first + follower)
    const results = [];
    for (const [addr, stats] of Object.entries(walletTimingStats)) {
      const total = stats.first + stats.follower;
      if (total < 5) continue; // Need enough data

      const leaderRatio = stats.first / total;
      const avgLagMs = stats.lagCount > 0 ? stats.totalLag / stats.lagCount : 0;

      results.push({
        address: addr,
        leaderRatio: +leaderRatio.toFixed(3),
        role: leaderRatio > 0.6 ? 'leader' : leaderRatio < 0.3 ? 'follower' : 'mixed',
        firstCount: stats.first,
        followerCount: stats.follower,
        avgLagMinutes: +(avgLagMs / 60000).toFixed(1),
        total
      });
    }

    return results.sort((a, b) => b.leaderRatio - a.leaderRatio);
  }

  /**
   * G3: Cross-dimensional P&L attribution.
   * Breaks down P&L by wallet × category × hour-of-day.
   */
  async attributePnL() {
    try {
      const journal = this.db.getSetting('trade_journal', []);
      if (!journal || journal.length < 5) return;

      const resolved = journal.filter(t => t.pnl !== undefined && t.pnl !== null);
      if (resolved.length < 5) return;

      // Attribution by wallet
      const byWallet = {};
      // Attribution by category
      const byCategory = {};
      // Attribution by hour
      const byHour = {};
      // Attribution by wallet+category
      const byWalletCat = {};

      for (const trade of resolved) {
        const wallet = (trade.wallet || trade.wallet_address || 'unknown').slice(0, 10);
        const cat = (trade.category || 'unknown').toLowerCase();
        const hour = trade.exitTime ? new Date(trade.exitTime).getHours() : -1;
        const pnl = parseFloat(trade.pnl) || 0;

        // By wallet
        if (!byWallet[wallet]) byWallet[wallet] = { pnl: 0, trades: 0, wins: 0 };
        byWallet[wallet].pnl += pnl;
        byWallet[wallet].trades++;
        if (pnl > 0) byWallet[wallet].wins++;

        // By category
        if (!byCategory[cat]) byCategory[cat] = { pnl: 0, trades: 0, wins: 0 };
        byCategory[cat].pnl += pnl;
        byCategory[cat].trades++;
        if (pnl > 0) byCategory[cat].wins++;

        // By hour
        if (hour >= 0) {
          if (!byHour[hour]) byHour[hour] = { pnl: 0, trades: 0, wins: 0 };
          byHour[hour].pnl += pnl;
          byHour[hour].trades++;
          if (pnl > 0) byHour[hour].wins++;
        }

        // By wallet+category
        const wCatKey = `${wallet}:${cat}`;
        if (!byWalletCat[wCatKey]) byWalletCat[wCatKey] = { pnl: 0, trades: 0, wins: 0, wallet, cat };
        byWalletCat[wCatKey].pnl += pnl;
        byWalletCat[wCatKey].trades++;
        if (pnl > 0) byWalletCat[wCatKey].wins++;
      }

      // Sort wallet+category by PnL desc
      const topCombinations = Object.values(byWalletCat)
        .sort((a, b) => b.pnl - a.pnl)
        .slice(0, 20);

      const attribution = {
        byWallet, byCategory, byHour,
        topCombinations,
        totalTrades: resolved.length,
        updatedAt: new Date().toISOString()
      };

      this.db.setSetting('pnl_attribution', attribution);
      console.log(`[Scheduler] G3 attribution: ${resolved.length} trades analyzed, top combo: ${topCombinations[0]?.wallet}:${topCombinations[0]?.cat} $${topCombinations[0]?.pnl?.toFixed(2)}`);
    } catch (err) {
      console.error('[Scheduler] attributePnL error:', err.message);
    }
  }

  async computeHourlyPerformance() {
    if (!this.analytics || !this.db) return;
    try {
      const hourlyData = this.analytics.getByTimeOfDay(90);
      const hourMap = {};
      for (const row of hourlyData) {
        hourMap[row.hour] = { wins: row.wins, trades: row.trades };
      }
      this.db.setSetting('analytics_hourlyWinRate', hourMap);
      this.log('info', 'Hourly performance data updated', { hours: Object.keys(hourMap).length });
    } catch (e) {
      this.log('warn', 'computeHourlyPerformance failed', { error: e.message });
    }
  }

  async fetchFundingRates() {
    try {
      const axios = require('axios');
      const [btc, eth] = await Promise.all([
        axios.get('https://fapi.binance.com/fapi/v1/fundingRate', { params: { symbol: 'BTCUSDT', limit: 1 }, timeout: 5000 }),
        axios.get('https://fapi.binance.com/fapi/v1/fundingRate', { params: { symbol: 'ETHUSDT', limit: 1 }, timeout: 5000 })
      ]);
      this._fundingRates = {
        BTC: parseFloat(btc.data[0]?.fundingRate || 0),
        ETH: parseFloat(eth.data[0]?.fundingRate || 0)
      };
      if (this.signal) this.signal.setFundingRates(this._fundingRates);
      this.log('info', 'Funding rates updated', this._fundingRates);
    } catch (e) { /* non-fatal — Binance API optional */ }
  }

  /**
   * ST7: Audit rejected signals for opportunity cost.
   *
   * Reads rejected-signals.jsonl, looks up each conditionId in the
   * wallet-tracker resolvedMarkets, and calculates what we WOULD have made
   * if we'd taken the trade.
   *
   * The result is saved to signal_rejectedSignalAudit in the DB and surfaced
   * via the /api/signal/learning-state endpoint. Use it to identify which
   * rejection filters are costing us the most money.
   */
  async auditRejectedSignals() {
    if (!this.db || !this._walletTracker) return;

    const lines = this.db.getSetting('signal_activityLog', []);
    if (lines.length === 0) return;

    const resolvedMarkets = this._walletTracker.resolvedMarkets; // Map<assetOrConditionId, {yesWins, question}>
    const reasonCost = {}; // rejectReason -> { count, hypotheticalPnL, wins, losses }
    let totalHypothetical = 0;

    for (const signal of lines) {
      const { conditionId, rejectReason, marketPrice, side, timestamp } = signal;
      if (!conditionId || !rejectReason) continue;

      const resolution = resolvedMarkets.get(conditionId);
      if (!resolution || resolution.yesWins === undefined) continue; // not resolved yet

      const yesWins = resolution.yesWins;
      const tradeSide = (side || 'YES').toUpperCase();
      const won = (tradeSide === 'YES' && yesWins) || (tradeSide === 'NO' && !yesWins);

      // Estimate hypothetical P&L: assume $20 notional at the recorded price
      const notional = 20;
      const price = parseFloat(marketPrice) || 0.5;
      const hypPnL = won ? notional * (1 - price) : -notional * price;

      if (!reasonCost[rejectReason]) {
        reasonCost[rejectReason] = { count: 0, hypotheticalPnL: 0, wins: 0, losses: 0 };
      }
      reasonCost[rejectReason].count++;
      reasonCost[rejectReason].hypotheticalPnL += hypPnL;
      if (won) reasonCost[rejectReason].wins++; else reasonCost[rejectReason].losses++;
      totalHypothetical += hypPnL;
    }

    const summary = {
      updatedAt: new Date().toISOString(),
      totalRejected: lines.length,
      resolvedChecked: Object.values(reasonCost).reduce((s, v) => s + v.count, 0),
      totalHypotheticalPnL: +totalHypothetical.toFixed(2),
      byReason: Object.entries(reasonCost)
        .sort((a, b) => a[1].hypotheticalPnL - b[1].hypotheticalPnL) // worst cost first
        .map(([reason, data]) => ({
          reason,
          count: data.count,
          wins: data.wins,
          losses: data.losses,
          winRate: data.count > 0 ? +((data.wins / data.count) * 100).toFixed(1) : 0,
          hypotheticalPnL: +data.hypotheticalPnL.toFixed(2)
        }))
    };

    try {
      this.db.setSetting('signal_rejectedSignalAudit', summary);
    } catch (e) {}

    this.log('info', 'Rejected signal audit complete', {
      totalRejected: lines.length,
      resolvedChecked: summary.resolvedChecked,
      hypotheticalPnL: summary.totalHypotheticalPnL
    });
  }

  getStatus() {
    return {
      running: this.running,
      tasks: [...this.tasks.keys()],
      monitor: this.monitor?.getStatus() || null,
      signal: this.signal?.getStatus() || null,
      rateLimiter: this.rateLimiter?.getStatus() || null,
      marketContext: this._marketContext || null
    };
  }

  setSetting(key, value) {
    if (this.db) this.db.setSetting('scheduler_' + key, value);
  }

  // ── ST8: Confidence Calibration Curve — monthly check ───────────────

  /**
   * ST8: Confidence Calibration Curve — monthly check
   * Verifies that wallets with score X actually win X% of the time.
   * Auto-corrects wallet confidence adjustments if miscalibrated.
   */
  async calibrateConfidenceScores() {
    try {
      const tracker = this._walletTracker;
      if (!tracker) return;

      const allWallets = tracker.walletTrades ? [...tracker.walletTrades.keys()] : [];
      if (allWallets.length === 0) return;

      const currentAdj = this.db.getSetting('signal_walletConfAdj', {});
      const newAdj = { ...currentAdj };
      const corrections = [];

      for (const addr of allWallets) {
        const stats = tracker.getWalletStats(addr);
        const window = stats?.d30;
        if (!window || window.resolvedTrades < 20) continue; // need sufficient sample

        const adj = currentAdj[addr] || 0;
        // Base Wilson WR (0-100 scale)
        const wins = window.wins || 0;
        const total = window.resolvedTrades || 1;
        const observedWR = (wins / total) * 100;

        // What our system "thinks" about this wallet (rough proxy: 50 + adj)
        const predictedWR = 50 + adj;

        // Calibration error
        const error = observedWR - predictedWR;

        // If error > 10 points, nudge the adjustment toward reality
        if (Math.abs(error) > 10) {
          const correction = Math.sign(error) * Math.min(5, Math.abs(error) * 0.3);
          newAdj[addr] = Math.max(-25, Math.min(25, adj + correction));
          corrections.push({
            addr: addr.slice(0, 10),
            observedWR: observedWR.toFixed(1),
            predictedWR: predictedWR.toFixed(1),
            oldAdj: adj.toFixed(1),
            newAdj: newAdj[addr].toFixed(1)
          });
        }
      }

      if (corrections.length > 0) {
        this.db.setSetting('signal_walletConfAdj', newAdj);
        if (this.signal?.loadLearningState) {
          this.signal.loadLearningState();
        }
        this.notifier?.send('Confidence Calibrated', `Corrected ${corrections.length} wallet confidence scores`, { type: 'info' });
        console.log('[Scheduler] ST8 calibration corrections:', corrections);
      } else {
        console.log('[Scheduler] ST8 calibration: all wallets within 10pt tolerance — no changes');
      }
    } catch (err) {
      console.error('[Scheduler] calibrateConfidenceScores error:', err.message);
    }
  }

  // ── G4: High-water-mark / withdrawal threshold check ────────────────

  async checkWithdrawalThreshold() {
    if (!this.db || !this.risk) return;
    try {
      const bankroll = this.risk.getConfig()?.bankroll || this.db.getSetting('risk_bankroll', 500);
      const hwm = this.db.getSetting('risk_highWaterMark', 0);

      // Update HWM if bankroll is higher
      if (bankroll > hwm) {
        this.db.setSetting('risk_highWaterMark', bankroll);
        this.log('info', `G4: High-water-mark updated to $${bankroll.toFixed(2)}`);
        return; // Just hit a new high — no withdrawal needed yet
      }

      // HWM unchanged: check if we've drifted up from last HWM baseline
      const hwmBaseline = this.db.getSetting('risk_hwmBaseline', bankroll);
      if (bankroll <= hwmBaseline) return; // haven't grown past baseline

      const excess = bankroll - hwmBaseline;
      const withdrawRecommended = +(excess * 0.30).toFixed(2);
      if (withdrawRecommended < 5) return; // not worth notifying under $5

      const msg = `Bankroll $${bankroll.toFixed(2)} is $${excess.toFixed(2)} above baseline. `
                + `Consider withdrawing $${withdrawRecommended} (30% of gains) to lock in profits.`;

      this.log('info', `G4: Withdrawal recommendation — ${msg}`);

      if (this.notifier) {
        this.notifier.send('Profit Withdrawal Recommendation', msg, { type: 'info', sound: false });
      }
      if (this.audit) {
        this.audit.record('WITHDRAWAL_RECOMMENDATION', {
          bankroll, hwmBaseline, excess, withdrawRecommended
        });
      }

      // Advance baseline to current bankroll so we don't re-notify until further growth
      this.db.setSetting('risk_hwmBaseline', bankroll);
    } catch (e) {
      this.log('warn', 'G4 checkWithdrawalThreshold failed', { error: e.message });
    }
  }

  /**
   * G5: Monitor Polymarket ToS page for changes. Halts trading if ToS changes.
   */
  async checkTosChanges() {
    try {
      const crypto = require('crypto');
      const response = await axios.get('https://polymarket.com/tos', {
        timeout: 10000,
        headers: { 'User-Agent': 'Mozilla/5.0 (compatible; polymarket-monitor/1.0)' }
      }).catch(() => null);

      if (!response?.data) return;

      const content = typeof response.data === 'string' ? response.data : JSON.stringify(response.data);
      const hash = crypto.createHash('sha256').update(content).digest('hex');
      const stored = this.db.getSetting('tos_hash', null);

      if (!stored) {
        this.db.setSetting('tos_hash', hash);
        this.db.setSetting('tos_hash_date', new Date().toISOString());
        console.log('[Scheduler] G5 ToS baseline stored');
        return;
      }

      if (hash !== stored) {
        this.db.setSetting('tos_hash', hash);
        this.db.setSetting('tos_hash_date', new Date().toISOString());
        // Notify but do NOT auto-switch to paper — the ToS page is dynamic HTML and hashes
        // change on every request (build IDs, timestamps). Auto-halting would fire on every startup.
        this.notifier?.send('ToS page changed', 'Polymarket ToS page hash changed. Review polymarket.com/tos manually if concerned.', { type: 'warn' });
        console.log('[Scheduler] G5: ToS hash changed (may be dynamic content, not actual ToS update)');
      } else {
        console.log('[Scheduler] G5 ToS unchanged');
      }
    } catch (err) {
      console.error('[Scheduler] checkTosChanges error:', err.message);
    }
  }

  // ── Redemption Sweep ────────────────────────────────────────────────
  // Scans closed/resolved trades and redeems winning conditional tokens
  // back to USDC via the ConditionalTokens contract.

  async sweepRedemptions() {
    const clob = this._clobClient;
    if (!clob || !clob.isReady()) return;

    try {
      // Find resolved winning trades that haven't been redeemed yet.
      // db.js doesn't expose `load()` publicly — use getAllTrades() which
      // is the proper public accessor and returns the same trade list.
      const allTrades = (typeof this.db?.getAllTrades === 'function')
        ? this.db.getAllTrades()
        : [];
      const unredeemed = allTrades.filter(t =>
        t.status === 'won' &&
        !t.redeemed &&
        !t.dry_run &&
        t.conditionId
      );

      if (!unredeemed.length) return;

      this.log('info', `Redemption sweep: ${unredeemed.length} unredeemed winning trades found`);

      const resolvedPositions = unredeemed.map(t => ({
        conditionId: t.conditionId,
        negRisk: t.negRisk || false,
        winningSide: t.side || 'YES',
        tradeId: t.id
      }));

      const result = await clob.sweepRedemptions(resolvedPositions);

      // Mark redeemed trades in DB
      if (result.results) {
        for (const r of result.results) {
          if (r.status === 'redeemed' || r.status === 'no_tokens') {
            const trade = unredeemed.find(t => t.conditionId === r.conditionId);
            if (trade) {
              try {
                this.db.updateTrade(trade.id, {
                  redeemed: true,
                  redemptionTx: r.txHash || null,
                  redeemedAt: new Date().toISOString()
                });
              } catch (e) {}
            }
          }
        }
      }

      if (result.redeemed > 0) {
        this.log('info', `Redeemed ${result.redeemed} positions to USDC`);
        if (this.notifier) {
          this.notifier.send('Redemption Complete', `${result.redeemed} winning positions redeemed to USDC`, { type: 'success' });
        }
        if (this.telegram) {
          this.telegram.send(`💰 Redeemed ${result.redeemed} winning positions to USDC`);
        }
      }
    } catch (e) {
      this.log('error', 'Redemption sweep error', { error: e.message });
    }
  }

  // ── Position Reconciliation ────────────────────────────────────────
  // Compares internal risk engine positions with CLOB open orders to
  // detect orphaned orders or missing positions.

  async reconcilePositions() {
    const clob = this._clobClient;
    if (!clob || !clob.isReady() || !this.risk) return;

    try {
      const positions = this.risk.state?.openPositions || [];
      const livePositions = positions.filter(p => !p.dryRun);

      if (!livePositions.length) return;

      const result = await clob.reconcilePositions(livePositions);

      if (!result.synced && !result.error) {
        // Alert on mismatches
        if (result.orphanedOrders?.length) {
          this.log('warn', `Reconciliation: ${result.orphanedOrders.length} orphaned orders on CLOB not tracked internally`);
          if (this.notifier) {
            this.notifier.send('Position Mismatch', `${result.orphanedOrders.length} orders on CLOB not tracked internally — check positions`, { type: 'warning', priority: 'high' });
          }
        }
        if (result.missingOrders?.length) {
          this.log('warn', `Reconciliation: ${result.missingOrders.length} internal positions not found on CLOB`);
        }
      }
    } catch (e) {
      this.log('error', 'Position reconciliation error', { error: e.message });
    }
  }

  // ── On-chain reconciliation ──────────────────────────────────────────
  //
  // Defense-in-depth against silent-corruption bugs. Compares local open
  // updown positions against actual on-chain trades (via data-api) and:
  //   - Flags PHANTOMS: local positions older than 3 min with no matching
  //     on-chain buy → closes them via risk.recordResult(id, 0) so they
  //     don't block the concurrent-position cap.
  //   - Flags ORPHANS: recent on-chain buys with no matching local position
  //     → logs + audits (doesn't auto-create, to avoid fabricating state).
  //   - Pauses trading if >2 phantoms in a single run (circuit breaker).
  async reconcileOnChain() {
    try {
      if (!this.risk) return;
      // Only run in live mode — paper trades never touch chain
      const cfg = this.risk.getConfig?.();
      if (!cfg || cfg.dryRun === true) return;

      const funder = this.db?.getSettingInternal?.('polymarket_funder_address');
      if (!funder) return;

      // Fetch recent on-chain trades for the funder account
      let onchainTrades = [];
      try {
        const r = await axios.get(`${DATA}/trades`, {
          params: { user: funder, limit: 50, sortBy: 'TIMESTAMP', sortDirection: 'DESC' },
          timeout: 8000
        });
        onchainTrades = r.data || [];
      } catch (e) {
        this.log('warn', 'Reconcile: data-api fetch failed', { error: e.message });
        return;
      }

      const now = Date.now();
      const WINDOW_MS = 15 * 60 * 1000; // 15 min window for on-chain buys
      const MATCH_TOLERANCE_MS = 3 * 60 * 1000; // ±3 min timestamp tolerance
      const PHANTOM_MIN_AGE_MS = 3 * 60 * 1000; // only check positions > 3 min old

      // data-api returns: { side, conditionId, timestamp (unix seconds), ... }
      const recentBuys = onchainTrades
        .filter(t => t && String(t.side || '').toUpperCase() === 'BUY')
        .map(t => ({
          conditionId: t.conditionId || t.condition_id || null,
          timestampMs: (t.timestamp || t.timeStamp || 0) * 1000,
          title: t.title || t.market || t.slug || '(unknown)',
          raw: t
        }))
        .filter(t => t.conditionId && t.timestampMs > 0 && (now - t.timestampMs) < WINDOW_MS);

      const positions = this.risk.state?.openPositions || [];
      // Only reconcile LIVE positions — paper (dryRun) trades have no on-chain backing by design
      const localUpdown = positions.filter(p => p.copied_from === 'updown_strategy' && !p.dryRun);

      let phantoms = 0;
      let orphans = 0;

      // ── ORPHAN detection — on-chain buy with no local record ───────
      for (const trade of recentBuys) {
        const match = localUpdown.find(p =>
          p.conditionId === trade.conditionId &&
          Math.abs((p.openedAt || 0) - trade.timestampMs) < MATCH_TOLERANCE_MS
        );
        if (!match) {
          orphans++;
          this.log('warn', `Reconcile: on-chain orphan (no local pos): ${String(trade.title).slice(0, 60)}, cid=${String(trade.conditionId).slice(0, 20)}, time=${new Date(trade.timestampMs).toISOString()}`);
          try {
            this.audit?.record?.('RECONCILE_ORPHAN', {
              conditionId: trade.conditionId,
              title: String(trade.title).slice(0, 80),
              timestampMs: trade.timestampMs
            });
          } catch (e) {}
        }
      }

      // ── PHANTOM detection — local pos with no on-chain backing ─────
      for (const pos of localUpdown) {
        const age = now - (pos.openedAt || 0);
        if (age < PHANTOM_MIN_AGE_MS) continue; // too fresh to judge
        const match = recentBuys.find(t =>
          t.conditionId === pos.conditionId &&
          Math.abs((pos.openedAt || 0) - t.timestampMs) < MATCH_TOLERANCE_MS
        );
        if (!match) {
          phantoms++;
          const ageMin = (age / 60000).toFixed(1);
          this.log('error', `Reconcile: PHANTOM position (no on-chain match): ${String(pos.market || '').slice(0, 60)}, cid=${String(pos.conditionId || '').slice(0, 20)}, age=${ageMin}min`);
          try {
            this.audit?.record?.('RECONCILE_PHANTOM', {
              positionId: pos.id,
              conditionId: pos.conditionId,
              market: String(pos.market || '').slice(0, 80),
              ageMinutes: +ageMin,
              openedAt: pos.openedAt
            });
          } catch (e) {}
          // Close the phantom via recordResult(id, 0) so it stops blocking the cap
          try {
            if (this.risk?.recordResult) this.risk.recordResult(pos.id, 0);
          } catch (e) {
            this.log('warn', 'Reconcile: recordResult failed for phantom', { id: pos.id, error: e.message });
          }
        }
      }

      // ── Circuit breaker — multiple phantoms = on-chain drift ───────
      if (phantoms > 2) {
        this.log('error', `Reconcile: ${phantoms} phantoms in single run — pausing trading`);
        try {
          this.risk?.pause?.('Reconcile found multiple phantoms — on-chain drift suspected');
        } catch (e) {}
        try {
          if (this.telegram?.send) {
            this.telegram.send(`CRITICAL: Reconcile detected ${phantoms} phantom positions (local state without on-chain backing). Trading paused.`);
          }
        } catch (e) {}
        try {
          this.notifier?.send?.('Reconcile: Trading Paused', `${phantoms} phantom positions detected — on-chain drift suspected`, { type: 'error', priority: 'critical' });
        } catch (e) {}
      }

      this.log('info', `Reconcile: ${recentBuys.length} on-chain buys in window, ${localUpdown.length} local open positions, ${phantoms} phantoms, ${orphans} orphans`);
    } catch (e) {
      // Any exception → log and continue. Must never crash the scheduler.
      this.log('error', 'reconcileOnChain failed', { error: e.message });
    }
  }

  log(level, message, data) {
    console.log(`[Scheduler] [${level}] ${message}`, data || '');
    if (this.db) { try { this.db.logEvent(level, '[Scheduler] ' + message, data); } catch (e) {} }
  }
}

module.exports = Scheduler;
