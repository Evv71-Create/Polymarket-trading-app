/**
 * Server Worker — runs the Express server in a separate Node.js process
 * to prevent the heavy API polling from blocking Electron's main process.
 *
 * Communication with the parent (Electron main) process via IPC:
 *   parent -> worker: { type: 'start', port }
 *   parent -> worker: { type: 'stop' }
 *   worker -> parent: { type: 'started', port }
 *   worker -> parent: { type: 'stopped' }
 *   worker -> parent: { type: 'notification', data: {...} }
 *   worker -> parent: { type: 'error', message }
 *   worker -> parent: { type: 'log', message }
 */

// Electron's forked Node context doesn't expose globalThis.crypto the same way
// standalone Node does, which breaks the CLOB SDK's HMAC signing (it calls
// `globalThis.crypto.subtle.importKey` — fails with "Cannot read properties of
// undefined (reading 'subtle')" and trips the CLOB order circuit breaker after
// 3 consecutive live order failures). Polyfill from Node's built-in webcrypto.
if (!globalThis.crypto || !globalThis.crypto.subtle) {
  try {
    const { webcrypto } = require('crypto');
    globalThis.crypto = webcrypto;
  } catch (e) {
    console.error('[ServerWorker] Failed to polyfill globalThis.crypto:', e.message);
  }
}

const { startServer, stopServer, getLogs, clearLogs, getNotifier } = require('./server');

let started = false;

// ── Heartbeat watchdog ─────────────────────────────────────────────
// If the parent Electron process crashes, `disconnect` may not fire
// reliably on Windows. This watchdog checks every 10s and forces exit
// if the parent has been gone for 30s.
let lastParentPing = Date.now();
let heartbeatInterval = null;

function startHeartbeat() {
  // Parent pings us every 10s via IPC
  heartbeatInterval = setInterval(() => {
    if (!process.connected) {
      console.error('[ServerWorker] Parent disconnected (heartbeat check), exiting...');
      cleanup();
      return;
    }
    // If we haven't received a heartbeat ping in 90s, parent is likely dead
    // (increased from 30s — Electron IPC can be slow under load or when launched from terminal)
    if (Date.now() - lastParentPing > 90000) {
      console.error('[ServerWorker] No heartbeat from parent for 90s, forcing exit...');
      cleanup();
    }
  }, 15000);
}

async function cleanup() {
  if (heartbeatInterval) clearInterval(heartbeatInterval);
  if (started) {
    try { await stopServer(); } catch (e) {}
  }
  process.exit(0);
}

process.on('message', async (msg) => {
  // Any message from parent counts as heartbeat
  lastParentPing = Date.now();

  if (msg.type === 'heartbeat') {
    // Just update timestamp, already done above
    return;
  }
  if (msg.type === 'start') {
    try {
      await startServer(msg.port || 3000);
      started = true;
      startHeartbeat();
      process.send({ type: 'started', port: msg.port || 3000 });

      // Wire notifications to forward to parent process
      const checkNotifier = (retries = 20) => {
        const notif = getNotifier();
        if (notif) {
          // Override the IPC sender to forward to parent instead of webContents
          notif.setIPC({
            isDestroyed: () => !process.connected,
            send: (channel, data) => {
              if (process.connected) {
                process.send({ type: 'notification', channel, data });
              }
            }
          });
          process.send({ type: 'log', message: 'Notification bridge connected to parent' });
        } else if (retries > 0) {
          setTimeout(() => checkNotifier(retries - 1), 500);
        }
      };
      checkNotifier();
    } catch (e) {
      process.send({ type: 'error', message: e.message });
    }
  } else if (msg.type === 'stop') {
    try {
      if (heartbeatInterval) { clearInterval(heartbeatInterval); heartbeatInterval = null; }
      await stopServer();
      started = false;
      process.send({ type: 'stopped' });
    } catch (e) {
      process.send({ type: 'error', message: 'Stop failed: ' + e.message });
    }
  }
});

// Parent disconnected — clean up and exit
process.on('disconnect', () => {
  console.error('[ServerWorker] Parent disconnected, cleaning up...');
  cleanup();
});

process.on('uncaughtException', (e) => {
  console.error('[ServerWorker] Uncaught:', e.message);
  if (process.connected) {
    process.send({ type: 'error', message: 'Uncaught: ' + e.message });
  }
});

process.on('unhandledRejection', (reason) => {
  console.error('[ServerWorker] Unhandled rejection:', reason);
  if (process.connected) {
    process.send({ type: 'error', message: 'Unhandled rejection: ' + (reason?.message || reason) });
  }
});
