/**
 * Electron Main Process
 * Server runs in a forked child process to prevent heavy API polling
 * from blocking the Electron main process and causing UI freezes.
 */

const { app, BrowserWindow, ipcMain, shell, Menu, safeStorage } = require('electron');
const path = require('path');
const fs = require('fs');
const { exec, fork } = require('child_process');

const PORT = 3000;
let mainWindow = null;
let serverProcess = null;

// ── Server child process management ──────────────────────────────────

/**
 * Kill any zombie process holding our port before starting.
 * This is the #1 reason the app "stops working" — a previous server
 * child process survived an Electron crash and still holds port 3000.
 */
async function killZombieOnPort(port) {
  return new Promise((resolve) => {
    exec(`netstat -ano | findstr ":${port}.*LISTENING"`, (err, stdout) => {
      if (!stdout) { resolve(); return; }
      const lines = stdout.trim().split('\n');
      const pids = new Set();
      for (const line of lines) {
        const parts = line.trim().split(/\s+/);
        const pid = parseInt(parts[parts.length - 1]);
        if (pid && pid !== process.pid) pids.add(pid);
      }
      if (pids.size === 0) { resolve(); return; }
      console.log(`[App] Killing ${pids.size} zombie process(es) on port ${port}: ${[...pids].join(', ')}`);
      let killed = 0;
      for (const pid of pids) {
        exec(`taskkill /PID ${pid} /F`, () => {
          killed++;
          if (killed >= pids.size) {
            setTimeout(resolve, 500); // Give OS time to release the port
          }
        });
      }
    });
  });
}

function startServerProcess() {
  return new Promise((resolve, reject) => {
    serverProcess = fork(path.join(__dirname, 'server-worker.js'), [], {
      cwd: __dirname,
      stdio: ['pipe', 'pipe', 'pipe', 'ipc']
    });

    // Forward stdout/stderr from server process
    serverProcess.stdout.on('data', (d) => process.stdout.write(d));
    serverProcess.stderr.on('data', (d) => process.stderr.write(d));

    const timeout = setTimeout(() => {
      reject(new Error('Server start timeout'));
    }, 15000);

    serverProcess.on('message', (msg) => {
      if (msg.type === 'started') {
        clearTimeout(timeout);
        console.log(`[App] Server started on port ${msg.port} (child process PID ${serverProcess.pid})`);
        resolve();
      } else if (msg.type === 'error') {
        console.error('[App] Server error:', msg.message);
        clearTimeout(timeout);
        reject(new Error(msg.message));
      } else if (msg.type === 'notification') {
        // Forward notifications from server to renderer
        if (mainWindow && !mainWindow.isDestroyed()) {
          try {
            mainWindow.webContents.send(msg.channel || 'notification', msg.data);
          } catch (e) {}
        }
      } else if (msg.type === 'log') {
        console.log('[ServerWorker]', msg.message);
      }
    });

    serverProcess.on('exit', (code) => {
      console.warn(`[App] Server process exited with code ${code}`);
      if (serverProcess?._heartbeat) clearInterval(serverProcess._heartbeat);
      serverProcess = null;
    });

    // Send heartbeat pings so the worker knows we're alive
    serverProcess._heartbeat = setInterval(() => {
      try {
        if (serverProcess && serverProcess.connected) {
          serverProcess.send({ type: 'heartbeat' });
        }
      } catch (e) {}
    }, 10000);

    serverProcess.send({ type: 'start', port: PORT });
  });
}

function stopServerProcess() {
  return new Promise((resolve) => {
    if (!serverProcess) { resolve(); return; }

    const timeout = setTimeout(() => {
      console.warn('[App] Server stop timeout, killing...');
      try { serverProcess.kill('SIGKILL'); } catch (e) {}
      serverProcess = null;
      resolve();
    }, 5000);

    serverProcess.once('message', (msg) => {
      if (msg.type === 'stopped') {
        clearTimeout(timeout);
        serverProcess = null;
        resolve();
      }
    });

    serverProcess.once('exit', () => {
      clearTimeout(timeout);
      serverProcess = null;
      resolve();
    });

    try {
      serverProcess.send({ type: 'stop' });
    } catch (e) {
      clearTimeout(timeout);
      try { serverProcess.kill(); } catch (e2) {}
      serverProcess = null;
      resolve();
    }
  });
}

// ── Window creation ──────────────────────────────────────────────────

function createWindow() {
  mainWindow = new BrowserWindow({
    width: 1440, height: 920, minWidth: 1100, minHeight: 700,
    title: 'Polymarket Copy Trader v3',
    backgroundColor: '#0a0a0f',
    webPreferences: {
      nodeIntegration: false, contextIsolation: true,
      preload: path.join(__dirname, 'preload.js'),
      devTools: true
    },
    autoHideMenuBar: false, show: false
  });

  async function tryLoad(attempts) {
    try {
      await mainWindow.loadURL(`http://localhost:${PORT}`);
    } catch (e) {
      if (attempts > 0) {
        console.log('[App] Server not ready, retrying... (' + attempts + ' left)');
        await new Promise(r => setTimeout(r, 1000));
        if (!mainWindow || mainWindow.isDestroyed()) return;
        await tryLoad(attempts - 1);
      } else {
        if (mainWindow && !mainWindow.isDestroyed()) {
          mainWindow.loadURL('data:text/html,<h1 style="color:white;background:%230a0a0f;padding:40px;font-family:monospace">Server failed to start. Check the terminal for errors.</h1>');
        }
      }
    }
  }

  tryLoad(10);
  mainWindow.once('ready-to-show', () => mainWindow.show());
  // Forward renderer console to main process for debugging
  mainWindow.webContents.on('console-message', (event, level, message, line, sourceId) => {
    const prefix = ['[Renderer:V]','[Renderer:I]','[Renderer:W]','[Renderer:E]'][level] || '[Renderer]';
    console.log(`${prefix} ${message}`);
  });
  mainWindow.on('closed', () => { mainWindow = null; });
  mainWindow.webContents.setWindowOpenHandler(({ url }) => { shell.openExternal(url); return { action: 'deny' }; });

  mainWindow.webContents.on('before-input-event', (event, input) => {
    if (input.key === 'F12') { mainWindow.webContents.openDevTools(); event.preventDefault(); }
  });

  const menu = Menu.buildFromTemplate([
    { label: 'App', submenu: [{ role: 'quit' }] },
    { label: 'View', submenu: [
      { label: 'Developer Tools', accelerator: 'F12', click: () => mainWindow?.webContents?.toggleDevTools() },
      { role: 'reload' }, { role: 'forceReload' }
    ]}
  ]);
  Menu.setApplicationMenu(menu);
}

// ── Path sandboxing helper ──────────────────────────────────────────

function resolveSafe(p) {
  const full = path.resolve(__dirname, p);
  if (full !== __dirname && !full.startsWith(__dirname + path.sep)) {
    throw new Error('Access denied: path outside app directory');
  }
  return full;
}

// ── File system IPC ─────────────────────────────────────────────────

ipcMain.handle('fs:read', async (_, p) => {
  try {
    const full = resolveSafe(p);
    return { success: true, content: fs.readFileSync(full, 'utf8'), path: full };
  } catch (e) { return { success: false, error: e.message }; }
});

ipcMain.handle('fs:write', async (_, p, content) => {
  try {
    const full = resolveSafe(p);
    if (fs.existsSync(full)) fs.copyFileSync(full, full + '.backup');
    fs.writeFileSync(full, content, 'utf8');
    return { success: true, path: full };
  } catch (e) { return { success: false, error: e.message }; }
});

ipcMain.handle('fs:list', async (_, dir) => {
  try {
    const full = resolveSafe(dir || '.');
    const items = fs.readdirSync(full).map(name => {
      const stat = fs.statSync(path.join(full, name));
      return { name, isDir: stat.isDirectory(), size: stat.size };
    });
    return { success: true, items };
  } catch (e) { return { success: false, error: e.message }; }
});

// ── Server control ──────────────────────────────────────────────────

ipcMain.handle('server:restart', async () => {
  try {
    await stopServerProcess();
    await killZombieOnPort(PORT);
    await new Promise(r => setTimeout(r, 600));
    await startServerProcess();
    const win = mainWindow;
    if (win && !win.isDestroyed()) {
      await new Promise(r => setTimeout(r, 900));
      if (win && !win.isDestroyed()) {
        win.loadURL(`http://localhost:${PORT}`);
      }
    }
    return { success: true, message: 'Server restarted' };
  } catch (e) { return { success: false, error: e.message }; }
});

ipcMain.handle('server:logs', async () => ({ success: true, logs: [] }));

ipcMain.handle('server:reload-ui', async () => {
  const win = mainWindow;
  if (win && !win.isDestroyed()) { win.webContents.reload(); return { success: true }; }
  return { success: false };
});

// ── Auth token for renderer (no longer needed — auth removed) ────────

ipcMain.handle('auth:token', async () => {
  return { success: true, token: 'localhost' };
});

// ── Secure key storage ──────────────────────────────────────────────

ipcMain.handle('keys:save', async (_, keys) => {
  try {
    if (safeStorage.isEncryptionAvailable()) {
      fs.writeFileSync(path.join(app.getPath('userData'), 'keys.enc'), safeStorage.encryptString(JSON.stringify(keys)));
      return { success: true, encrypted: true };
    } else {
      fs.writeFileSync(path.join(app.getPath('userData'), 'keys.json'), JSON.stringify(keys));
      return { success: true, encrypted: false };
    }
  } catch (e) { return { success: false, error: e.message }; }
});

ipcMain.handle('keys:load', async () => {
  try {
    const ep = path.join(app.getPath('userData'), 'keys.enc');
    const jp = path.join(app.getPath('userData'), 'keys.json');
    if (fs.existsSync(ep) && safeStorage.isEncryptionAvailable()) {
      return { success: true, keys: JSON.parse(safeStorage.decryptString(fs.readFileSync(ep))), encrypted: true };
    } else if (fs.existsSync(jp)) {
      return { success: true, keys: JSON.parse(fs.readFileSync(jp, 'utf8')), encrypted: false };
    }
    return { success: true, keys: null };
  } catch (e) { return { success: false, error: e.message }; }
});

// ── Command execution (strict allowlist) ────────────────────────────

const ALLOWED_COMMANDS = ['npm install', 'npm audit fix', 'node --version', 'npm --version'];
const SHELL_METACHARACTERS = /[;&|`$(){}[\]<>!#]/;

ipcMain.handle('exec:run', async (_, command) => {
  return new Promise((resolve) => {
    if (!ALLOWED_COMMANDS.includes(command) || SHELL_METACHARACTERS.test(command)) {
      resolve({ success: false, error: 'Command not allowed: ' + command });
      return;
    }
    exec(command, { cwd: __dirname, timeout: 60000 }, (err, stdout, stderr) => {
      resolve({ success: !err, stdout: stdout?.trim(), stderr: stderr?.trim(), error: err?.message });
    });
  });
});

ipcMain.handle('app:info', async () => {
  let version = 'unknown';
  try { version = require('./package.json').version; } catch (e) {}
  return {
    success: true, appDir: __dirname, userData: app.getPath('userData'),
    version, platform: process.platform, nodeVersion: process.version
  };
});

// ── App lifecycle ───────────────────────────────────────────────────

app.whenReady().then(async () => {
  try {
    await killZombieOnPort(PORT);
    await startServerProcess();
  } catch (e) {
    console.error('[App] Failed to start server:', e.message);
    const { dialog } = require('electron');
    dialog.showErrorBox('Startup Error', `Server failed to start: ${e.message}`);
    app.quit();
    return;
  }
  await new Promise(r => setTimeout(r, 1500));
  createWindow();

  // Auto-restart on renderer crash
  if (mainWindow) {
    mainWindow.webContents.on('render-process-gone', async (event, details) => {
      console.error('[App] Renderer crashed:', details.reason);
      // Destroy the old window to avoid stale references
      if (mainWindow && !mainWindow.isDestroyed()) mainWindow.destroy();
      mainWindow = null;
      await new Promise(r => setTimeout(r, 2000));
      createWindow();
    });

    mainWindow.on('unresponsive', () => {
      console.warn('[App] Window unresponsive, reloading...');
      if (mainWindow && !mainWindow.isDestroyed()) {
        mainWindow.webContents.reload();
      }
    });
  }

  // Auto-restart server if it exits unexpectedly
  setInterval(async () => {
    if (!serverProcess) {
      console.error('[App] Server process gone — restarting...');
      try {
        await killZombieOnPort(PORT);
        await startServerProcess();
        console.log('[App] Server auto-restarted successfully');
      } catch (e) {
        console.error('[App] Auto-restart failed:', e.message);
      }
    }
  }, 30000);
});

app.on('window-all-closed', () => { if (process.platform !== 'darwin') app.quit(); });
app.on('activate', () => { if (mainWindow === null) createWindow(); });

let _quitting = false;
app.on('will-quit', async (event) => {
  if (_quitting) return;
  _quitting = true;
  event.preventDefault();
  try { await stopServerProcess(); } catch (e) { console.error('[App] Shutdown error:', e.message); }
  app.exit(0);
});
