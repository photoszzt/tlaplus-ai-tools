#!/usr/bin/env node

/**
 * Bootstrap script for TLA+ MCP server.
 *
 * - Auto-installs dependencies if node_modules is missing
 * - Runs from TypeScript source (via tsx) when available
 * - Falls back to pre-compiled dist/index.js when tsx is unavailable
 * - Cross-platform: uses Node.js instead of bash
 */

const { execFileSync } = require('child_process');
const path = require('path');
const fs = require('fs');

const isWin = process.platform === 'win32';
const npmCmd = isWin ? 'npm.cmd' : 'npm';

const rootDir = path.resolve(__dirname, '..');
process.chdir(rootDir);

// Install dependencies, suppressing stdout to avoid corrupting MCP stdio transport.
function npmInstall() {
  const hasLockfile = fs.existsSync(path.join(rootDir, 'package-lock.json'));
  const npmArgs = hasLockfile
    ? ['ci', '--no-audit', '--no-fund']
    : ['install', '--no-audit', '--no-fund'];
  if (process.env.NODE_ENV === 'production') {
    npmArgs.push('--omit=dev');
  }
  execFileSync(npmCmd, npmArgs, {
    stdio: ['ignore', 'ignore', 'inherit'],
    cwd: rootDir,
  });
}

// Auto-install dependencies if missing
if (!fs.existsSync(path.join(rootDir, 'node_modules'))) {
  if (process.env.TLAPLUS_NO_AUTO_INSTALL === '1') {
    process.stderr.write(
      'Error: node_modules is missing and auto-install is disabled (TLAPLUS_NO_AUTO_INSTALL=1).\nRun "npm ci" manually before starting the server.\n'
    );
    process.exit(1);
  }
  try {
    npmInstall();
  } catch (err) {
    if (err && err.code === 'ENOENT') {
      process.stderr.write(
        'Error: npm executable not found. Ensure that Node.js and npm are installed and available on your PATH.\n'
      );
      process.exit(1);
    }
    let detail = String(err);
    if (err.stderr) {
      detail += '\nnpm stderr:\n' + String(err.stderr);
    }
    if (err.stdout) {
      detail += '\nnpm stdout:\n' + String(err.stdout);
    }
    process.stderr.write(
      'Error: Failed to install dependencies.\n' + detail + '\n'
    );
    process.exit(typeof err.status === 'number' ? err.status : 1);
  }
}

const srcEntry = path.join(rootDir, 'src', 'index.ts');
const distEntry = path.join(rootDir, 'dist', 'index.js');

// Check if tsx is available for running TypeScript source directly
let hasTsx = false;
if (fs.existsSync(srcEntry)) {
  try {
    require.resolve('tsx/cjs');
    hasTsx = true;
  } catch (_) {
    // tsx not resolvable — attempt to (re)install dependencies, then retry
    if (process.env.TLAPLUS_NO_AUTO_INSTALL !== '1') {
      try {
        npmInstall();
        require.resolve('tsx/cjs');
        hasTsx = true;
      } catch (installErr) {
        if (installErr && installErr.code === 'ENOENT') {
          process.stderr.write(
            'Error: npm executable not found. Ensure that Node.js and npm are installed and available on your PATH.\n'
          );
          process.exit(1);
        }
        // If npm install or the second resolve fails, fall back to dist/ if available
        let detail = String(installErr);
        if (installErr.stderr) {
          detail += '\nnpm stderr:\n' + String(installErr.stderr);
        }
        if (installErr.stdout) {
          detail += '\nnpm stdout:\n' + String(installErr.stdout);
        }
        process.stderr.write(
          'Warning: Failed to ensure "tsx" is installed via dependency installation.\n' +
            detail +
            '\n'
        );
      }
    }
  }
}

if (fs.existsSync(srcEntry) && hasTsx) {
  // Prefer running from TypeScript source (no build step needed).
  // Register tsx loader and run in-process so stdin/stdout stay
  // owned by this process, which is required for MCP stdio transport.
  try {
    require('tsx/cjs');
    require(srcEntry);
  } catch (err) {
    process.stderr.write(
      'Error: Failed to start server from src/index.ts.\n' + String(err) + '\n'
    );
    process.exit(1);
  }
} else if (fs.existsSync(distEntry)) {
  // Use pre-compiled dist/index.js (packaged installs or tsx unavailable)
  try {
    require(distEntry);
  } catch (err) {
    process.stderr.write(
      'Error: Failed to start server from dist/index.js.\n' + String(err) + '\n'
    );
    process.exit(1);
  }
} else if (fs.existsSync(srcEntry)) {
  // src/ exists but tsx is not available and no dist/ fallback
  process.stderr.write(
    'Error: The "tsx" runtime is not available, but src/index.ts exists.\n' +
      'Run "npm install" (and ensure "tsx" is listed as a dependency) before starting the server.\n'
  );
  process.exit(1);
} else {
  process.stderr.write(
    'Error: Neither src/index.ts nor dist/index.js found.\n' +
      'Run "npm run build" or ensure src/ is available.\n'
  );
  process.exit(1);
}
