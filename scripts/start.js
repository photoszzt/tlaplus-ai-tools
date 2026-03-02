#!/usr/bin/env node

/**
 * Bootstrap script for TLA+ MCP server.
 *
 * - Auto-installs dependencies if key runtime deps are not resolvable
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

// Format an npm install error with stderr/stdout details.
function formatInstallError(err) {
  let detail = String(err);
  if (err.stderr) {
    detail += '\nnpm stderr:\n' + String(err.stderr);
  }
  if (err.stdout) {
    detail += '\nnpm stdout:\n' + String(err.stdout);
  }
  return detail;
}

// Determine whether auto-install is allowed based on environment.
// Auto-install is on by default in Claude plugin contexts (CLAUDE_PLUGIN_ROOT set)
// and requires explicit opt-in (TLAPLUS_AUTO_INSTALL=1) outside of that.
// TLAPLUS_NO_AUTO_INSTALL=1 always disables auto-install regardless of context.
function isAutoInstallAllowed() {
  if (process.env.TLAPLUS_NO_AUTO_INSTALL === '1') return false;
  if (process.env.TLAPLUS_AUTO_INSTALL === '1') return true;
  // In plugin-cache contexts, auto-install by default
  if (process.env.CLAUDE_PLUGIN_ROOT) return true;
  return false;
}

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
    stdio: ['ignore', 'pipe', 'pipe'],
    cwd: rootDir,
  });
}

// Check whether key runtime dependencies are resolvable.
// In npm-installed or hoisted setups, node_modules may not exist locally
// but dependencies are still resolvable through the parent tree.
function runtimeDepsResolvable() {
  try {
    require.resolve('@modelcontextprotocol/sdk');
    require.resolve('fast-xml-parser');
    require.resolve('zod');
    return true;
  } catch (_) {
    return false;
  }
}

// Auto-install dependencies if key runtime deps are not resolvable
if (!runtimeDepsResolvable()) {
  if (!isAutoInstallAllowed()) {
    process.stderr.write(
      'Error: Required dependencies are not resolvable and auto-install is not enabled.\n' +
        'Run "npm ci" manually, or set TLAPLUS_AUTO_INSTALL=1 to allow automatic installation.\n'
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
    process.stderr.write(
      'Error: Failed to install dependencies.\n' + formatInstallError(err) + '\n'
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
    if (isAutoInstallAllowed()) {
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
        process.stderr.write(
          'Warning: Failed to ensure "tsx" is installed via dependency installation.\n' +
            formatInstallError(installErr) +
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
