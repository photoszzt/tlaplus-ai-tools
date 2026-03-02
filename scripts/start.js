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

// Run npm install, directing stdout to stderr to avoid corrupting MCP stdio transport.
function npmInstall() {
  const npmArgs = ['install'];
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
      'Error: Failed to run "npm install".\n' + String(err) + '\n'
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
        'Warning: Failed to ensure "tsx" is installed via "npm install".\n' +
          String(installErr) +
          '\n'
      );
    }
  }
}

if (fs.existsSync(srcEntry) && hasTsx) {
  // Prefer running from TypeScript source (no build step needed).
  // Register tsx loader and run in-process so stdin/stdout stay
  // owned by this process, which is required for MCP stdio transport.
  require('tsx/cjs');
  require(srcEntry);
} else if (fs.existsSync(distEntry)) {
  // Use pre-compiled dist/index.js (packaged installs or tsx unavailable)
  require(distEntry);
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
