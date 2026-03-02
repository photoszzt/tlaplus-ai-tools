#!/usr/bin/env node

/**
 * Bootstrap script for TLA+ MCP server.
 *
 * - Auto-installs dependencies if node_modules is missing
 * - Runs from TypeScript source (via tsx) when available
 * - Falls back to pre-compiled dist/index.js for packaged installs
 * - Cross-platform: uses Node.js instead of bash
 */

const { execFileSync } = require('child_process');
const path = require('path');
const fs = require('fs');

const rootDir = path.resolve(__dirname, '..');
process.chdir(rootDir);

// Auto-install dependencies if missing
if (!fs.existsSync(path.join(rootDir, 'node_modules'))) {
  execFileSync('npm', ['install'], { stdio: 'inherit', cwd: rootDir });
}

const srcEntry = path.join(rootDir, 'src', 'index.ts');
const distEntry = path.join(rootDir, 'dist', 'index.js');

if (fs.existsSync(srcEntry)) {
  // Register tsx loader and run from TypeScript source in-process.
  // This keeps stdin/stdout owned by this process, which is required
  // for MCP stdio transport.
  require('tsx/cjs');
  require(srcEntry);
} else if (fs.existsSync(distEntry)) {
  // Fallback to pre-compiled JavaScript for packaged installs
  require(distEntry);
} else {
  process.stderr.write(
    'Error: Neither src/index.ts nor dist/index.js found.\n' +
      'Run "npm run build" or ensure src/ is available.\n'
  );
  process.exit(1);
}
