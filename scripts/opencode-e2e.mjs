#!/usr/bin/env node

/**
 * OpenCode E2E Test Runner
 * 
 * Local-only E2E tests for OpenCode command integration.
 * Requires OpenCode CLI in PATH and configured model provider.
 * 
 * Usage:
 *   OPENCODE_E2E=1 npm run opencode:e2e
 * 
 * Deterministic enable/skip rule:
 *   - If OPENCODE_E2E !== '1', prints SKIP and exits 0
 *   - If OPENCODE_E2E === '1', runs suite and exits non-zero on failure
 */

import { spawn } from 'child_process';
import { fileURLToPath } from 'url';
import { dirname, join } from 'path';

const __filename = fileURLToPath(import.meta.url);
const __dirname = dirname(__filename);
const projectRoot = join(__dirname, '..');

// ANSI color codes
const colors = {
  reset: '\x1b[0m',
  red: '\x1b[31m',
  green: '\x1b[32m',
  yellow: '\x1b[33m',
  blue: '\x1b[34m',
  cyan: '\x1b[36m',
  gray: '\x1b[90m',
};

function log(message, color = 'reset') {
  console.log(`${colors[color]}${message}${colors.reset}`);
}

function logSection(title) {
  console.log();
  log(`${'='.repeat(60)}`, 'cyan');
  log(title, 'cyan');
  log(`${'='.repeat(60)}`, 'cyan');
}

// Deterministic enable/skip rule
if (process.env.OPENCODE_E2E !== '1') {
  log('SKIP: OPENCODE_E2E not set to 1', 'yellow');
  log('To run E2E tests: OPENCODE_E2E=1 npm run opencode:e2e', 'gray');
  process.exit(0);
}

logSection('OpenCode E2E Test Suite');
log('Running local E2E tests for OpenCode commands...', 'blue');

// Preflight checks
async function runCommand(command, args, options = {}) {
  return new Promise((resolve, reject) => {
    const proc = spawn(command, args, {
      cwd: options.cwd || projectRoot,
      stdio: options.stdio || 'pipe',
      shell: process.platform === 'win32',
    });

    let stdout = '';
    let stderr = '';

    if (proc.stdout) {
      proc.stdout.on('data', (data) => {
        stdout += data.toString();
      });
    }

    if (proc.stderr) {
      proc.stderr.on('data', (data) => {
        stderr += data.toString();
      });
    }

    proc.on('close', (code) => {
      resolve({ code, stdout, stderr });
    });

    proc.on('error', (err) => {
      reject(err);
    });
  });
}

async function preflight() {
  logSection('Preflight Checks');

  // Check opencode --version
  log('Checking OpenCode CLI...', 'blue');
  try {
    const { code, stdout, stderr } = await runCommand('opencode', ['--version']);
    if (code !== 0) {
      log(`✗ opencode --version failed (exit ${code})`, 'red');
      log(`stderr: ${stderr}`, 'gray');
      return false;
    }
    log(`✓ OpenCode version: ${stdout.trim()}`, 'green');
  } catch (err) {
    log(`✗ OpenCode CLI not found: ${err.message}`, 'red');
    log('Install OpenCode: npm install -g @opencode/cli', 'yellow');
    return false;
  }

  // Check opencode run --help contains --command
  log('Checking OpenCode run command...', 'blue');
  try {
    const { code, stdout } = await runCommand('opencode', ['run', '--help']);
    if (code !== 0) {
      log(`✗ opencode run --help failed (exit ${code})`, 'red');
      return false;
    }
    if (!stdout.includes('--command')) {
      log('✗ opencode run --help does not contain --command flag', 'red');
      log('OpenCode version may be outdated', 'yellow');
      return false;
    }
    log('✓ OpenCode run --command available', 'green');
  } catch (err) {
    log(`✗ Failed to check opencode run: ${err.message}`, 'red');
    return false;
  }

  return true;
}

// E2E test suite
const testSuite = [
  {
    name: 'tla-parse',
    command: 'opencode',
    args: ['run', '--command', 'tla-parse', 'test-specs/Counter.tla'],
    markers: ['Spec path:'],
  },
  {
    name: 'tla-symbols',
    command: 'opencode',
    args: ['run', '--command', 'tla-symbols', 'test-specs/Counter.tla'],
    markers: ['Spec path:', 'CFG written:'],
  },
  {
    name: 'tla-smoke',
    command: 'opencode',
    args: ['run', '--command', 'tla-smoke', 'test-specs/Counter.tla'],
    markers: ['Spec path:', 'CFG used:'],
  },
  {
    name: 'tla-check',
    command: 'opencode',
    args: ['run', '--command', 'tla-check', 'test-specs/Counter.tla', 'test-specs/Counter.cfg'],
    markers: ['Spec path:', 'CFG used:'],
  },
  {
    name: 'tla-review',
    command: 'opencode',
    args: ['run', '--command', 'tla-review', 'test-specs/Counter.tla'],
    markers: ['Spec path:', 'Review Summary'],
  },
  {
    name: 'tla-setup',
    command: 'opencode',
    args: ['run', '--command', 'tla-setup'],
    markers: ['Spec path:'], // tla-setup may have different markers
  },
];

async function runTest(test) {
  log(`\nRunning: ${test.name}`, 'blue');
  log(`Command: ${test.command} ${test.args.join(' ')}`, 'gray');

  try {
    const { code, stdout, stderr } = await runCommand(test.command, test.args);

    // Check exit code
    if (code !== 0) {
      log(`✗ Command failed with exit code ${code}`, 'red');
      log(`stdout:\n${stdout}`, 'gray');
      log(`stderr:\n${stderr}`, 'gray');
      
      // Check for missing configuration
      if (stdout.includes('model') || stdout.includes('provider') || stderr.includes('authentication')) {
        log('\nDiagnostic: Missing OpenCode model/provider configuration', 'yellow');
        log('Configure OpenCode with: opencode config set', 'yellow');
      }
      
      return false;
    }

    // Check markers
    const missingMarkers = test.markers.filter(marker => !stdout.includes(marker));
    if (missingMarkers.length > 0) {
      log(`✗ Missing expected markers: ${missingMarkers.join(', ')}`, 'red');
      log(`stdout:\n${stdout}`, 'gray');
      return false;
    }

    log(`✓ Test passed (found markers: ${test.markers.join(', ')})`, 'green');
    return true;
  } catch (err) {
    log(`✗ Command execution failed: ${err.message}`, 'red');
    return false;
  }
}

async function runSuite() {
  logSection('Running E2E Test Suite');

  let passed = 0;
  let failed = 0;

  for (const test of testSuite) {
    const result = await runTest(test);
    if (result) {
      passed++;
    } else {
      failed++;
    }
  }

  logSection('Test Results');
  log(`Total: ${testSuite.length}`, 'blue');
  log(`Passed: ${passed}`, 'green');
  log(`Failed: ${failed}`, failed > 0 ? 'red' : 'green');

  return failed === 0;
}

// Main execution
async function main() {
  try {
    // Run preflight checks
    const preflightPassed = await preflight();
    if (!preflightPassed) {
      log('\n✗ Preflight checks failed', 'red');
      process.exit(1);
    }

    // Run test suite
    const suitePassed = await runSuite();
    if (!suitePassed) {
      log('\n✗ E2E test suite failed', 'red');
      process.exit(1);
    }

    log('\n✓ All E2E tests passed!', 'green');
    process.exit(0);
  } catch (err) {
    log(`\n✗ Unexpected error: ${err.message}`, 'red');
    console.error(err);
    process.exit(1);
  }
}

main();
