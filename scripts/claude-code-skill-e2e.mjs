#!/usr/bin/env node

/**
 * Claude Code Skill E2E Test Runner
 *
 * Tests skills (not commands) in Claude Code --print mode.
 * Commands are not accessible in --print mode - see docs/e2e-testing-findings.md
 *
 * Usage:
 *   CLAUDE_CODE_E2E=1 npm run claude-code:skill-e2e
 *
 * Deterministic enable/skip rule:
 *   - If CLAUDE_CODE_E2E !== '1', prints SKIP and exits 0
 *   - If CLAUDE_CODE_E2E === '1', runs suite and exits non-zero on failure
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
if (process.env.CLAUDE_CODE_E2E !== '1') {
  log('SKIP: CLAUDE_CODE_E2E not set to 1', 'yellow');
  log('To run E2E tests: CLAUDE_CODE_E2E=1 npm run claude-code:skill-e2e', 'gray');
  process.exit(0);
}

logSection('Claude Code Skill E2E Test Suite');
log('Testing skills in --print mode...', 'blue');
log('Note: Commands cannot be tested in --print mode', 'yellow');

// Preflight checks
async function runCommand(command, args, options = {}) {
  return new Promise((resolve, reject) => {
    const proc = spawn(command, args, {
      cwd: options.cwd || projectRoot,
      stdio: options.stdio || 'pipe',
      shell: process.platform === 'win32',
      env: {
        ...process.env,
      },
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

    // Handle timeout
    if (options.timeout) {
      const timeoutId = setTimeout(() => {
        proc.kill('SIGTERM');
        reject(new Error(`Command timed out after ${options.timeout}ms`));
      }, options.timeout);

      proc.on('close', () => {
        clearTimeout(timeoutId);
      });
    }
  });
}

async function runCommandWithStdin(input, options = {}) {
  return new Promise((resolve, reject) => {
    const proc = spawn('claude', ['--print', '--plugin-dir', projectRoot], {
      cwd: options.cwd || projectRoot,
      stdio: 'pipe',
      shell: process.platform === 'win32',
      env: {
        ...process.env,
      },
    });

    let stdout = '';
    let stderr = '';

    proc.stdout.on('data', (data) => {
      stdout += data.toString();
    });

    proc.stderr.on('data', (data) => {
      stderr += data.toString();
    });

    proc.on('close', (code) => {
      resolve({ code, stdout, stderr });
    });

    proc.on('error', (err) => {
      reject(err);
    });

    // Write input and close stdin
    proc.stdin.write(input);
    proc.stdin.end();

    // Handle timeout
    const timeout = options.timeout || 60000;
    const timeoutId = setTimeout(() => {
      proc.kill('SIGTERM');
      reject(new Error(`Command timed out after ${timeout}ms`));
    }, timeout);

    proc.on('close', () => {
      clearTimeout(timeoutId);
    });
  });
}

async function preflight() {
  logSection('Preflight Checks');

  // Check claude --help
  log('Checking Claude Code CLI...', 'blue');
  try {
    const { code, stdout, stderr } = await runCommand('claude', ['--help']);
    if (code !== 0) {
      log(`✗ claude --help failed (exit ${code})`, 'red');
      log(`stderr: ${stderr}`, 'gray');
      return false;
    }
    log('✓ Claude Code CLI found', 'green');
  } catch (err) {
    log(`✗ Claude Code CLI not found: ${err.message}`, 'red');
    log('Install Claude Code: https://docs.anthropic.com/claude/docs/claude-code', 'yellow');
    return false;
  }

  // Check --print flag support
  log('Checking Claude Code --print flag...', 'blue');
  try {
    const { stdout: helpOutput } = await runCommand('claude', ['--help']);
    if (!helpOutput.includes('--print') && !helpOutput.includes('-p')) {
      log('✗ claude --print flag not found', 'red');
      log('Claude Code version may be outdated', 'yellow');
      return false;
    }
    log('✓ Claude Code --print flag available', 'green');
  } catch (err) {
    log(`✗ Failed to check claude --print: ${err.message}`, 'red');
    return false;
  }

  return true;
}

// Skill E2E test suite
const skillSuite = [
  {
    name: 'tla-getting-started',
    input: '/tla-getting-started',
    markers: ['TLA+', 'spec'],
  },
  {
    name: 'tla-model-checking',
    input: '/tla-model-checking',
    markers: ['TLC', 'model check'],
  },
  {
    name: 'tla-spec-review',
    input: '/tla-spec-review',
    markers: ['review', 'specification'],
  },
  {
    name: 'tla-debug-violations',
    input: '/tla-debug-violations',
    markers: ['debug', 'violation'],
  },
  {
    name: 'tla-create-animations',
    input: '/tla-create-animations',
    markers: ['animation', 'visualiz'],
  },
  {
    name: 'tla-refinement-proofs',
    input: '/tla-refinement-proofs',
    markers: ['refinement', 'proof'],
  },
];

async function runTest(test) {
  log(`\nRunning: ${test.name}`, 'blue');
  log(`Input: ${test.input}`, 'gray');

  try {
    const { code, stdout, stderr } = await runCommandWithStdin(test.input, {
      timeout: 60000,
    });

    // Check exit code
    if (code !== 0) {
      log(`✗ Command failed with exit code ${code}`, 'red');
      log(`stdout:\n${stdout.substring(0, 500)}`, 'gray');
      log(`stderr:\n${stderr.substring(0, 500)}`, 'gray');

      // Check for missing configuration
      if (
        stdout.includes('API key') ||
        stderr.includes('authentication') ||
        stderr.includes('ANTHROPIC_API_KEY')
      ) {
        log('\nDiagnostic: Missing Claude API key', 'yellow');
        log('Set ANTHROPIC_API_KEY environment variable', 'yellow');
      }

      return false;
    }

    // Check markers (case-insensitive)
    const lowerStdout = stdout.toLowerCase();
    const missingMarkers = test.markers.filter(
      (marker) => !lowerStdout.includes(marker.toLowerCase())
    );

    if (missingMarkers.length > 0) {
      log(`✗ Missing expected markers: ${missingMarkers.join(', ')}`, 'red');
      log(`stdout preview:\n${stdout.substring(0, 500)}...`, 'gray');
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
  logSection('Running Skill E2E Test Suite');

  let passed = 0;
  let failed = 0;

  for (const test of skillSuite) {
    const result = await runTest(test);
    if (result) {
      passed++;
    } else {
      failed++;
    }
  }

  logSection('Test Results');
  log(`Total: ${skillSuite.length}`, 'blue');
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

    log('\n✓ All skill E2E tests passed!', 'green');
    log('\nNote: Commands cannot be tested in --print mode', 'yellow');
    log('Use OpenCode E2E or manual testing for command validation', 'yellow');
    process.exit(0);
  } catch (err) {
    log(`\n✗ Unexpected error: ${err.message}`, 'red');
    console.error(err);
    process.exit(1);
  }
}

main();
