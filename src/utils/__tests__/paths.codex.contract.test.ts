// Spec: docs/codex-fixes/spec.md
// Contract: docs/codex-fixes/contract.md (resolveAndValidatePath)
// Testing: docs/codex-fixes/testing.md
//
// Contract tests for resolveAndValidatePath public API.
// These tests verify behavior documented in the contract without peeking at implementation.

import * as path from 'path';
import * as fs from 'fs';
import * as os from 'os';

describe('resolveAndValidatePath - Contract Tests', () => {
  let tempDir: string;

  beforeEach(() => {
    tempDir = fs.mkdtempSync(path.join(os.tmpdir(), 'codex-contract-'));
  });

  afterEach(() => {
    fs.rmSync(tempDir, { recursive: true, force: true });
  });

  function getResolveAndValidatePath(): (filePath: string, workingDir: string | null) => string {
    const modulePath = require.resolve('../paths');
    delete require.cache[modulePath];
    const fsModulePath = require.resolve('fs');
    delete require.cache[fsModulePath];
    return require('../paths').resolveAndValidatePath;
  }

  // @tests-contract REQ-CODEX-003
  it('path escaping via symlink outside workingDir is blocked', () => {
    const resolveAndValidatePath = getResolveAndValidatePath();

    // On macOS, tmpdir may be a symlink (/var -> /private/var)
    const realTempDir = fs.realpathSync(tempDir);

    const workspace = path.join(realTempDir, 'ws');
    const outside = path.join(realTempDir, 'outside');
    fs.mkdirSync(workspace);
    fs.mkdirSync(outside);
    fs.writeFileSync(path.join(outside, 'secret'), 'data');
    fs.symlinkSync(path.join(outside, 'secret'), path.join(workspace, 'escape'));

    expect(() => resolveAndValidatePath('escape', workspace)).toThrow();
  });

  // @tests-contract REQ-CODEX-004
  it('null workingDir accepts any path without throwing', () => {
    const resolveAndValidatePath = getResolveAndValidatePath();

    // Contract: when workingDir is null, no containment check
    const result = resolveAndValidatePath('/any/absolute/path', null);
    expect(typeof result).toBe('string');
    expect(path.isAbsolute(result)).toBe(true);
  });

  // @tests-contract REQ-CODEX-003
  // INV-CODEX-004: function takes (string, string|null) -> string
  it('function signature: (string, string|null) -> string', () => {
    const resolveAndValidatePath = getResolveAndValidatePath();

    // Verify it returns a string for both parameter variants
    const r1 = resolveAndValidatePath('/test', null);
    expect(typeof r1).toBe('string');

    const realTempDir2 = fs.realpathSync(tempDir);
    const workspace = path.join(realTempDir2, 'ws2');
    fs.mkdirSync(workspace);
    fs.writeFileSync(path.join(workspace, 'f.txt'), '');
    const r2 = resolveAndValidatePath('f.txt', workspace);
    expect(typeof r2).toBe('string');
  });
});
