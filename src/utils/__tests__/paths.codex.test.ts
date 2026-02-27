// Spec: docs/codex-fixes/spec.md
// Testing: docs/codex-fixes/testing.md
//
// White-box tests for Finding 2: symlink-aware resolveAndValidatePath

import * as path from 'path';

const mockRealpathSync = jest.fn();

jest.mock('fs', () => ({
  realpathSync: (...args: unknown[]) => mockRealpathSync(...args),
  promises: {
    stat: jest.fn(),
    access: jest.fn(),
    readdir: jest.fn(),
  },
}));

jest.mock('child_process', () => ({
  execSync: jest.fn(),
}));

import { resolveAndValidatePath } from '../paths';

describe('resolveAndValidatePath - Codex Symlink Fixes', () => {
  beforeEach(() => {
    mockRealpathSync.mockReset();
    // Default: realpathSync returns its input (no symlinks)
    mockRealpathSync.mockImplementation((p: string) => p);
  });

  // @tests REQ-CODEX-003, SCN-CODEX-003-01
  it('symlink inside workingDir pointing outside throws Access denied', () => {
    // Simulate: /workspace/link.tla is a symlink to /etc/passwd
    mockRealpathSync.mockImplementation((p: string) => {
      if (p === '/workspace/link.tla') return '/etc/passwd';
      if (p === '/workspace') return '/workspace';
      return p;
    });

    expect(() => resolveAndValidatePath('link.tla', '/workspace'))
      .toThrow('Access denied');

    expect(() => resolveAndValidatePath('link.tla', '/workspace'))
      .toThrow(/resolves to \/etc\/passwd/);
  });

  // @tests REQ-CODEX-003, SCN-CODEX-003-02
  it('non-existent path falls back to lexical check (inside workingDir)', () => {
    // Simulate: /workspace/nonexistent.tla does not exist -> ENOENT
    mockRealpathSync.mockImplementation((p: string) => {
      const err = new Error('ENOENT') as NodeJS.ErrnoException;
      err.code = 'ENOENT';
      throw err;
    });

    const result = resolveAndValidatePath('nonexistent.tla', '/workspace');
    expect(result).toBe(path.resolve('/workspace', 'nonexistent.tla'));
  });

  // @tests REQ-CODEX-003, SCN-CODEX-003-03
  it('non-existent path outside workingDir still rejected via lexical check', () => {
    mockRealpathSync.mockImplementation(() => {
      const err = new Error('ENOENT') as NodeJS.ErrnoException;
      err.code = 'ENOENT';
      throw err;
    });

    expect(() => resolveAndValidatePath('../outside.tla', '/workspace'))
      .toThrow('Access denied');
  });

  // @tests REQ-CODEX-003, SCN-CODEX-003-04
  it('workingDir is a symlink - containment works on real paths', () => {
    // /tmp/workspace-link -> /real/workspace
    // /tmp/workspace-link/spec.tla resolves to /real/workspace/spec.tla
    mockRealpathSync.mockImplementation((p: string) => {
      if (p === '/tmp/workspace-link/spec.tla') return '/real/workspace/spec.tla';
      if (p === '/tmp/workspace-link') return '/real/workspace';
      return p;
    });

    const result = resolveAndValidatePath('spec.tla', '/tmp/workspace-link');
    // Return value is the lexically resolved path, NOT the realpath
    expect(result).toBe(path.resolve('/tmp/workspace-link', 'spec.tla'));
  });

  // @tests REQ-CODEX-004, SCN-CODEX-004-01
  it('null workingDir skips all validation including realpathSync', () => {
    const result = resolveAndValidatePath('../somewhere/file.tla', null);

    // No realpathSync should be called when workingDir is null
    expect(mockRealpathSync).not.toHaveBeenCalled();
    expect(result).toBe(path.resolve(process.cwd(), '../somewhere/file.tla'));
  });

  // @tests REQ-CODEX-003
  // TC-EDGE-001: realpathSync throws non-ENOENT error -> re-thrown
  it('realpathSync EACCES error is re-thrown (not swallowed)', () => {
    mockRealpathSync.mockImplementation(() => {
      const err = new Error('EACCES: permission denied') as NodeJS.ErrnoException;
      err.code = 'EACCES';
      throw err;
    });

    expect(() => resolveAndValidatePath('file.tla', '/workspace'))
      .toThrow('EACCES');
  });

  // @tests REQ-CODEX-003
  it('return value is lexical absolute path, not realpath', () => {
    // Even when realpathSync resolves to a different path,
    // the return value should be the lexical path.resolve() result
    mockRealpathSync.mockImplementation((p: string) => {
      if (p === '/workspace/link.tla') return '/workspace/real/target.tla';
      if (p === '/workspace') return '/workspace';
      return p;
    });

    const result = resolveAndValidatePath('link.tla', '/workspace');
    expect(result).toBe(path.resolve('/workspace', 'link.tla'));
    expect(result).not.toBe('/workspace/real/target.tla');
  });

  // @tests REQ-CODEX-003
  // TC-SEC-001: path traversal with workingDir
  it('path traversal ../../../etc/passwd blocked', () => {
    expect(() => resolveAndValidatePath('../../../etc/passwd', '/workspace'))
      .toThrow('Access denied');
  });

  // @tests REQ-CODEX-003
  // TC-SEC-002: symlink escape via realpathSync
  it('symlink to /etc/passwd inside workingDir is blocked', () => {
    mockRealpathSync.mockImplementation((p: string) => {
      if (p === '/workspace/malicious') return '/etc/passwd';
      if (p === '/workspace') return '/workspace';
      return p;
    });

    expect(() => resolveAndValidatePath('malicious', '/workspace'))
      .toThrow('Access denied');
  });

  // @tests-invariant INV-CODEX-004
  it('function signature: takes (string, string|null) returns string', () => {
    // Verify the function accepts the documented parameter types
    const result1 = resolveAndValidatePath('/absolute/path', null);
    expect(typeof result1).toBe('string');

    const result2 = resolveAndValidatePath('relative', '/workspace');
    expect(typeof result2).toBe('string');
  });
});
