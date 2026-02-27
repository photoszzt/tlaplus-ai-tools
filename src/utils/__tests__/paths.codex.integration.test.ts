// Spec: docs/codex-fixes/spec.md
// Testing: docs/codex-fixes/testing.md
//
// Integration tests for Finding 2: real-filesystem symlink scenarios
// These tests use actual symlinks in os.tmpdir() to verify realpathSync integration.

import * as fs from 'fs';
import * as path from 'path';
import * as os from 'os';

// Import the REAL resolveAndValidatePath (no mocks)
// We need to use a dynamic require to avoid Jest module cache issues
// since other test files mock 'fs'. We run these as a separate test file.

describe('resolveAndValidatePath - Integration Tests (Real Filesystem)', () => {
  let tempDir: string;

  beforeEach(() => {
    tempDir = fs.mkdtempSync(path.join(os.tmpdir(), 'codex-test-'));
  });

  afterEach(() => {
    fs.rmSync(tempDir, { recursive: true, force: true });
  });

  // We need the unmocked function. Since jest.mock is hoisted and affects the whole file,
  // we'll use a fresh require for the actual module.
  function getResolveAndValidatePath(): (filePath: string, workingDir: string | null) => string {
    // Clear the module from require cache so we get the real one
    const modulePath = require.resolve('../paths');
    delete require.cache[modulePath];
    // Also clear the fs module cache to get the real fs
    const fsModulePath = require.resolve('fs');
    delete require.cache[fsModulePath];
    const mod = require('../paths');
    return mod.resolveAndValidatePath;
  }

  // @tests REQ-CODEX-003, SCN-CODEX-003-01
  it('real symlink pointing outside workingDir is blocked', () => {
    const resolveAndValidatePath = getResolveAndValidatePath();

    // On macOS, os.tmpdir() returns /var/... which is a symlink to /private/var/...
    // Use realpathSync to get the canonical temp dir to avoid prefix mismatch.
    const realTempDir = fs.realpathSync(tempDir);

    // Create workspace and outside directories
    const workspace = path.join(realTempDir, 'workspace');
    const outside = path.join(realTempDir, 'outside');
    fs.mkdirSync(workspace);
    fs.mkdirSync(outside);

    // Create a file outside workspace
    const outsideFile = path.join(outside, 'secret.txt');
    fs.writeFileSync(outsideFile, 'secret content');

    // Create a symlink inside workspace pointing outside
    const symlinkPath = path.join(workspace, 'link.txt');
    fs.symlinkSync(outsideFile, symlinkPath);

    // Verify the symlink exists and points where we think
    expect(fs.lstatSync(symlinkPath).isSymbolicLink()).toBe(true);

    // resolveAndValidatePath should block this
    expect(() => resolveAndValidatePath('link.txt', workspace))
      .toThrow('Access denied');
  });

  // @tests REQ-CODEX-003, SCN-CODEX-003-04
  it('workingDir itself is a symlink - containment check uses realpath', () => {
    const resolveAndValidatePath = getResolveAndValidatePath();
    const realTempDir = fs.realpathSync(tempDir);

    // Create real workspace
    const realWorkspace = path.join(realTempDir, 'real-workspace');
    fs.mkdirSync(realWorkspace);

    // Create a file inside the real workspace
    const realFile = path.join(realWorkspace, 'spec.tla');
    fs.writeFileSync(realFile, 'spec content');

    // Create a symlink to the workspace
    const workspaceLink = path.join(realTempDir, 'workspace-link');
    fs.symlinkSync(realWorkspace, workspaceLink);

    // Verify the symlink works
    expect(fs.lstatSync(workspaceLink).isSymbolicLink()).toBe(true);

    // File inside linked workspace should be allowed
    const result = resolveAndValidatePath('spec.tla', workspaceLink);
    expect(result).toBe(path.resolve(workspaceLink, 'spec.tla'));
  });

  // @tests REQ-CODEX-003
  it('real symlink inside workingDir pointing inside succeeds', () => {
    const resolveAndValidatePath = getResolveAndValidatePath();
    const realTempDir = fs.realpathSync(tempDir);

    // Create workspace with nested directories
    const workspace = path.join(realTempDir, 'workspace');
    const subdir = path.join(workspace, 'subdir');
    fs.mkdirSync(workspace);
    fs.mkdirSync(subdir);

    // Create a file in subdir
    const realFile = path.join(subdir, 'spec.tla');
    fs.writeFileSync(realFile, 'spec content');

    // Create symlink in workspace root pointing to file in subdir (still inside workspace)
    const symlinkPath = path.join(workspace, 'link.tla');
    fs.symlinkSync(realFile, symlinkPath);

    // Should succeed - symlink target is still inside workspace
    const result = resolveAndValidatePath('link.tla', workspace);
    expect(result).toBe(path.resolve(workspace, 'link.tla'));
  });
});
