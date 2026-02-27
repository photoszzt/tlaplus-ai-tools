// Spec: docs/codex-fixes/spec.md
// Testing: docs/codex-fixes/testing.md
//
// White-box tests for Finding 4: Commands installer content comparison + stale removal

import * as fs from 'fs';
import * as path from 'path';
import * as paths from '../paths';
import { installCommands } from '../commands-installer';

jest.mock('fs');
jest.mock('../paths');

const mockFs = fs as jest.Mocked<typeof fs>;
const mockPaths = paths as jest.Mocked<typeof paths>;

function normalizePath(p: string): string {
  return p.split(path.sep).join('/');
}

describe('Commands Installer - Codex Content Comparison Fixes', () => {
  const projectRoot = '/project';
  const sourceDir = '/project/commands';
  const targetDir = '/project/.opencode/commands';

  beforeEach(() => {
    jest.clearAllMocks();
    mockPaths.getCanonicalDir.mockReturnValue(targetDir);
  });

  // --- REQ-CODEX-009: Content comparison in isAlreadyInstalled ---

  // @tests REQ-CODEX-009, SCN-CODEX-009-01
  it('stale file content (different from source) triggers reinstall', () => {
    const sourcePath = path.join(sourceDir, 'tla-parse.md');
    const targetPath = path.join(targetDir, 'tla-parse.md');

    let rmSyncCalled = false;
    mockFs.existsSync.mockImplementation((p) => {
      const normalized = normalizePath(p.toString());
      if (normalized === normalizePath(sourceDir)) return true;
      if (normalized === normalizePath(sourcePath)) return true;
      if (normalized === normalizePath(targetPath)) return !rmSyncCalled;
      return false;
    });

    mockFs.readdirSync.mockReturnValue([
      { name: 'tla-parse.md', isFile: () => true, isDirectory: () => false } as any,
    ]);

    // Target is a regular file (not symlink) with DIFFERENT content
    mockFs.lstatSync.mockReturnValue({
      isSymbolicLink: () => false,
      isFile: () => true,
      isDirectory: () => false,
    } as any);

    mockFs.readFileSync.mockImplementation((p: fs.PathOrFileDescriptor) => {
      const normalized = normalizePath(p.toString());
      if (normalized === normalizePath(targetPath)) return 'old version content';
      if (normalized === normalizePath(sourcePath)) return 'new version content';
      return '';
    });

    mockFs.rmSync.mockImplementation(() => { rmSyncCalled = true; });
    mockFs.symlinkSync.mockImplementation(() => {});

    const result = installCommands(projectRoot);

    expect(result.success).toBe(true);
    expect(result.installedCount).toBe(1);
    expect(result.alreadyInstalledCount).toBe(0);
    expect(result.commands[0].installed).toBe(true);
    expect(mockFs.rmSync).toHaveBeenCalledWith(targetPath, { force: true });
  });

  // @tests REQ-CODEX-009, SCN-CODEX-009-02
  it('matching file content returns already installed (no reinstall)', () => {
    const sourcePath = path.join(sourceDir, 'tla-parse.md');
    const targetPath = path.join(targetDir, 'tla-parse.md');

    mockFs.existsSync.mockImplementation((p) => {
      const normalized = normalizePath(p.toString());
      if (normalized === normalizePath(sourceDir)) return true;
      if (normalized === normalizePath(sourcePath)) return true;
      if (normalized === normalizePath(targetPath)) return true;
      return false;
    });

    mockFs.readdirSync.mockReturnValue([
      { name: 'tla-parse.md', isFile: () => true, isDirectory: () => false } as any,
    ]);

    mockFs.lstatSync.mockReturnValue({
      isSymbolicLink: () => false,
      isFile: () => true,
      isDirectory: () => false,
    } as any);

    // Both files have the SAME content
    mockFs.readFileSync.mockReturnValue('same content for both');

    const result = installCommands(projectRoot);

    expect(result.installedCount).toBe(0);
    expect(result.alreadyInstalledCount).toBe(1);
    expect(result.commands[0].installed).toBe(false);
    expect(result.commands[0].error).toBeUndefined();
    expect(mockFs.rmSync).not.toHaveBeenCalled();
    expect(mockFs.symlinkSync).not.toHaveBeenCalled();
  });

  // @tests REQ-CODEX-009
  // TC-EDGE-004: readFileSync throws -> isAlreadyInstalled returns false
  it('readFileSync error during content comparison triggers reinstall', () => {
    const sourcePath = path.join(sourceDir, 'tla-parse.md');
    const targetPath = path.join(targetDir, 'tla-parse.md');

    let rmSyncCalled = false;
    mockFs.existsSync.mockImplementation((p) => {
      const normalized = normalizePath(p.toString());
      if (normalized === normalizePath(sourceDir)) return true;
      if (normalized === normalizePath(sourcePath)) return true;
      if (normalized === normalizePath(targetPath)) return !rmSyncCalled;
      return false;
    });

    mockFs.readdirSync.mockReturnValue([
      { name: 'tla-parse.md', isFile: () => true, isDirectory: () => false } as any,
    ]);

    mockFs.lstatSync.mockReturnValue({
      isSymbolicLink: () => false,
      isFile: () => true,
      isDirectory: () => false,
    } as any);

    // readFileSync throws (permission denied)
    mockFs.readFileSync.mockImplementation(() => {
      throw new Error('EACCES: permission denied');
    });

    mockFs.rmSync.mockImplementation(() => { rmSyncCalled = true; });
    mockFs.symlinkSync.mockImplementation(() => {});

    const result = installCommands(projectRoot);

    // isAlreadyInstalled returns false due to read error -> reinstall triggered
    expect(result.installedCount).toBe(1);
    expect(result.commands[0].installed).toBe(true);
  });

  // --- REQ-CODEX-011: Remove stale target before reinstall ---

  // @tests REQ-CODEX-011, SCN-CODEX-011-01
  it('stale command file is removed and reinstalled', () => {
    const sourcePath = path.join(sourceDir, 'tla-parse.md');
    const targetPath = path.join(targetDir, 'tla-parse.md');

    let rmSyncCalled = false;
    mockFs.existsSync.mockImplementation((p) => {
      const normalized = normalizePath(p.toString());
      if (normalized === normalizePath(sourceDir)) return true;
      if (normalized === normalizePath(sourcePath)) return true;
      if (normalized === normalizePath(targetPath)) return !rmSyncCalled;
      return false;
    });

    mockFs.readdirSync.mockReturnValue([
      { name: 'tla-parse.md', isFile: () => true, isDirectory: () => false } as any,
    ]);

    mockFs.lstatSync.mockReturnValue({
      isSymbolicLink: () => false,
      isFile: () => true,
      isDirectory: () => false,
    } as any);

    mockFs.readFileSync.mockImplementation((p: fs.PathOrFileDescriptor) => {
      const normalized = normalizePath(p.toString());
      if (normalized === normalizePath(targetPath)) return 'old content';
      if (normalized === normalizePath(sourcePath)) return 'new content';
      return '';
    });

    mockFs.rmSync.mockImplementation(() => { rmSyncCalled = true; });
    mockFs.symlinkSync.mockImplementation(() => {});

    const result = installCommands(projectRoot);

    expect(mockFs.rmSync).toHaveBeenCalledWith(targetPath, { force: true });
    expect(mockFs.symlinkSync).toHaveBeenCalledTimes(1);
    expect(result.commands[0].installed).toBe(true);
    expect(result.commands[0].symlinked).toBe(true);
  });

  // @tests REQ-CODEX-011, SCN-CODEX-011-03
  it('permission failure during stale removal returns error field', () => {
    const sourcePath = path.join(sourceDir, 'tla-parse.md');
    const targetPath = path.join(targetDir, 'tla-parse.md');

    mockFs.existsSync.mockImplementation((p) => {
      const normalized = normalizePath(p.toString());
      if (normalized === normalizePath(sourceDir)) return true;
      if (normalized === normalizePath(sourcePath)) return true;
      if (normalized === normalizePath(targetPath)) return true;
      return false;
    });

    mockFs.readdirSync.mockReturnValue([
      { name: 'tla-parse.md', isFile: () => true, isDirectory: () => false } as any,
    ]);

    mockFs.lstatSync.mockReturnValue({
      isSymbolicLink: () => false,
      isFile: () => true,
      isDirectory: () => false,
    } as any);

    mockFs.readFileSync.mockImplementation((p: fs.PathOrFileDescriptor) => {
      const normalized = normalizePath(p.toString());
      if (normalized === normalizePath(targetPath)) return 'old content';
      if (normalized === normalizePath(sourcePath)) return 'new content';
      return '';
    });

    const permissionError = new Error('EPERM: operation not permitted');
    (permissionError as NodeJS.ErrnoException).code = 'EPERM';
    mockFs.rmSync.mockImplementation(() => { throw permissionError; });

    const result = installCommands(projectRoot);

    expect(result.success).toBe(false);
    expect(result.failedCount).toBe(1);
    expect(result.commands[0].installed).toBe(false);
    expect(result.commands[0].error).toContain('Failed to remove stale target');
    expect(mockFs.symlinkSync).not.toHaveBeenCalled();
  });
});
