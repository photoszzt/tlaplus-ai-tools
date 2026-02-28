// Spec: docs/codex-fixes/spec.md
// Contract: docs/codex-fixes/contract.md (installCommands)
// Testing: docs/codex-fixes/testing.md
//
// Contract tests for installCommands stale handling.

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

describe('installCommands - Contract Tests (Codex)', () => {
  const projectRoot = '/project';
  const sourceDir = '/project/commands';
  const targetDir = '/project/.opencode/commands';

  beforeEach(() => {
    jest.clearAllMocks();
    mockPaths.getCanonicalDir.mockReturnValue(targetDir);
  });

  // @tests-contract REQ-CODEX-009
  it('stale command file triggers reinstall (installed: true)', () => {
    const sourcePath = path.join(sourceDir, 'cmd.md');
    const targetPath = path.join(targetDir, 'cmd.md');

    let rmCalled = false;
    mockFs.existsSync.mockImplementation((p) => {
      const n = normalizePath(p.toString());
      if (n === normalizePath(sourceDir)) return true;
      if (n === normalizePath(sourcePath)) return true;
      if (n === normalizePath(targetPath)) return !rmCalled;
      return false;
    });

    mockFs.readdirSync.mockReturnValue([
      { name: 'cmd.md', isFile: () => true, isDirectory: () => false } as any,
    ]);

    mockFs.lstatSync.mockReturnValue({
      isSymbolicLink: () => false,
      isFile: () => true,
      isDirectory: () => false,
    } as any);

    mockFs.readFileSync.mockImplementation((p: fs.PathOrFileDescriptor) => {
      const n = normalizePath(p.toString());
      if (n === normalizePath(targetPath)) return 'old';
      if (n === normalizePath(sourcePath)) return 'new';
      return '';
    });

    mockFs.rmSync.mockImplementation(() => { rmCalled = true; });
    mockFs.symlinkSync.mockImplementation(() => {});

    const result = installCommands(projectRoot);

    // Contract: stale content leads to reinstall
    expect(result.commands[0].installed).toBe(true);
  });

  // @tests-contract REQ-CODEX-011
  it('stale target is removed then reinstalled', () => {
    const sourcePath = path.join(sourceDir, 'cmd.md');
    const targetPath = path.join(targetDir, 'cmd.md');

    let rmCalled = false;
    mockFs.existsSync.mockImplementation((p) => {
      const n = normalizePath(p.toString());
      if (n === normalizePath(sourceDir)) return true;
      if (n === normalizePath(sourcePath)) return true;
      if (n === normalizePath(targetPath)) return !rmCalled;
      return false;
    });

    mockFs.readdirSync.mockReturnValue([
      { name: 'cmd.md', isFile: () => true, isDirectory: () => false } as any,
    ]);

    mockFs.lstatSync.mockReturnValue({
      isSymbolicLink: () => false,
      isFile: () => true,
      isDirectory: () => false,
    } as any);

    mockFs.readFileSync.mockImplementation((p: fs.PathOrFileDescriptor) => {
      const n = normalizePath(p.toString());
      if (n === normalizePath(targetPath)) return 'old';
      if (n === normalizePath(sourcePath)) return 'new';
      return '';
    });

    mockFs.rmSync.mockImplementation(() => { rmCalled = true; });
    mockFs.symlinkSync.mockImplementation(() => {});

    const result = installCommands(projectRoot);

    expect(result.commands[0].installed).toBe(true);
    expect(result.commands[0].error).toBeUndefined();
  });

  // @tests-contract REQ-CODEX-009
  it('matching content means already installed (skip)', () => {
    const sourcePath = path.join(sourceDir, 'cmd.md');
    const targetPath = path.join(targetDir, 'cmd.md');

    mockFs.existsSync.mockImplementation((p) => {
      const n = normalizePath(p.toString());
      if (n === normalizePath(sourceDir)) return true;
      if (n === normalizePath(sourcePath)) return true;
      if (n === normalizePath(targetPath)) return true;
      return false;
    });

    mockFs.readdirSync.mockReturnValue([
      { name: 'cmd.md', isFile: () => true, isDirectory: () => false } as any,
    ]);

    mockFs.lstatSync.mockReturnValue({
      isSymbolicLink: () => false,
      isFile: () => true,
      isDirectory: () => false,
    } as any);

    mockFs.readFileSync.mockReturnValue('identical content');

    const result = installCommands(projectRoot);

    expect(result.commands[0].installed).toBe(false);
    expect(result.alreadyInstalledCount).toBe(1);
  });
});
