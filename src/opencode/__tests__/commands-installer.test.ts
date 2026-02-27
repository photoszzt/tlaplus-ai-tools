import * as fs from 'fs';
import * as path from 'path';
import * as paths from '../paths';
import {
  enumerateCommands,
  installCommands,
  uninstallCommand,
  uninstallAllCommands,
} from '../commands-installer';

jest.mock('fs');
jest.mock('../paths');

const mockFs = fs as jest.Mocked<typeof fs>;
const mockPaths = paths as jest.Mocked<typeof paths>;

// Helper to normalize paths for cross-platform comparison
function normalizePath(p: string): string {
  return p.split(path.sep).join('/');
}

describe('commands-installer', () => {
  beforeEach(() => {
    jest.clearAllMocks();
  });

  describe('enumerateCommands', () => {
    it('returns empty array when source directory does not exist', () => {
      mockFs.existsSync.mockReturnValue(false);

      const result = enumerateCommands('/nonexistent');

      expect(result).toEqual([]);
    });

    it('returns empty array when no .md files exist', () => {
      mockFs.existsSync.mockReturnValue(true);
      mockFs.readdirSync.mockReturnValue([
        { name: 'README.txt', isFile: () => true, isDirectory: () => false } as any,
        { name: 'subdir', isFile: () => false, isDirectory: () => true } as any,
      ]);

      const result = enumerateCommands('/commands');

      expect(result).toEqual([]);
    });

    it('returns sorted array of command names without .md extension', () => {
      mockFs.existsSync.mockReturnValue(true);
      mockFs.readdirSync.mockReturnValue([
        { name: 'tla-check.md', isFile: () => true, isDirectory: () => false } as any,
        { name: 'tla-parse.md', isFile: () => true, isDirectory: () => false } as any,
        { name: 'README.txt', isFile: () => true, isDirectory: () => false } as any,
        { name: 'tla-smoke.md', isFile: () => true, isDirectory: () => false } as any,
      ]);

      const result = enumerateCommands('/commands');

      expect(result).toEqual(['tla-check', 'tla-parse', 'tla-smoke']);
    });
  });

  describe('installCommands - project mode', () => {
    const projectRoot = '/project';
    const sourceDir = '/project/commands';
    const targetDir = '/project/.opencode/commands';

    beforeEach(() => {
      mockPaths.getCanonicalDir.mockReturnValue(targetDir);
    });

    it('creates symlinks for all commands', () => {
      mockFs.existsSync.mockImplementation((p) => {
        const normalized = normalizePath(p.toString());
        if (normalized === normalizePath(sourceDir)) return true;
        if (normalized === normalizePath(path.join(sourceDir, 'tla-parse.md'))) return true;
        if (normalized === normalizePath(path.join(sourceDir, 'tla-check.md'))) return true;
        return false;
      });

      mockFs.readdirSync.mockReturnValue([
        { name: 'tla-parse.md', isFile: () => true, isDirectory: () => false } as any,
        { name: 'tla-check.md', isFile: () => true, isDirectory: () => false } as any,
      ]);

      mockFs.symlinkSync.mockImplementation(() => {});

      const result = installCommands(projectRoot);

      expect(result.success).toBe(true);
      expect(result.installedCount).toBe(2);
      expect(result.alreadyInstalledCount).toBe(0);
      expect(result.failedCount).toBe(0);
      expect(result.commands).toHaveLength(2);
      expect(result.commands[0].symlinked).toBe(true);
      expect(result.commands[1].symlinked).toBe(true);
      expect(mockFs.symlinkSync).toHaveBeenCalledTimes(2);
    });

    it('falls back to copy when symlink fails', () => {
      mockFs.existsSync.mockImplementation((p) => {
        const normalized = normalizePath(p.toString());
        if (normalized === normalizePath(sourceDir)) return true;
        if (normalized === normalizePath(path.join(sourceDir, 'tla-parse.md'))) return true;
        return false;
      });

      mockFs.readdirSync.mockReturnValue([
        { name: 'tla-parse.md', isFile: () => true, isDirectory: () => false } as any,
      ]);

      mockFs.symlinkSync.mockImplementation(() => {
        throw new Error('Symlink not supported');
      });

      mockFs.copyFileSync.mockImplementation(() => {});

      const result = installCommands(projectRoot);

      expect(result.success).toBe(true);
      expect(result.installedCount).toBe(1);
      expect(result.commands[0].symlinked).toBe(false);
      expect(mockFs.symlinkSync).toHaveBeenCalledTimes(1);
      expect(mockFs.copyFileSync).toHaveBeenCalledTimes(1);
    });

    it('skips already installed commands (symlink)', () => {
      const targetPath = path.join(targetDir, 'tla-parse.md');
      const sourcePath = path.join(sourceDir, 'tla-parse.md');

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
        isSymbolicLink: () => true,
        isFile: () => false,
        isDirectory: () => false,
      } as any);

      mockFs.readlinkSync.mockReturnValue(sourcePath);

      const result = installCommands(projectRoot);

      expect(result.success).toBe(true);
      expect(result.installedCount).toBe(0);
      expect(result.alreadyInstalledCount).toBe(1);
      expect(result.commands[0].installed).toBe(false);
      expect(mockFs.symlinkSync).not.toHaveBeenCalled();
    });

    it('skips already installed commands (copy)', () => {
      const targetPath = path.join(targetDir, 'tla-parse.md');
      const sourcePath = path.join(sourceDir, 'tla-parse.md');

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

      const result = installCommands(projectRoot);

      expect(result.success).toBe(true);
      expect(result.installedCount).toBe(0);
      expect(result.alreadyInstalledCount).toBe(1);
      expect(result.commands[0].installed).toBe(false);
      expect(mockFs.symlinkSync).not.toHaveBeenCalled();
    });

    it('reports error when source file missing', () => {
      mockFs.existsSync.mockImplementation((p) => {
        const normalized = normalizePath(p.toString());
        if (normalized === normalizePath(sourceDir)) return true;
        return false;
      });

      mockFs.readdirSync.mockReturnValue([
        { name: 'tla-parse.md', isFile: () => true, isDirectory: () => false } as any,
      ]);

      const result = installCommands(projectRoot);

      expect(result.success).toBe(false);
      expect(result.failedCount).toBe(1);
      expect(result.commands[0].error).toContain('Source file not found');
    });

    // @tests REQ-CODEX-011, SCN-CODEX-011-01
    it('removes stale target and reinstalls when target exists but incorrect', () => {
      const targetPath = path.join(targetDir, 'tla-parse.md');
      const sourcePath = path.join(sourceDir, 'tla-parse.md');

      // First call: existsSync for sourceDir, sourcePath, targetPath (isAlreadyInstalled check),
      // and targetPath again (stale removal check) all return true.
      // After rmSync removes the stale target, the next existsSync for targetPath returns false
      // (so the symlink path proceeds without error).
      let rmSyncCalled = false;
      mockFs.existsSync.mockImplementation((p) => {
        const normalized = normalizePath(p.toString());
        if (normalized === normalizePath(sourceDir)) return true;
        if (normalized === normalizePath(sourcePath)) return true;
        if (normalized === normalizePath(targetPath)) {
          // After rmSync is called, the target no longer exists
          return !rmSyncCalled;
        }
        return false;
      });

      mockFs.readdirSync.mockReturnValue([
        { name: 'tla-parse.md', isFile: () => true, isDirectory: () => false } as any,
      ]);

      mockFs.lstatSync.mockReturnValue({
        isSymbolicLink: () => true,
        isFile: () => false,
        isDirectory: () => false,
      } as any);

      mockFs.readlinkSync.mockReturnValue('/wrong/path');

      mockFs.rmSync.mockImplementation(() => {
        rmSyncCalled = true;
      });

      mockFs.symlinkSync.mockImplementation(() => {});

      const result = installCommands(projectRoot);

      expect(result.success).toBe(true);
      expect(result.installedCount).toBe(1);
      expect(result.failedCount).toBe(0);
      expect(result.commands[0].installed).toBe(true);
      expect(result.commands[0].symlinked).toBe(true);
      expect(result.commands[0].error).toBeUndefined();
      expect(mockFs.rmSync).toHaveBeenCalledWith(targetPath, { force: true });
      expect(mockFs.symlinkSync).toHaveBeenCalledTimes(1);
    });

    // @tests SCN-CODEX-011-03
    it('reports error when permission denied removing stale target', () => {
      const targetPath = path.join(targetDir, 'tla-parse.md');
      const sourcePath = path.join(sourceDir, 'tla-parse.md');

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
        isSymbolicLink: () => true,
        isFile: () => false,
        isDirectory: () => false,
      } as any);

      mockFs.readlinkSync.mockReturnValue('/wrong/path');

      const permissionError = new Error('EPERM: operation not permitted');
      (permissionError as NodeJS.ErrnoException).code = 'EPERM';
      mockFs.rmSync.mockImplementation(() => {
        throw permissionError;
      });

      const result = installCommands(projectRoot);

      expect(result.success).toBe(false);
      expect(result.failedCount).toBe(1);
      expect(result.commands[0].installed).toBe(false);
      expect(result.commands[0].error).toContain('Failed to remove stale target');
      expect(mockFs.symlinkSync).not.toHaveBeenCalled();
    });

    it('is idempotent - running twice produces same result', () => {
      const targetPath = path.join(targetDir, 'tla-parse.md');
      const sourcePath = path.join(sourceDir, 'tla-parse.md');

      mockFs.readdirSync.mockReturnValue([
        { name: 'tla-parse.md', isFile: () => true, isDirectory: () => false } as any,
      ]);

      mockFs.existsSync.mockImplementation((p) => {
        const normalized = normalizePath(p.toString());
        if (normalized === normalizePath(sourceDir)) return true;
        if (normalized === normalizePath(sourcePath)) return true;
        return false;
      });

      mockFs.symlinkSync.mockImplementation(() => {});

      const result1 = installCommands(projectRoot);
      expect(result1.installedCount).toBe(1);

      mockFs.existsSync.mockImplementation((p) => {
        const normalized = normalizePath(p.toString());
        if (normalized === normalizePath(sourceDir)) return true;
        if (normalized === normalizePath(sourcePath)) return true;
        if (normalized === normalizePath(targetPath)) return true;
        return false;
      });

      mockFs.lstatSync.mockReturnValue({
        isSymbolicLink: () => true,
        isFile: () => false,
        isDirectory: () => false,
      } as any);

      mockFs.readlinkSync.mockReturnValue(sourcePath);

      const result2 = installCommands(projectRoot);
      expect(result2.installedCount).toBe(0);
      expect(result2.alreadyInstalledCount).toBe(1);
    });
  });

  describe('installCommands - global mode', () => {
    const globalPackageRoot = '/usr/local/lib/node_modules/tlaplus-ai-tools';
    const sourceDir = path.join(globalPackageRoot, 'commands');
    const targetDir = '/home/user/.config/opencode/commands';

    beforeEach(() => {
      mockPaths.getCanonicalDir.mockReturnValue(targetDir);
    });

    it('creates symlinks in global directory', () => {
      mockFs.existsSync.mockImplementation((p) => {
        const normalized = normalizePath(p.toString());
        if (normalized === normalizePath(sourceDir)) return true;
        if (normalized === normalizePath(path.join(sourceDir, 'tla-parse.md'))) return true;
        return false;
      });

      mockFs.readdirSync.mockReturnValue([
        { name: 'tla-parse.md', isFile: () => true, isDirectory: () => false } as any,
      ]);

      mockFs.symlinkSync.mockImplementation(() => {});

      const result = installCommands(globalPackageRoot);

      expect(result.success).toBe(true);
      expect(result.installedCount).toBe(1);
      expect(result.commands[0].symlinked).toBe(true);
      expect(mockPaths.getCanonicalDir).toHaveBeenCalled();
    });
  });

  describe('uninstallCommand', () => {
    it('removes command file and returns true', () => {
      const targetDir = '/project/.opencode/commands';
      const targetPath = path.join(targetDir, 'tla-parse.md');

      mockFs.existsSync.mockReturnValue(true);
      mockFs.rmSync.mockImplementation(() => {});

      const result = uninstallCommand('tla-parse', targetDir);

      expect(result).toBe(true);
      expect(mockFs.rmSync).toHaveBeenCalledWith(targetPath, { force: true });
    });

    it('returns false when command not installed', () => {
      mockFs.existsSync.mockReturnValue(false);

      const result = uninstallCommand('tla-parse', '/project/.opencode/commands');

      expect(result).toBe(false);
      expect(mockFs.rmSync).not.toHaveBeenCalled();
    });
  });

  describe('uninstallAllCommands', () => {
    const projectRoot = '/project';
    const targetDir = '/project/.opencode/commands';

    beforeEach(() => {
      mockPaths.getCanonicalDir.mockReturnValue(targetDir);
    });

    it('removes all command files and returns count', () => {
      mockFs.existsSync.mockReturnValue(true);
      mockFs.readdirSync.mockReturnValue([
        { name: 'tla-parse.md', isFile: () => true, isDirectory: () => false } as any,
        { name: 'tla-check.md', isFile: () => true, isDirectory: () => false } as any,
        { name: 'README.txt', isFile: () => true, isDirectory: () => false } as any,
      ]);

      mockFs.rmSync.mockImplementation(() => {});

      const result = uninstallAllCommands();

      expect(result).toBe(2);
      expect(mockFs.rmSync).toHaveBeenCalledTimes(2);
    });

    it('returns 0 when commands directory does not exist', () => {
      mockFs.existsSync.mockReturnValue(false);

      const result = uninstallAllCommands();

      expect(result).toBe(0);
      expect(mockFs.rmSync).not.toHaveBeenCalled();
    });
  });
});
