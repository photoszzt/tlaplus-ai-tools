import * as path from 'path';

const mockStat = jest.fn();
const mockAccess = jest.fn();
const mockReaddir = jest.fn();
const mockExecSync = jest.fn();

jest.mock('fs', () => ({
  promises: {
    stat: (...args: unknown[]) => mockStat(...args),
    access: (...args: unknown[]) => mockAccess(...args),
    readdir: (...args: unknown[]) => mockReaddir(...args)
  }
}));

jest.mock('child_process', () => ({
  execSync: (...args: unknown[]) => mockExecSync(...args)
}));

import {
  resolveAndValidatePath,
  autoDetectToolsDir,
  autoDetectKbDir,
  validateDirectory
} from '../paths';

describe('paths', () => {
  beforeEach(() => {
    mockStat.mockReset();
    mockAccess.mockReset();
    mockReaddir.mockReset();
    mockExecSync.mockReset();
  });

  describe('resolveAndValidatePath', () => {
    it('resolves absolute paths correctly when no workingDir', () => {
      const absolutePath = '/absolute/path/file.txt';

      const result = resolveAndValidatePath(absolutePath, null);
      expect(result).toBe(absolutePath);
    });

    it('resolves relative paths correctly', () => {
      const basePath = '/base/path';
      const relativePath = 'relative/file.txt';
      const expectedPath = path.join(basePath, relativePath);

      const result = resolveAndValidatePath(relativePath, basePath);
      expect(result).toBe(expectedPath);
    });

    it('blocks path traversal with ../', () => {
      const basePath = '/base/path';
      const traversalPath = '../../../etc/passwd';

      expect(() => resolveAndValidatePath(traversalPath, basePath))
        .toThrow('Access denied');
    });

    it('allows any path when workingDir is null', () => {
      const absolutePath = '/anywhere/file.txt';

      const result = resolveAndValidatePath(absolutePath, null);
      expect(result).toBe(absolutePath);
    });

    it('allows traversal when workingDir is null', () => {
      const basePath = null;
      const traversalPath = '../../../etc/passwd';
      const expectedPath = path.resolve(process.cwd(), traversalPath);

      const result = resolveAndValidatePath(traversalPath, basePath);
      expect(result).toBe(expectedPath);
    });

    it('handles Windows-style absolute paths', () => {
      // Windows absolute paths should work regardless of platform
      const windowsAbsolutePath = 'C:\\Users\\test\\file.txt';

      const result = resolveAndValidatePath(windowsAbsolutePath, null);
      // path.isAbsolute recognizes Windows paths even on Unix
      expect(path.isAbsolute(result)).toBe(true);
    });

    it('handles Unix paths correctly', () => {
      const originalPlatform = process.platform;
      Object.defineProperty(process, 'platform', {
        value: 'linux',
        configurable: true
      });

      const basePath = '/base/path';
      const relativePath = 'file.txt';
      const expectedPath = path.join(basePath, relativePath);

      const result = resolveAndValidatePath(relativePath, basePath);
      expect(result).toBe(expectedPath);

      Object.defineProperty(process, 'platform', {
        value: originalPlatform,
        configurable: true
      });
    });

    it('blocks absolute paths when workingDir is specified', () => {
      const basePath = '/base/path';
      const absolutePath = '/etc/passwd';

      expect(() => resolveAndValidatePath(absolutePath, basePath))
        .toThrow('Access denied');
    });

    it('allows paths within working directory', () => {
      const basePath = '/base/path';
      const safePath = 'subdir/file.txt';
      const expectedPath = path.join(basePath, safePath);

      const result = resolveAndValidatePath(safePath, basePath);
      expect(result).toBe(expectedPath);
    });
  });

  describe('autoDetectToolsDir', () => {
    it('detects monorepo tools directory', async () => {
      mockStat.mockResolvedValue({ isDirectory: () => true });
      mockAccess.mockResolvedValue(undefined);

      const result = await autoDetectToolsDir();
      expect(result).not.toBeNull();
      expect(result).toContain('tools');
      expect(mockAccess).toHaveBeenCalledWith(
        expect.stringContaining('tla2tools.jar')
      );
    });

    it('detects standalone tools directory', async () => {
      mockStat
        .mockRejectedValueOnce(new Error('Not found'))
        .mockResolvedValueOnce({ isDirectory: () => true });
      mockAccess.mockResolvedValueOnce(undefined);

      const result = await autoDetectToolsDir();
      expect(result).toContain('tools');
    });

    it('detects npm global tools directory', async () => {
      const npmRoot = '/usr/local/lib/node_modules';
      mockExecSync.mockReturnValue(`${npmRoot}\n`);

      mockStat
        .mockRejectedValueOnce(new Error('Not found'))
        .mockRejectedValueOnce(new Error('Not found'))
        .mockResolvedValueOnce({ isDirectory: () => true });
      mockAccess.mockResolvedValueOnce(undefined);

      const result = await autoDetectToolsDir();
      expect(result).toBe(path.join(npmRoot, '@tlaplus', 'mcp-server', 'tools'));
    });

    it('returns null when npm is not available', async () => {
      mockExecSync.mockImplementation(() => {
        throw new Error('npm not found');
      });

      mockStat.mockRejectedValue(new Error('Not found'));

      const result = await autoDetectToolsDir();
      expect(result).toBeNull();
    });

    it('returns null when no tools directory found', async () => {
      mockStat.mockRejectedValue(new Error('Not found'));
      mockExecSync.mockImplementation(() => {
        throw new Error('npm not found');
      });

      const result = await autoDetectToolsDir();
      expect(result).toBeNull();
    });

    it('validates tla2tools.jar exists in tools directory', async () => {
      mockStat.mockResolvedValue({ isDirectory: () => true });
      mockAccess.mockRejectedValue(new Error('tla2tools.jar not found'));
      mockExecSync.mockImplementation(() => {
        throw new Error('npm not found');
      });

      const result = await autoDetectToolsDir();
      expect(result).toBeNull();
    });

    it('skips directory if it is not a directory', async () => {
      mockStat
        .mockResolvedValueOnce({ isDirectory: () => false }) // monorepo is file
        .mockResolvedValueOnce({ isDirectory: () => true }); // standalone is directory
      mockAccess.mockResolvedValue(undefined);
      mockExecSync.mockImplementation(() => {
        throw new Error('npm not found');
      });

      const result = await autoDetectToolsDir();
      expect(result).toContain('tools');
    });

    it('continues checking when jar validation fails', async () => {
      mockStat
        .mockResolvedValueOnce({ isDirectory: () => true }) // monorepo exists
        .mockResolvedValueOnce({ isDirectory: () => true }); // standalone exists
      mockAccess
        .mockRejectedValueOnce(new Error('jar not found')) // monorepo jar missing
        .mockResolvedValueOnce(undefined); // standalone jar exists
      mockExecSync.mockImplementation(() => {
        throw new Error('npm not found');
      });

      const result = await autoDetectToolsDir();
      expect(result).toContain('tools');
    });
  });

  describe('autoDetectKbDir', () => {
    it('detects monorepo knowledgebase directory', async () => {
      mockStat.mockResolvedValue({ isDirectory: () => true });
      mockReaddir.mockResolvedValue(['README.md', 'intro.md']);

      const result = await autoDetectKbDir();
      expect(result).toContain('knowledgebase');
    });

    it('detects standalone knowledgebase directory', async () => {
      mockStat
        .mockRejectedValueOnce(new Error('Not found')) // monorepo fails
        .mockResolvedValueOnce({ isDirectory: () => true }); // standalone succeeds
      mockReaddir
        .mockResolvedValueOnce(['README.md']);

      const result = await autoDetectKbDir();
      expect(result).toContain('knowledgebase');
    });

    it('detects npm global knowledgebase directory', async () => {
      const npmRoot = '/usr/local/lib/node_modules';
      mockExecSync.mockReturnValue(`${npmRoot}\n`);

      mockStat
        .mockRejectedValueOnce(new Error('Not found')) // monorepo fails
        .mockRejectedValueOnce(new Error('Not found')) // standalone fails
        .mockResolvedValueOnce({ isDirectory: () => true }); // npm global succeeds
      mockReaddir
        .mockResolvedValueOnce(['guide.md']);

      const result = await autoDetectKbDir();
      expect(result).toBe(path.join(npmRoot, '@tlaplus', 'mcp-server', 'resources', 'knowledgebase'));
    });

    it('returns null when no knowledgebase found', async () => {
      mockStat.mockRejectedValue(new Error('Not found'));
      mockExecSync.mockImplementation(() => {
        throw new Error('npm not found');
      });

      const result = await autoDetectKbDir();
      expect(result).toBeNull();
    });

    it('returns null when npm is not available', async () => {
      mockExecSync.mockImplementation(() => {
        throw new Error('npm not found');
      });
      mockStat.mockRejectedValue(new Error('Not found'));

      const result = await autoDetectKbDir();
      expect(result).toBeNull();
    });

    it('skips directory without markdown files', async () => {
      mockStat
        .mockResolvedValueOnce({ isDirectory: () => true }) // monorepo exists
        .mockResolvedValueOnce({ isDirectory: () => true }); // standalone exists
      mockReaddir
        .mockResolvedValueOnce(['file.txt', 'config.json']) // no .md files
        .mockResolvedValueOnce(['guide.md']); // has .md files
      mockExecSync.mockImplementation(() => {
        throw new Error('npm not found');
      });

      const result = await autoDetectKbDir();
      expect(result).toContain('knowledgebase');
    });

    it('handles empty directory', async () => {
      mockStat
        .mockResolvedValueOnce({ isDirectory: () => true });
      mockReaddir
        .mockResolvedValueOnce([]); // empty directory
      mockExecSync.mockImplementation(() => {
        throw new Error('npm not found');
      });

      const result = await autoDetectKbDir();
      expect(result).toBeNull();
    });

    it('skips if not a directory', async () => {
      mockStat
        .mockResolvedValueOnce({ isDirectory: () => false }) // monorepo is file
        .mockResolvedValueOnce({ isDirectory: () => true }); // standalone is directory
      mockReaddir
        .mockResolvedValueOnce(['guide.md']);
      mockExecSync.mockImplementation(() => {
        throw new Error('npm not found');
      });

      const result = await autoDetectKbDir();
      expect(result).toContain('knowledgebase');
    });
  });

  describe('validateDirectory', () => {
    it('succeeds when directory exists', async () => {
      mockStat.mockResolvedValue({ isDirectory: () => true });

      await expect(validateDirectory('/valid/path', 'Test'))
        .resolves.not.toThrow();
    });

    it('throws when path does not exist', async () => {
      const error: any = new Error('ENOENT');
      error.code = 'ENOENT';
      mockStat.mockRejectedValue(error);

      await expect(validateDirectory('/invalid/path', 'Test'))
        .rejects.toThrow('Test directory not found');
    });

    it('throws when path is not a directory', async () => {
      mockStat.mockResolvedValue({ isDirectory: () => false });

      await expect(validateDirectory('/file.txt', 'Test'))
        .rejects.toThrow('Test path exists but is not a directory');
    });

    it('rethrows other errors', async () => {
      const error = new Error('Permission denied');
      mockStat.mockRejectedValue(error);

      await expect(validateDirectory('/forbidden', 'Test'))
        .rejects.toThrow('Permission denied');
    });
  });
});
