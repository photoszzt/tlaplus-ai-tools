import * as fs from 'fs';
import * as path from 'path';
import * as os from 'os';
import {
  getGlobalOpenCodeDir,
  findExistingDir,
  findPluginDir,
  findCommandsDir,
  findSkillsDir,
  findConfigFile,
  parseConfigFile,
  getOpenCodePaths,
  ensureDir,
  getCanonicalDir,
  CANONICAL_DIRS,
  CONFIG_FILENAMES,
} from '../paths';

jest.mock('fs');
jest.mock('os');

const mockFs = fs as jest.Mocked<typeof fs>;
const mockOs = os as jest.Mocked<typeof os>;

describe('OpenCode Paths', () => {
  beforeEach(() => {
    jest.clearAllMocks();
  });

  describe('getGlobalOpenCodeDir', () => {
    it('returns Windows path when platform is win32', () => {
      mockOs.platform.mockReturnValue('win32');
      process.env.APPDATA = 'C:\\Users\\test\\AppData\\Roaming';

      const result = getGlobalOpenCodeDir();

      expect(result).toBe(path.join('C:\\Users\\test\\AppData\\Roaming', 'opencode'));
    });

    it('throws error when APPDATA not set on Windows', () => {
      mockOs.platform.mockReturnValue('win32');
      delete process.env.APPDATA;

      expect(() => getGlobalOpenCodeDir()).toThrow(
        'APPDATA environment variable not set on Windows'
      );
    });

    it('returns Linux path when platform is linux', () => {
      mockOs.platform.mockReturnValue('linux');
      mockOs.homedir.mockReturnValue('/home/test');

      const result = getGlobalOpenCodeDir();

      expect(result).toBe('/home/test/.config/opencode');
    });

    it('returns macOS path when platform is darwin', () => {
      mockOs.platform.mockReturnValue('darwin');
      mockOs.homedir.mockReturnValue('/Users/test');

      const result = getGlobalOpenCodeDir();

      expect(result).toBe('/Users/test/.config/opencode');
    });
  });

  describe('findExistingDir', () => {
    it('returns plural path when both singular and plural exist', () => {
      const baseDir = '/project/.opencode';
      mockFs.existsSync.mockImplementation((p) => {
        const pathStr = p.toString();
        return pathStr.includes('plugins') || pathStr.includes('plugin');
      });
      mockFs.statSync.mockReturnValue({ isDirectory: () => true } as fs.Stats);

      const result = findExistingDir(baseDir, 'plugin', 'plugins');

      expect(result).toBe('/project/.opencode/plugins');
    });

    it('returns singular path when only singular exists', () => {
      const baseDir = '/project/.opencode';
      mockFs.existsSync.mockImplementation((p) => {
        const pathStr = p.toString();
        return pathStr.includes('plugin') && !pathStr.includes('plugins');
      });
      mockFs.statSync.mockReturnValue({ isDirectory: () => true } as fs.Stats);

      const result = findExistingDir(baseDir, 'plugin', 'plugins');

      expect(result).toBe('/project/.opencode/plugin');
    });

    it('returns null when neither exists', () => {
      const baseDir = '/project/.opencode';
      mockFs.existsSync.mockReturnValue(false);

      const result = findExistingDir(baseDir, 'plugin', 'plugins');

      expect(result).toBeNull();
    });

    it('returns null when path exists but is not a directory', () => {
      const baseDir = '/project/.opencode';
      mockFs.existsSync.mockReturnValue(true);
      mockFs.statSync.mockReturnValue({ isDirectory: () => false } as fs.Stats);

      const result = findExistingDir(baseDir, 'plugin', 'plugins');

      expect(result).toBeNull();
    });
  });

  describe('findPluginDir', () => {
    it('returns per-project plugin directory when it exists', () => {
      const projectRoot = '/project';
      mockFs.existsSync.mockImplementation((p) => {
        const pathStr = p.toString();
        return pathStr.includes('/project/.opencode/plugins');
      });
      mockFs.statSync.mockReturnValue({ isDirectory: () => true } as fs.Stats);

      const result = findPluginDir(projectRoot);

      expect(result).toBe('/project/.opencode/plugins');
    });

    it('returns global plugin directory when per-project does not exist', () => {
      const projectRoot = '/project';
      mockOs.platform.mockReturnValue('linux');
      mockOs.homedir.mockReturnValue('/home/test');
      mockFs.existsSync.mockImplementation((p) => {
        const pathStr = p.toString();
        return pathStr.includes('/home/test/.config/opencode/plugins');
      });
      mockFs.statSync.mockReturnValue({ isDirectory: () => true } as fs.Stats);

      const result = findPluginDir(projectRoot);

      expect(result).toBe('/home/test/.config/opencode/plugins');
    });

    it('returns null when no plugin directory exists', () => {
      const projectRoot = '/project';
      mockOs.platform.mockReturnValue('linux');
      mockOs.homedir.mockReturnValue('/home/test');
      mockFs.existsSync.mockReturnValue(false);

      const result = findPluginDir(projectRoot);

      expect(result).toBeNull();
    });
  });

  describe('findCommandsDir', () => {
    it('returns per-project commands directory when it exists', () => {
      const projectRoot = '/project';
      mockFs.existsSync.mockImplementation((p) => {
        const pathStr = p.toString();
        return pathStr.includes('/project/.opencode/commands');
      });
      mockFs.statSync.mockReturnValue({ isDirectory: () => true } as fs.Stats);

      const result = findCommandsDir(projectRoot);

      expect(result).toBe('/project/.opencode/commands');
    });
  });

  describe('findSkillsDir', () => {
    it('returns per-project skills directory when it exists', () => {
      const projectRoot = '/project';
      mockFs.existsSync.mockImplementation((p) => {
        const pathStr = p.toString();
        return pathStr.includes('/project/.opencode/skills');
      });
      mockFs.statSync.mockReturnValue({ isDirectory: () => true } as fs.Stats);

      const result = findSkillsDir(projectRoot);

      expect(result).toBe('/project/.opencode/skills');
    });
  });

  describe('findConfigFile', () => {
    it('returns .json file when both .json and .jsonc exist', () => {
      const projectRoot = '/project';
      mockFs.existsSync.mockReturnValue(true);
      mockFs.statSync.mockReturnValue({ isFile: () => true } as fs.Stats);

      const result = findConfigFile(projectRoot);

      expect(result).toBe('/project/.opencode/opencode.json');
    });

    it('returns .jsonc file when only .jsonc exists', () => {
      const projectRoot = '/project';
      mockFs.existsSync.mockImplementation((p) => {
        const pathStr = p.toString();
        return pathStr.endsWith('opencode.jsonc');
      });
      mockFs.statSync.mockReturnValue({ isFile: () => true } as fs.Stats);

      const result = findConfigFile(projectRoot);

      expect(result).toBe('/project/.opencode/opencode.jsonc');
    });

    it('returns global config when per-project does not exist', () => {
      const projectRoot = '/project';
      mockOs.platform.mockReturnValue('linux');
      mockOs.homedir.mockReturnValue('/home/test');
      mockFs.existsSync.mockImplementation((p) => {
        const pathStr = p.toString();
        return pathStr.includes('/home/test/.config/opencode/opencode.json');
      });
      mockFs.statSync.mockReturnValue({ isFile: () => true } as fs.Stats);

      const result = findConfigFile(projectRoot);

      expect(result).toBe('/home/test/.config/opencode/opencode.json');
    });

    it('returns null when no config file exists', () => {
      const projectRoot = '/project';
      mockOs.platform.mockReturnValue('linux');
      mockOs.homedir.mockReturnValue('/home/test');
      mockFs.existsSync.mockReturnValue(false);

      const result = findConfigFile(projectRoot);

      expect(result).toBeNull();
    });
  });

  describe('parseConfigFile', () => {
    it('parses standard JSON file', () => {
      const configPath = '/project/.opencode/opencode.json';
      const configContent = '{"mcp": {"tlaplus": {"enabled": true}}}';
      mockFs.readFileSync.mockReturnValue(configContent);

      const result = parseConfigFile(configPath);

      expect(result).toEqual({ mcp: { tlaplus: { enabled: true } } });
    });

    it('parses JSONC file with comments', () => {
      const configPath = '/project/.opencode/opencode.jsonc';
      const configContent = `{
  // This is a comment
  "mcp": {
    /* Multi-line
       comment */
    "tlaplus": {
      "enabled": true,
    }
  }
}`;
      mockFs.readFileSync.mockReturnValue(configContent);

      const result = parseConfigFile(configPath);

      expect(result).toEqual({ mcp: { tlaplus: { enabled: true } } });
    });

    it('handles trailing commas in JSONC', () => {
      const configPath = '/project/.opencode/opencode.jsonc';
      const configContent = `{
  "mcp": {
    "tlaplus": {
      "enabled": true,
    },
  },
}`;
      mockFs.readFileSync.mockReturnValue(configContent);

      const result = parseConfigFile(configPath);

      expect(result).toEqual({ mcp: { tlaplus: { enabled: true } } });
    });

    it('throws error for invalid JSON', () => {
      const configPath = '/project/.opencode/opencode.json';
      const configContent = '{invalid json}';
      mockFs.readFileSync.mockReturnValue(configContent);

      expect(() => parseConfigFile(configPath)).toThrow();
    });
  });

  describe('getOpenCodePaths', () => {
    it('returns all paths for a project', () => {
      const projectRoot = '/project';
      mockOs.platform.mockReturnValue('linux');
      mockOs.homedir.mockReturnValue('/home/test');
      mockFs.existsSync.mockImplementation((p) => {
        const pathStr = p.toString();
        return (
          pathStr.includes('/project/.opencode/plugins') ||
          pathStr.includes('/project/.opencode/commands') ||
          pathStr.includes('/project/.opencode/skills') ||
          pathStr.includes('/project/.opencode/opencode.json')
        );
      });
      mockFs.statSync.mockImplementation((p) => {
        const pathStr = p.toString();
        if (pathStr.endsWith('opencode.json')) {
          return { isFile: () => true, isDirectory: () => false } as fs.Stats;
        }
        return { isDirectory: () => true, isFile: () => false } as fs.Stats;
      });

      const result = getOpenCodePaths(projectRoot);

      expect(result).toEqual({
        pluginDir: '/project/.opencode/plugins',
        commandsDir: '/project/.opencode/commands',
        skillsDir: '/project/.opencode/skills',
        configFile: '/project/.opencode/opencode.json',
        globalDir: '/home/test/.config/opencode',
      });
    });
  });

  describe('ensureDir', () => {
    it('creates directory when it does not exist', () => {
      const dirPath = '/project/.opencode/plugins';
      mockFs.existsSync.mockReturnValue(false);
      mockFs.mkdirSync.mockReturnValue(undefined);

      ensureDir(dirPath);

      expect(mockFs.mkdirSync).toHaveBeenCalledWith(dirPath, { recursive: true });
    });

    it('does not create directory when it already exists', () => {
      const dirPath = '/project/.opencode/plugins';
      mockFs.existsSync.mockReturnValue(true);

      ensureDir(dirPath);

      expect(mockFs.mkdirSync).not.toHaveBeenCalled();
    });
  });

  describe('getCanonicalDir', () => {
    it('returns canonical plugin directory path', () => {
      const baseDir = '/project/.opencode';
      const result = getCanonicalDir(baseDir, 'plugin');

      expect(result).toBe('/project/.opencode/plugins');
    });

    it('returns canonical commands directory path', () => {
      const baseDir = '/project/.opencode';
      const result = getCanonicalDir(baseDir, 'command');

      expect(result).toBe('/project/.opencode/commands');
    });

    it('returns canonical skills directory path', () => {
      const baseDir = '/project/.opencode';
      const result = getCanonicalDir(baseDir, 'skill');

      expect(result).toBe('/project/.opencode/skills');
    });

    it('creates directory when createIfMissing is true', () => {
      const baseDir = '/project/.opencode';
      mockFs.existsSync.mockReturnValue(false);
      mockFs.mkdirSync.mockReturnValue(undefined);

      const result = getCanonicalDir(baseDir, 'plugin', true);

      expect(result).toBe('/project/.opencode/plugins');
      expect(mockFs.mkdirSync).toHaveBeenCalledWith('/project/.opencode/plugins', {
        recursive: true,
      });
    });
  });

  describe('constants', () => {
    it('exports canonical directory names', () => {
      expect(CANONICAL_DIRS.PLUGIN).toBe('plugins');
      expect(CANONICAL_DIRS.COMMAND).toBe('commands');
      expect(CANONICAL_DIRS.SKILL).toBe('skills');
    });

    it('exports config filenames', () => {
      expect(CONFIG_FILENAMES).toEqual(['opencode.json', 'opencode.jsonc']);
    });
  });
});
