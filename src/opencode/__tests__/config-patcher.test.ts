import * as fs from 'fs';
import * as path from 'path';
import * as os from 'os';
import {
  patchOpenCodeConfig,
  isConfigPatched,
} from '../config-patcher';

jest.mock('fs');
jest.mock('os');

const mockFs = fs as jest.Mocked<typeof fs>;
const mockOs = os as jest.Mocked<typeof os>;

// Helper to normalize paths for cross-platform comparison
function normalizePath(p: string): string {
  return p.split(path.sep).join('/');
}

describe('config-patcher', () => {
  let tempDir: string;
  let configPath: string;
  let projectRoot: string;
  let pluginRoot: string;

  beforeEach(() => {
    jest.clearAllMocks();
    tempDir = '/tmp/test-opencode';
    configPath = path.join(tempDir, 'opencode.json');
    projectRoot = '/project';
    pluginRoot = '/plugin';

    mockOs.platform.mockReturnValue('linux');
    mockOs.homedir.mockReturnValue('/home/user');
  });

  describe('patchOpenCodeConfig', () => {

    describe('global mode', () => {
      it('should create new config with global mode command', async () => {
        mockFs.existsSync.mockReturnValue(false);
        mockFs.mkdirSync.mockImplementation(() => undefined);
        mockFs.writeFileSync.mockImplementation(() => undefined);
        mockFs.renameSync.mockImplementation(() => undefined);

        const result = await patchOpenCodeConfig(configPath, pluginRoot);

        expect(result.success).toBe(true);
        expect(result.created).toBe(true);
        expect(result.modified).toBe(true);

        const writeCall = mockFs.writeFileSync.mock.calls[0];
        const writtenContent = writeCall[1] as string;
        const config = JSON.parse(writtenContent);

        expect(config.mcp.tlaplus).toEqual({
          type: 'local',
          command: ['tlaplus-ai-tools'],
          enabled: true,
        });
      });

      it('should patch existing config with global command', async () => {
        const existingConfig = {
          mcp: {
            otherServer: {
              type: 'local',
              command: ['other'],
              enabled: true,
            },
          },
        };

        mockFs.existsSync.mockImplementation((p) => {
          if (p === configPath) return true;
          if (p === `${configPath}.bak`) return false;
          return false;
        });

        mockFs.statSync.mockReturnValue({ isFile: () => true } as fs.Stats);
        mockFs.readFileSync.mockReturnValue(JSON.stringify(existingConfig));
        mockFs.writeFileSync.mockImplementation(() => undefined);
        mockFs.renameSync.mockImplementation(() => undefined);

        const result = await patchOpenCodeConfig(configPath, pluginRoot);

        expect(result.success).toBe(true);
        expect(result.created).toBe(false);
        expect(result.modified).toBe(true);

        const writeCall = mockFs.writeFileSync.mock.calls.find(
          (call) => call[0] === `${configPath}.tmp`
        );
        const writtenContent = writeCall![1] as string;
        const config = JSON.parse(writtenContent);

        expect(config.mcp.otherServer).toEqual(existingConfig.mcp.otherServer);
        expect(config.mcp.tlaplus).toEqual({
          type: 'local',
          command: ['tlaplus-ai-tools'],
          enabled: true,
        });
      });
    });

    describe('idempotency', () => {
      it('should not modify already-correct global config', async () => {
        const correctConfig = {
          mcp: {
            tlaplus: {
              type: 'local',
              command: ['tlaplus-ai-tools'],
              enabled: true,
            },
          },
        };

        mockFs.existsSync.mockReturnValue(true);
        mockFs.statSync.mockReturnValue({ isFile: () => true } as fs.Stats);
        mockFs.readFileSync.mockReturnValue(JSON.stringify(correctConfig));

        const result = await patchOpenCodeConfig(configPath, pluginRoot);

        expect(result.success).toBe(true);
        expect(result.created).toBe(false);
        expect(result.modified).toBe(false);
        expect(mockFs.writeFileSync).not.toHaveBeenCalled();
      });

      it('should update config if command differs', async () => {
        const wrongConfig = {
          mcp: {
            tlaplus: {
              type: 'local',
              command: ['wrong', 'command'],
              enabled: true,
            },
          },
        };

        mockFs.existsSync.mockImplementation((p) => {
          if (p === configPath) return true;
          if (p === `${configPath}.bak`) return false;
          return false;
        });

        mockFs.statSync.mockReturnValue({ isFile: () => true } as fs.Stats);
        mockFs.readFileSync.mockReturnValue(JSON.stringify(wrongConfig));
        mockFs.writeFileSync.mockImplementation(() => undefined);
        mockFs.renameSync.mockImplementation(() => undefined);

        const result = await patchOpenCodeConfig(configPath, pluginRoot);

        expect(result.success).toBe(true);
        expect(result.modified).toBe(true);
      });
    });

    describe('backup creation', () => {
      it('should create backup when modifying existing config', async () => {
        const existingConfig = { mcp: {} };

        mockFs.existsSync.mockImplementation((p) => {
          if (p === configPath) return true;
          if (p === `${configPath}.bak`) return false;
          return false;
        });

        mockFs.statSync.mockReturnValue({ isFile: () => true } as fs.Stats);
        mockFs.readFileSync.mockReturnValue(JSON.stringify(existingConfig));
        mockFs.writeFileSync.mockImplementation(() => undefined);
        mockFs.renameSync.mockImplementation(() => undefined);

        const result = await patchOpenCodeConfig(configPath, pluginRoot);

        expect(result.success).toBe(true);
        expect(result.backupPath).toBe(`${configPath}.bak`);

        const backupCall = mockFs.writeFileSync.mock.calls.find(
          (call) => call[0] === `${configPath}.bak`
        );
        expect(backupCall).toBeDefined();
      });

      it('should not overwrite existing backup', async () => {
        const existingConfig = { mcp: {} };

        mockFs.existsSync.mockImplementation((p) => {
          if (p === configPath) return true;
          if (p === `${configPath}.bak`) return true;
          return false;
        });

        mockFs.statSync.mockReturnValue({ isFile: () => true } as fs.Stats);
        mockFs.readFileSync.mockReturnValue(JSON.stringify(existingConfig));
        mockFs.writeFileSync.mockImplementation(() => undefined);
        mockFs.renameSync.mockImplementation(() => undefined);

        const result = await patchOpenCodeConfig(configPath, pluginRoot);

        expect(result.success).toBe(true);
        expect(result.backupPath).toBeUndefined();

        const backupCall = mockFs.writeFileSync.mock.calls.find(
          (call) => call[0] === `${configPath}.bak`
        );
        expect(backupCall).toBeUndefined();
      });

      it('should not create backup for new config', async () => {
        mockFs.existsSync.mockImplementation((p) => {
          if (p === configPath) return false;
          return false;
        });

        mockFs.mkdirSync.mockImplementation(() => undefined);
        mockFs.writeFileSync.mockImplementation(() => undefined);
        mockFs.renameSync.mockImplementation(() => undefined);

        const result = await patchOpenCodeConfig(configPath, pluginRoot);

        expect(result.success).toBe(true);
        expect(result.backupPath).toBeUndefined();
      });
    });

    describe('atomic writes', () => {
      it('should write to temp file then rename', async () => {
        mockFs.existsSync.mockImplementation((p) => {
          if (p === configPath) return false;
          return false;
        });

        mockFs.mkdirSync.mockImplementation(() => undefined);
        mockFs.writeFileSync.mockImplementation(() => undefined);
        mockFs.renameSync.mockImplementation(() => undefined);

        await patchOpenCodeConfig(configPath, pluginRoot);

        expect(mockFs.writeFileSync).toHaveBeenCalledWith(
          `${configPath}.tmp`,
          expect.any(String),
          'utf-8'
        );

        expect(mockFs.renameSync).toHaveBeenCalledWith(`${configPath}.tmp`, configPath);
      });

      it('should create directory if missing', async () => {
        mockFs.existsSync.mockImplementation((p) => {
          if (p === configPath) return false;
          if (p === tempDir) return false;
          return false;
        });

        mockFs.mkdirSync.mockImplementation(() => undefined);
        mockFs.writeFileSync.mockImplementation(() => undefined);
        mockFs.renameSync.mockImplementation(() => undefined);

        await patchOpenCodeConfig(configPath, pluginRoot);

        const mkdirCall = mockFs.mkdirSync.mock.calls[0];
        expect(normalizePath(mkdirCall[0] as string)).toBe(normalizePath(tempDir));
        expect(mkdirCall[1]).toEqual({ recursive: true });
      });
    });

    describe('JSONC support', () => {
      it('should parse JSONC with comments', async () => {
        const jsoncContent = `{
  // This is a comment
  "mcp": {
    /* Multi-line
       comment */
    "otherServer": {
      "type": "local",
      "command": ["other"],
      "enabled": true,
    }
  }
}`;

        mockFs.existsSync.mockImplementation((p) => {
          if (p === configPath.replace('.json', '.jsonc')) return true;
          if (p === `${configPath}.bak`) return false;
          return false;
        });

        mockFs.statSync.mockReturnValue({ isFile: () => true } as fs.Stats);
        mockFs.readFileSync.mockReturnValue(jsoncContent);
        mockFs.writeFileSync.mockImplementation(() => undefined);
        mockFs.renameSync.mockImplementation(() => undefined);

        const jsoncPath = configPath.replace('.json', '.jsonc');
        const result = await patchOpenCodeConfig(jsoncPath, projectRoot);

        expect(result.success).toBe(true);
        expect(result.modified).toBe(true);
      });
    });

    describe('error handling', () => {
      it('should handle invalid JSON', async () => {
        mockFs.existsSync.mockImplementation((p) => {
          if (p === configPath) return true;
          return false;
        });

        mockFs.statSync.mockReturnValue({ isFile: () => true } as fs.Stats);
        mockFs.readFileSync.mockReturnValue('invalid json');

        const result = await patchOpenCodeConfig(configPath, pluginRoot);

        expect(result.success).toBe(false);
        expect(result.error).toContain('Failed to parse config');
      });

      it('should handle write errors', async () => {
        mockFs.existsSync.mockImplementation((p) => {
          if (p === configPath) return false;
          return false;
        });

        mockFs.mkdirSync.mockImplementation(() => undefined);
        mockFs.writeFileSync.mockImplementation(() => {
          throw new Error('Write failed');
        });

        const result = await patchOpenCodeConfig(configPath, pluginRoot);

        expect(result.success).toBe(false);
        expect(result.error).toContain('Write failed');
      });
    });
  });

  describe('isConfigPatched', () => {

    it('should return true for correctly patched global config', () => {
      const correctConfig = {
        mcp: {
          tlaplus: {
            type: 'local',
            command: ['tlaplus-ai-tools'],
            enabled: true,
          },
        },
      };

      mockFs.existsSync.mockReturnValue(true);
      mockFs.statSync.mockReturnValue({ isFile: () => true } as fs.Stats);
      mockFs.readFileSync.mockReturnValue(JSON.stringify(correctConfig));

      expect(isConfigPatched(configPath)).toBe(true);
    });

    it('should return false for missing config', () => {
      mockFs.existsSync.mockReturnValue(false);

      expect(isConfigPatched(configPath)).toBe(false);
    });

    it('should return false for wrong command', () => {
      const wrongConfig = {
        mcp: {
          tlaplus: {
            type: 'local',
            command: ['wrong', 'command'],
            enabled: true,
          },
        },
      };

      mockFs.existsSync.mockReturnValue(true);
      mockFs.statSync.mockReturnValue({ isFile: () => true } as fs.Stats);
      mockFs.readFileSync.mockReturnValue(JSON.stringify(wrongConfig));

      expect(isConfigPatched(configPath)).toBe(false);
    });

    it('should return false for disabled server', () => {
      const disabledConfig = {
        mcp: {
          tlaplus: {
            type: 'local',
            command: ['node', './dist/index.js'],
            enabled: false,
          },
        },
      };

      mockFs.existsSync.mockReturnValue(true);
      mockFs.statSync.mockReturnValue({ isFile: () => true } as fs.Stats);
      mockFs.readFileSync.mockReturnValue(JSON.stringify(disabledConfig));

      expect(isConfigPatched(configPath)).toBe(false);
    });

    it('should return false for missing mcp section', () => {
      const noMcpConfig = { someOtherKey: 'value' };

      mockFs.existsSync.mockReturnValue(true);
      mockFs.statSync.mockReturnValue({ isFile: () => true } as fs.Stats);
      mockFs.readFileSync.mockReturnValue(JSON.stringify(noMcpConfig));

      expect(isConfigPatched(configPath)).toBe(false);
    });

    it('should return false for invalid JSON', () => {
      mockFs.existsSync.mockReturnValue(true);
      mockFs.statSync.mockReturnValue({ isFile: () => true } as fs.Stats);
      mockFs.readFileSync.mockReturnValue('invalid json');

      expect(isConfigPatched(configPath)).toBe(false);
    });
  });
});
