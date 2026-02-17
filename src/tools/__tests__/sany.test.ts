import { registerSanyTools } from '../sany';
import { createMockMcpServer, callRegisteredTool } from '../../__tests__/helpers/mock-server';
import { expectMcpTextResponse, expectMcpErrorResponse, expectToolRegistered } from '../../__tests__/helpers/assertions';
import { mockSanySuccess, mockSanyError, mockExtractSymbolsSuccess, mockExtractSymbolsError, mockFsExists } from '../../__tests__/helpers/mock-utils';
import { MINIMAL_CONFIG, NO_TOOLS_CONFIG } from '../../__tests__/fixtures/config-samples';

// Mock dependencies
jest.mock('../../utils/paths');
jest.mock('../../utils/sany');
jest.mock('../../utils/symbols');
jest.mock('../../utils/jarfile');
jest.mock('../../utils/tla-tools');
jest.mock('fs', () => ({
  existsSync: jest.fn(),
  promises: {
    readdir: jest.fn(),
    readFile: jest.fn()
  }
}));

import { resolveAndValidatePath } from '../../utils/paths';
import { runSanyParse, parseSanyOutput } from '../../utils/sany';
import { extractSymbols } from '../../utils/symbols';
import * as jarfile from '../../utils/jarfile';
import * as tlaTools from '../../utils/tla-tools';
import * as fs from 'fs';

describe('SANY Tools', () => {
  let mockServer: ReturnType<typeof createMockMcpServer>;

  beforeEach(() => {
    jest.clearAllMocks();
    mockServer = createMockMcpServer();
    (resolveAndValidatePath as jest.Mock).mockImplementation((path) => path);
    (tlaTools.getModuleSearchPaths as jest.Mock).mockReturnValue([]);
    (jarfile.isJarfileUri as jest.Mock).mockImplementation((p: string) => p.startsWith('jarfile:'));
  });

  describe('Tool Registration', () => {
    it('registers all three SANY tools', async () => {
      await registerSanyTools(mockServer, MINIMAL_CONFIG);

      expectToolRegistered(mockServer, 'sany_parse');
      expectToolRegistered(mockServer, 'sany_symbol');
      expectToolRegistered(mockServer, 'sany_modules');

      expect(mockServer.tool).toHaveBeenCalledTimes(3);
    });
  });

  describe('sany_parse', () => {
    beforeEach(async () => {
      await registerSanyTools(mockServer, MINIMAL_CONFIG);
    });

    it('returns success for valid TLA+ file', async () => {
      (fs.existsSync as jest.Mock).mockReturnValue(true);
      const mocks = mockSanySuccess();
      (runSanyParse as jest.Mock).mockImplementation(mocks.runSanyParse);
      (parseSanyOutput as jest.Mock).mockImplementation(mocks.parseSanyOutput);

      const response = await callRegisteredTool(mockServer, 'sany_parse', {
        fileName: '/mock/test.tla'
      });

      expectMcpTextResponse(response, 'No errors found');
      expect(runSanyParse).toHaveBeenCalledWith(
        '/mock/test.tla',
        MINIMAL_CONFIG.toolsDir,
        undefined
      );
    });

    it('returns error for missing file', async () => {
      (fs.existsSync as jest.Mock).mockReturnValue(false);

      const response = await callRegisteredTool(mockServer, 'sany_parse', {
        fileName: '/mock/missing.tla'
      });

      expectMcpErrorResponse(response, 'does not exist');
    });

    it('returns parse errors when SANY fails', async () => {
      (fs.existsSync as jest.Mock).mockReturnValue(true);
      const mocks = mockSanyError('Unexpected token');
      (runSanyParse as jest.Mock).mockImplementation(mocks.runSanyParse);
      (parseSanyOutput as jest.Mock).mockImplementation(mocks.parseSanyOutput);

      const response = await callRegisteredTool(mockServer, 'sany_parse', {
        fileName: '/mock/error.tla'
      });

      expectMcpErrorResponse(response, 'Parsing of file');
      expectMcpErrorResponse(response, 'line 5');
      expectMcpErrorResponse(response, 'Unexpected token');
    });

    it('returns error when tools directory not configured', async () => {
      await registerSanyTools(mockServer, NO_TOOLS_CONFIG);
      (fs.existsSync as jest.Mock).mockReturnValue(true);

      const response = await callRegisteredTool(mockServer, 'sany_parse', {
        fileName: '/mock/test.tla'
      });

      expectMcpErrorResponse(response, 'tools directory not configured');
    });

    it('handles exceptions gracefully', async () => {
      (fs.existsSync as jest.Mock).mockReturnValue(true);
      (runSanyParse as jest.Mock).mockRejectedValue(new Error('Java not found'));

      const response = await callRegisteredTool(mockServer, 'sany_parse', {
        fileName: '/mock/test.tla'
      });

      expectMcpErrorResponse(response, 'Error [FILE_IO_ERROR]');
      expectMcpErrorResponse(response, 'Java not found');
      expectMcpErrorResponse(response, 'Suggested Actions:');
    });

    describe('jarfile: URI support', () => {
      it('resolves jarfile: URI to filesystem before parsing', async () => {
        (jarfile.resolveJarfilePath as jest.Mock).mockReturnValue('/tmp/cache/Naturals.tla');
        (fs.existsSync as jest.Mock).mockReturnValue(true);
        const mocks = mockSanySuccess();
        (runSanyParse as jest.Mock).mockImplementation(mocks.runSanyParse);
        (parseSanyOutput as jest.Mock).mockImplementation(mocks.parseSanyOutput);

        const response = await callRegisteredTool(mockServer, 'sany_parse', {
          fileName: 'jarfile:/tools/tla2tools.jar!/tla2sany/StandardModules/Naturals.tla'
        });

        expect(jarfile.resolveJarfilePath).toHaveBeenCalledWith(
          'jarfile:/tools/tla2tools.jar!/tla2sany/StandardModules/Naturals.tla'
        );
        expect(runSanyParse).toHaveBeenCalledWith(
          '/tmp/cache/Naturals.tla',
          MINIMAL_CONFIG.toolsDir,
          undefined
        );
        expectMcpTextResponse(response, 'No errors found');
      });

      it('returns error when jarfile resolution fails', async () => {
        (jarfile.resolveJarfilePath as jest.Mock).mockImplementation(() => {
          throw new Error('Entry not found in JAR');
        });

        const response = await callRegisteredTool(mockServer, 'sany_parse', {
          fileName: 'jarfile:/tools/test.jar!/nonexistent.tla'
        });

        expectMcpErrorResponse(response, 'Error resolving jarfile URI');
        expectMcpErrorResponse(response, 'Entry not found in JAR');
      });
    });

    it('uses javaHome from config when provided', async () => {
      const configWithJava = { ...MINIMAL_CONFIG, javaHome: '/custom/java' };
      await registerSanyTools(mockServer, configWithJava);

      (fs.existsSync as jest.Mock).mockReturnValue(true);
      const mocks = mockSanySuccess();
      (runSanyParse as jest.Mock).mockImplementation(mocks.runSanyParse);
      (parseSanyOutput as jest.Mock).mockImplementation(mocks.parseSanyOutput);

      await callRegisteredTool(mockServer, 'sany_parse', {
        fileName: '/mock/test.tla'
      });

      expect(runSanyParse).toHaveBeenCalledWith(
        '/mock/test.tla',
        configWithJava.toolsDir,
        '/custom/java'
      );
    });
  });

  describe('sany_symbol', () => {
    beforeEach(async () => {
      await registerSanyTools(mockServer, MINIMAL_CONFIG);
    });

    it('returns symbols for valid TLA+ file', async () => {
      (fs.existsSync as jest.Mock).mockReturnValue(true);
      const symbolData = {
        schemaVersion: 1,
        constants: ['N'],
        variables: ['x', 'y'],
        statePredicates: ['Init', 'TypeOK'],
        actionPredicates: ['Next'],
        temporalFormulas: ['Spec'],
        operatorsWithArgs: [],
        theorems: [],
        assumptions: [],
        bestGuess: { init: 'Init', next: 'Next', spec: 'Spec' }
      };
      const mocks = mockExtractSymbolsSuccess(symbolData);
      (extractSymbols as jest.Mock).mockImplementation(mocks.extractSymbols);

      const response = await callRegisteredTool(mockServer, 'sany_symbol', {
        fileName: '/mock/test.tla'
      });

      const parsed = JSON.parse(response.content[0].text);
      expect(parsed.schemaVersion).toBe(1);
      expect(parsed.constants).toContain('N');
      expect(parsed.variables).toContain('x');
      expect(parsed.bestGuess.init).toBe('Init');
    });

    it('respects includeExtendedModules flag', async () => {
      (fs.existsSync as jest.Mock).mockReturnValue(true);
      const mocks = mockExtractSymbolsSuccess();
      (extractSymbols as jest.Mock).mockImplementation(mocks.extractSymbols);

      await callRegisteredTool(mockServer, 'sany_symbol', {
        fileName: '/mock/test.tla',
        includeExtendedModules: true
      });

      expect(extractSymbols).toHaveBeenCalledWith(
        '/mock/test.tla',
        MINIMAL_CONFIG.toolsDir,
        true,
        undefined
      );
    });

    it('defaults includeExtendedModules to false', async () => {
      (fs.existsSync as jest.Mock).mockReturnValue(true);
      const mocks = mockExtractSymbolsSuccess();
      (extractSymbols as jest.Mock).mockImplementation(mocks.extractSymbols);

      await callRegisteredTool(mockServer, 'sany_symbol', {
        fileName: '/mock/test.tla'
      });

      expect(extractSymbols).toHaveBeenCalledWith(
        '/mock/test.tla',
        MINIMAL_CONFIG.toolsDir,
        false,
        undefined
      );
    });

    it('returns error for missing file', async () => {
      (fs.existsSync as jest.Mock).mockReturnValue(false);

      const response = await callRegisteredTool(mockServer, 'sany_symbol', {
        fileName: '/mock/missing.tla'
      });

      expectMcpErrorResponse(response, 'does not exist');
    });

    it('returns error when tools directory not configured', async () => {
      await registerSanyTools(mockServer, NO_TOOLS_CONFIG);
      (fs.existsSync as jest.Mock).mockReturnValue(true);

      const response = await callRegisteredTool(mockServer, 'sany_symbol', {
        fileName: '/mock/test.tla'
      });

      expectMcpErrorResponse(response, 'tools directory not configured');
    });

    it('returns helpful error when extraction fails', async () => {
      (fs.existsSync as jest.Mock).mockReturnValue(true);
      (extractSymbols as jest.Mock).mockRejectedValue(new Error('Failed to parse XML'));

      const response = await callRegisteredTool(mockServer, 'sany_symbol', {
        fileName: '/mock/test.tla'
      });

      expectMcpErrorResponse(response, 'Error [FILE_IO_ERROR]');
      expectMcpErrorResponse(response, 'Failed to parse XML');
      expectMcpErrorResponse(response, 'Suggested Actions:');
    });

    describe('jarfile: URI support', () => {
      it('resolves jarfile: URI to filesystem before extracting symbols', async () => {
        (jarfile.resolveJarfilePath as jest.Mock).mockReturnValue('/tmp/cache/Naturals.tla');
        (fs.existsSync as jest.Mock).mockReturnValue(true);
        const symbolData = {
          schemaVersion: 1,
          moduleName: 'Naturals',
          constants: [],
          variables: [],
          statePredicates: [],
          actionPredicates: [],
          temporalFormulas: [],
          operatorsWithArgs: [],
          theorems: [],
          assumptions: [],
          bestGuess: {}
        };
        const mocks = mockExtractSymbolsSuccess(symbolData);
        (extractSymbols as jest.Mock).mockImplementation(mocks.extractSymbols);

        const response = await callRegisteredTool(mockServer, 'sany_symbol', {
          fileName: 'jarfile:/tools/tla2tools.jar!/tla2sany/StandardModules/Naturals.tla'
        });

        expect(jarfile.resolveJarfilePath).toHaveBeenCalledWith(
          'jarfile:/tools/tla2tools.jar!/tla2sany/StandardModules/Naturals.tla'
        );
        expect(extractSymbols).toHaveBeenCalledWith(
          '/tmp/cache/Naturals.tla',
          MINIMAL_CONFIG.toolsDir,
          false,
          undefined
        );
        const parsed = JSON.parse(response.content[0].text);
        expect(parsed.moduleName).toBe('Naturals');
      });

      it('returns error when jarfile resolution fails', async () => {
        (jarfile.resolveJarfilePath as jest.Mock).mockImplementation(() => {
          throw new Error('Entry not found in JAR');
        });

        const response = await callRegisteredTool(mockServer, 'sany_symbol', {
          fileName: 'jarfile:/tools/test.jar!/nonexistent.tla'
        });

        expectMcpErrorResponse(response, 'Error resolving jarfile URI');
        expectMcpErrorResponse(response, 'Entry not found in JAR');
      });
    });

    it('uses javaHome from config', async () => {
      const configWithJava = { ...MINIMAL_CONFIG, javaHome: '/custom/java' };
      await registerSanyTools(mockServer, configWithJava);

      (fs.existsSync as jest.Mock).mockReturnValue(true);
      const mocks = mockExtractSymbolsSuccess();
      (extractSymbols as jest.Mock).mockImplementation(mocks.extractSymbols);

      await callRegisteredTool(mockServer, 'sany_symbol', {
        fileName: '/mock/test.tla'
      });

      expect(extractSymbols).toHaveBeenCalledWith(
        '/mock/test.tla',
        configWithJava.toolsDir,
        false,
        '/custom/java'
      );
    });
  });

  describe('sany_modules', () => {
    beforeEach(async () => {
      await registerSanyTools(mockServer, MINIMAL_CONFIG);
    });

    it('lists modules from StandardModules directory', async () => {
      (fs.existsSync as jest.Mock).mockReturnValue(true);
      (fs.promises.readdir as jest.Mock).mockResolvedValue([
        'Naturals.tla',
        'Sequences.tla',
        'FiniteSets.tla',
        '_Internal.tla',
        'readme.txt'
      ]);

      const response = await callRegisteredTool(mockServer, 'sany_modules', {});

      expectMcpTextResponse(response, 'Naturals.tla');
      expectMcpTextResponse(response, 'Sequences.tla');
      expectMcpTextResponse(response, 'FiniteSets.tla');
      expect(response.content[0].text).not.toContain('_Internal.tla');
      expect(response.content[0].text).not.toContain('readme.txt');
    });

    it('handles empty StandardModules directory', async () => {
      (fs.existsSync as jest.Mock).mockReturnValue(true);
      (fs.promises.readdir as jest.Mock).mockResolvedValue([]);

      const response = await callRegisteredTool(mockServer, 'sany_modules', {});

      expectMcpErrorResponse(response, 'No TLA+ modules found');
      expectMcpErrorResponse(response, 'JAR file support');
    });

    it('handles missing StandardModules directory', async () => {
      (fs.existsSync as jest.Mock).mockReturnValue(false);

      const response = await callRegisteredTool(mockServer, 'sany_modules', {});

      expectMcpErrorResponse(response, 'No TLA+ modules found');
    });

    it('returns error when tools directory not configured', async () => {
      await registerSanyTools(mockServer, NO_TOOLS_CONFIG);

      const response = await callRegisteredTool(mockServer, 'sany_modules', {});

      expectMcpErrorResponse(response, 'tools directory not configured');
    });

    it('handles readdir errors gracefully', async () => {
      const standardModulesPath = '/mock/tools/StandardModules';
      (tlaTools.getModuleSearchPaths as jest.Mock).mockReturnValue([standardModulesPath]);
      (fs.existsSync as jest.Mock).mockReturnValue(true);
      (fs.promises.readdir as jest.Mock).mockRejectedValue(new Error('Permission denied'));

      const response = await callRegisteredTool(mockServer, 'sany_modules', {});

      expectMcpErrorResponse(response, 'Warning: Failed to read');
      expectMcpErrorResponse(response, 'Permission denied');
    });

    describe('JAR scanning', () => {
      beforeEach(() => {
        (jarfile.isJarfileUri as jest.Mock).mockImplementation((p: string) => p.startsWith('jarfile:'));
        (jarfile.parseJarfileUri as jest.Mock).mockImplementation((uri: string) => {
          const withoutScheme = uri.slice('jarfile:'.length);
          const sepIdx = withoutScheme.indexOf('!');
          return {
            jarPath: withoutScheme.slice(0, sepIdx),
            innerPath: withoutScheme.slice(sepIdx + 2),
          };
        });
      });

      it('lists modules from JAR roots returned by getModuleSearchPaths', async () => {
        (fs.existsSync as jest.Mock).mockReturnValue(false);
        (tlaTools.getModuleSearchPaths as jest.Mock).mockReturnValue([
          'jarfile:/tools/tla2tools.jar!/tla2sany/StandardModules',
        ]);
        (jarfile.listTlaModulesInJar as jest.Mock).mockReturnValue([
          'jarfile:/tools/tla2tools.jar!/tla2sany/StandardModules/Naturals.tla',
          'jarfile:/tools/tla2tools.jar!/tla2sany/StandardModules/Sequences.tla',
        ]);

        const response = await callRegisteredTool(mockServer, 'sany_modules', {});

        expect(response.content[0].text).toContain('Naturals.tla');
        expect(response.content[0].text).toContain('Sequences.tla');
        expect(response.content[0].text).toContain('jarfile:');
      });

      it('combines filesystem and JAR modules', async () => {
        (fs.existsSync as jest.Mock).mockReturnValue(true);
        (fs.promises.readdir as jest.Mock).mockResolvedValue([
          'LocalModule.tla',
        ]);
        (tlaTools.getModuleSearchPaths as jest.Mock).mockReturnValue([
          'jarfile:/tools/tla2tools.jar!/tla2sany/StandardModules',
        ]);
        (jarfile.listTlaModulesInJar as jest.Mock).mockReturnValue([
          'jarfile:/tools/tla2tools.jar!/tla2sany/StandardModules/Naturals.tla',
        ]);

        const response = await callRegisteredTool(mockServer, 'sany_modules', {});

        expect(response.content[0].text).toContain('LocalModule.tla');
        expect(response.content[0].text).toContain('Naturals.tla');
      });
    });
  });
});
