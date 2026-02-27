// Spec: docs/codex-fixes/spec.md
// Testing: docs/codex-fixes/testing.md
//
// White-box tests for Finding 2 (continued): jarfile: URI validation in SANY tools

import { registerSanyTools } from '../sany';
import { createMockMcpServer, callRegisteredTool } from '../../__tests__/helpers/mock-server';
import { expectMcpTextResponse, expectMcpErrorResponse } from '../../__tests__/helpers/assertions';
import { mockSanySuccess, mockExtractSymbolsSuccess } from '../../__tests__/helpers/mock-utils';
import { MINIMAL_CONFIG } from '../../__tests__/fixtures/config-samples';

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
    readFile: jest.fn(),
  },
}));

import { resolveAndValidatePath } from '../../utils/paths';
import { runSanyParse, parseSanyOutput } from '../../utils/sany';
import { extractSymbols } from '../../utils/symbols';
import * as jarfile from '../../utils/jarfile';
import * as tlaTools from '../../utils/tla-tools';
import * as fs from 'fs';

describe('SANY Tools - Codex jarfile Validation Fixes', () => {
  let mockServer: ReturnType<typeof createMockMcpServer>;

  beforeEach(() => {
    jest.clearAllMocks();
    mockServer = createMockMcpServer();
    (resolveAndValidatePath as jest.Mock).mockImplementation((p: string) => p);
    (tlaTools.getModuleSearchPaths as jest.Mock).mockReturnValue([]);
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

  // --- REQ-CODEX-005: jarfile: URI JAR path validated against workingDir ---

  describe('REQ-CODEX-005: jarfile JAR path containment', () => {
    // @tests REQ-CODEX-005, SCN-CODEX-005-01
    it('sany_parse: JAR path outside workingDir returns Access denied', async () => {
      const configWithDir = { ...MINIMAL_CONFIG, workingDir: '/workspace' };
      await registerSanyTools(mockServer, configWithDir);

      // resolveAndValidatePath throws for paths outside workingDir
      (resolveAndValidatePath as jest.Mock).mockImplementation((p: string, _wd: string | null) => {
        if (p === '/etc/evil.jar') {
          throw new Error('Access denied: Path /etc/evil.jar is outside the working directory /workspace');
        }
        return p;
      });

      const response = await callRegisteredTool(mockServer, 'tlaplus_mcp_sany_parse', {
        fileName: 'jarfile:/etc/evil.jar!/Module.tla',
      });

      expectMcpTextResponse(response, 'Access denied');
      expect(jarfile.resolveJarfilePath).not.toHaveBeenCalled();
    });

    // @tests REQ-CODEX-005, SCN-CODEX-005-02
    it('sany_symbol: traversal in JAR path returns Access denied', async () => {
      const configWithDir = { ...MINIMAL_CONFIG, workingDir: '/workspace' };
      await registerSanyTools(mockServer, configWithDir);

      (resolveAndValidatePath as jest.Mock).mockImplementation((p: string) => {
        if (p === '../../../etc/evil.jar') {
          throw new Error('Access denied: Path ../../../etc/evil.jar is outside the working directory /workspace');
        }
        return p;
      });

      const response = await callRegisteredTool(mockServer, 'tlaplus_mcp_sany_symbol', {
        fileName: 'jarfile:../../../etc/evil.jar!/Module.tla',
      });

      expectMcpTextResponse(response, 'Access denied');
      expect(jarfile.resolveJarfilePath).not.toHaveBeenCalled();
    });

    // @tests REQ-CODEX-005, SCN-CODEX-005-03
    it('JAR path inside workingDir succeeds normally', async () => {
      const configWithDir = { ...MINIMAL_CONFIG, workingDir: '/workspace' };
      await registerSanyTools(mockServer, configWithDir);

      (resolveAndValidatePath as jest.Mock).mockImplementation((p: string) => {
        // Inside workingDir - no throw
        return p;
      });
      (jarfile.resolveJarfilePath as jest.Mock).mockReturnValue('/tmp/cache/Naturals.tla');
      (fs.existsSync as jest.Mock).mockReturnValue(true);
      const mocks = mockSanySuccess();
      (runSanyParse as jest.Mock).mockImplementation(mocks.runSanyParse);
      (parseSanyOutput as jest.Mock).mockImplementation(mocks.parseSanyOutput);

      const response = await callRegisteredTool(mockServer, 'tlaplus_mcp_sany_parse', {
        fileName: 'jarfile:/workspace/tools/tla2tools.jar!/tla2sany/StandardModules/Naturals.tla',
      });

      expect(jarfile.resolveJarfilePath).toHaveBeenCalled();
      expectMcpTextResponse(response, 'No errors found');
    });

    // @tests REQ-CODEX-005
    // TC-CROSS-002: Both sany_parse and sany_symbol produce same error
    it('both SANY tools produce same error format for jarfile outside workingDir', async () => {
      const configWithDir = { ...MINIMAL_CONFIG, workingDir: '/workspace' };
      await registerSanyTools(mockServer, configWithDir);

      (resolveAndValidatePath as jest.Mock).mockImplementation((p: string) => {
        if (p === '/etc/evil.jar') {
          throw new Error('Access denied: Path /etc/evil.jar is outside the working directory /workspace');
        }
        return p;
      });

      const parseResponse = await callRegisteredTool(mockServer, 'tlaplus_mcp_sany_parse', {
        fileName: 'jarfile:/etc/evil.jar!/Module.tla',
      });

      const symbolResponse = await callRegisteredTool(mockServer, 'tlaplus_mcp_sany_symbol', {
        fileName: 'jarfile:/etc/evil.jar!/Module.tla',
      });

      // Both should start with "Access denied:"
      expect(parseResponse.content[0].text).toContain('Access denied');
      expect(symbolResponse.content[0].text).toContain('Access denied');
    });
  });

  // --- REQ-CODEX-006: Null workingDir skips jarfile validation ---

  describe('REQ-CODEX-006: null workingDir no jarfile validation', () => {
    // @tests REQ-CODEX-006, SCN-CODEX-006-01
    it('null workingDir skips JAR path validation and proceeds', async () => {
      const configNoDir = { ...MINIMAL_CONFIG, workingDir: null };
      await registerSanyTools(mockServer, configNoDir);

      (jarfile.resolveJarfilePath as jest.Mock).mockReturnValue('/tmp/cache/Module.tla');
      (fs.existsSync as jest.Mock).mockReturnValue(true);
      const mocks = mockSanySuccess();
      (runSanyParse as jest.Mock).mockImplementation(mocks.runSanyParse);
      (parseSanyOutput as jest.Mock).mockImplementation(mocks.parseSanyOutput);

      const response = await callRegisteredTool(mockServer, 'tlaplus_mcp_sany_parse', {
        fileName: 'jarfile:/any/path/tools.jar!/Module.tla',
      });

      // resolveAndValidatePath should NOT have been called with the jarPath
      // (it's only called in the else branch for non-jarfile URIs)
      expectMcpTextResponse(response, 'No errors found');
      expect(jarfile.resolveJarfilePath).toHaveBeenCalled();
    });
  });

  // --- Adversarial: TC-SEC-003, TC-SEC-004 ---

  describe('Security: jarfile path traversal/escape', () => {
    // @tests REQ-CODEX-005
    // TC-SEC-003: jarfile traversal
    it('jarfile with relative traversal in JAR path is denied', async () => {
      const configWithDir = { ...MINIMAL_CONFIG, workingDir: '/workspace' };
      await registerSanyTools(mockServer, configWithDir);

      (resolveAndValidatePath as jest.Mock).mockImplementation((p: string) => {
        if (p === '../../../etc/evil.jar') {
          throw new Error('Access denied');
        }
        return p;
      });

      const response = await callRegisteredTool(mockServer, 'tlaplus_mcp_sany_parse', {
        fileName: 'jarfile:../../../etc/evil.jar!/Module.tla',
      });

      expectMcpTextResponse(response, 'Access denied');
    });

    // @tests REQ-CODEX-005
    // TC-SEC-004: absolute jar path escape
    it('jarfile with absolute path outside workingDir is denied', async () => {
      const configWithDir = { ...MINIMAL_CONFIG, workingDir: '/workspace' };
      await registerSanyTools(mockServer, configWithDir);

      (resolveAndValidatePath as jest.Mock).mockImplementation((p: string) => {
        if (p === '/etc/evil.jar') {
          throw new Error('Access denied: Path /etc/evil.jar is outside the working directory /workspace');
        }
        return p;
      });

      const response = await callRegisteredTool(mockServer, 'tlaplus_mcp_sany_parse', {
        fileName: 'jarfile:/etc/evil.jar!/Module.tla',
      });

      expectMcpTextResponse(response, 'Access denied');
    });
  });
});
