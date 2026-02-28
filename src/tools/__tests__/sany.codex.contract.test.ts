// Spec: docs/codex-fixes/spec.md
// Contract: docs/codex-fixes/contract.md (SANY tool handlers)
// Testing: docs/codex-fixes/testing.md
//
// Contract tests for SANY tools jarfile: URI behavior.

import { registerSanyTools } from '../sany';
import { createMockMcpServer, callRegisteredTool } from '../../__tests__/helpers/mock-server';
import { MINIMAL_CONFIG } from '../../__tests__/fixtures/config-samples';
import { mockSanySuccess } from '../../__tests__/helpers/mock-utils';

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
import * as jarfile from '../../utils/jarfile';
import * as tlaTools from '../../utils/tla-tools';
import * as fs from 'fs';

describe('SANY Tools - Contract Tests (Codex jarfile)', () => {
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

  // @tests-contract REQ-CODEX-005
  it('jarfile: URI with JAR outside workingDir returns error response', async () => {
    const configWithDir = { ...MINIMAL_CONFIG, workingDir: '/workspace' };
    await registerSanyTools(mockServer, configWithDir);

    (resolveAndValidatePath as jest.Mock).mockImplementation((p: string) => {
      if (p === '/etc/evil.jar') {
        throw new Error('Access denied');
      }
      return p;
    });

    const response = await callRegisteredTool(mockServer, 'tlaplus_mcp_sany_parse', {
      fileName: 'jarfile:/etc/evil.jar!/Module.tla',
    });

    expect(response.content).toHaveLength(1);
    expect(response.content[0].type).toBe('text');
    expect(response.content[0].text).toContain('Access denied');
  });

  // @tests-contract REQ-CODEX-006
  it('jarfile: URI with null workingDir proceeds without validation error', async () => {
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

    // Contract: no access denied error, tool proceeds
    expect(response.content[0].text).not.toContain('Access denied');
    expect(response.content[0].text).toContain('No errors found');
  });
});
