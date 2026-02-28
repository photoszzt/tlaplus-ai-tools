// Spec: docs/codex-fixes/spec.md
// Contract: docs/codex-fixes/contract.md (TLC tool handlers)
// Testing: docs/codex-fixes/testing.md
//
// Contract tests for TLC tools cfgFile behavior.
// These tests exercise the PUBLIC MCP tool API as documented.

import { registerTlcTools } from '../tlc';
import { createMockMcpServer, callRegisteredTool } from '../../__tests__/helpers/mock-server';
import { MINIMAL_CONFIG } from '../../__tests__/fixtures/config-samples';
import { TLC_SUCCESS_OUTPUT } from '../../__tests__/fixtures/sample-modules';

// Mock dependencies (minimum needed to exercise the tool handler)
jest.mock('../../utils/paths');
jest.mock('../../utils/tlc-helpers');
jest.mock('fs');

import { resolveAndValidatePath } from '../../utils/paths';
import { getSpecFiles, runTlcAndWait } from '../../utils/tlc-helpers';
import * as fs from 'fs';

describe('TLC Tools - Contract Tests (Codex cfgFile)', () => {
  let mockServer: ReturnType<typeof createMockMcpServer>;

  beforeEach(() => {
    jest.clearAllMocks();
    mockServer = createMockMcpServer();
    (resolveAndValidatePath as jest.Mock).mockImplementation((p: string) => p);
  });

  async function setupTools() {
    await registerTlcTools(mockServer, MINIMAL_CONFIG);
    (getSpecFiles as jest.Mock).mockResolvedValue({
      tlaFilePath: '/mock/spec.tla',
      cfgFilePath: '/mock/spec.cfg',
    });
    (runTlcAndWait as jest.Mock).mockResolvedValue({
      exitCode: 0,
      output: TLC_SUCCESS_OUTPUT,
    });
  }

  // @tests-contract REQ-CODEX-001
  it('missing cfgFile returns error response with resolved path', async () => {
    await setupTools();
    (fs.existsSync as jest.Mock).mockImplementation((p: string) => {
      if (p === '/tmp/nonexistent.cfg') return false;
      return true;
    });

    const response = await callRegisteredTool(mockServer, 'tlaplus_mcp_tlc_check', {
      fileName: '/mock/spec.tla',
      cfgFile: '/tmp/nonexistent.cfg',
    });

    // Contract: response has content array with text type
    expect(response.content).toHaveLength(1);
    expect(response.content[0].type).toBe('text');
    expect(response.content[0].text).toContain('/tmp/nonexistent.cfg');
    expect(response.content[0].text).toContain('does not exist');
  });

  // @tests-contract REQ-CODEX-001
  it('response has no isError field for missing cfgFile', async () => {
    await setupTools();
    (fs.existsSync as jest.Mock).mockImplementation((p: string) => {
      if (p === '/tmp/missing.cfg') return false;
      return true;
    });

    const response = await callRegisteredTool(mockServer, 'tlaplus_mcp_tlc_check', {
      fileName: '/mock/spec.tla',
      cfgFile: '/tmp/missing.cfg',
    });

    expect(response).not.toHaveProperty('isError');
  });

  // @tests-contract REQ-CODEX-002
  it('existing cfgFile is used as config (tool proceeds)', async () => {
    await setupTools();
    (fs.existsSync as jest.Mock).mockReturnValue(true);

    const response = await callRegisteredTool(mockServer, 'tlaplus_mcp_tlc_check', {
      fileName: '/mock/spec.tla',
      cfgFile: '/workspace/custom.cfg',
    });

    // Contract: tool proceeds without error when cfgFile exists
    expect(response.content[0].text).toContain('Model check completed');
    expect(response.content[0].text).not.toContain('does not exist');
  });
});
