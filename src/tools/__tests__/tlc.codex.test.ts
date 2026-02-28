// Spec: docs/codex-fixes/spec.md
// Testing: docs/codex-fixes/testing.md
//
// White-box tests for Finding 1: cfgFile Silent Fallback fixes in TLC tools

import { registerTlcTools } from '../tlc';
import { createMockMcpServer, callRegisteredTool } from '../../__tests__/helpers/mock-server';
import { expectMcpTextResponse, expectMcpErrorResponse } from '../../__tests__/helpers/assertions';
import { mockTlcSuccess, mockTlcNoConfig } from '../../__tests__/helpers/mock-utils';
import { MINIMAL_CONFIG } from '../../__tests__/fixtures/config-samples';
import { TLC_SUCCESS_OUTPUT } from '../../__tests__/fixtures/sample-modules';

// Mock dependencies
jest.mock('../../utils/paths');
jest.mock('../../utils/tlc-helpers');
jest.mock('fs');

import { resolveAndValidatePath } from '../../utils/paths';
import { getSpecFiles, runTlcAndWait } from '../../utils/tlc-helpers';
import * as fs from 'fs';

describe('TLC Tools - Codex cfgFile Fixes', () => {
  let mockServer: ReturnType<typeof createMockMcpServer>;

  beforeEach(() => {
    jest.clearAllMocks();
    mockServer = createMockMcpServer();
    // Default: resolveAndValidatePath returns its input (identity transform)
    (resolveAndValidatePath as jest.Mock).mockImplementation((p: string) => p);
  });

  // Helper: register tools and set up standard mocks for a working spec
  async function setupWithSpec() {
    await registerTlcTools(mockServer, MINIMAL_CONFIG);
    const mocks = mockTlcSuccess(TLC_SUCCESS_OUTPUT, 0);
    (getSpecFiles as jest.Mock).mockImplementation(mocks.getSpecFiles);
    (runTlcAndWait as jest.Mock).mockImplementation(mocks.runTlcAndWait);
  }

  // --- REQ-CODEX-001: Error on Missing Explicit cfgFile ---

  describe('REQ-CODEX-001: cfgFile non-existent returns error', () => {
    // @tests REQ-CODEX-001, SCN-CODEX-001-01
    it('tlaplus_mcp_tlc_check: cfgFile non-existent returns error', async () => {
      await setupWithSpec();
      (fs.existsSync as jest.Mock).mockImplementation((p: string) => {
        if (p === '/mock/spec.tla') return true;        // spec file exists
        if (p === '/tmp/nonexistent.cfg') return false;  // cfgFile does not exist
        return true;
      });

      const response = await callRegisteredTool(mockServer, 'tlaplus_mcp_tlc_check', {
        fileName: '/mock/spec.tla',
        cfgFile: '/tmp/nonexistent.cfg',
      });

      expectMcpTextResponse(response, 'Config file');
      expectMcpTextResponse(response, '/tmp/nonexistent.cfg');
      expectMcpTextResponse(response, 'does not exist on disk');
      expect(runTlcAndWait).not.toHaveBeenCalled();
    });

    // @tests REQ-CODEX-001, SCN-CODEX-001-01
    it('tlaplus_mcp_tlc_smoke: cfgFile non-existent returns error', async () => {
      await setupWithSpec();
      (fs.existsSync as jest.Mock).mockImplementation((p: string) => {
        if (p === '/mock/spec.tla') return true;
        if (p === '/tmp/nonexistent.cfg') return false;
        return true;
      });

      const response = await callRegisteredTool(mockServer, 'tlaplus_mcp_tlc_smoke', {
        fileName: '/mock/spec.tla',
        cfgFile: '/tmp/nonexistent.cfg',
      });

      expectMcpTextResponse(response, 'Config file');
      expectMcpTextResponse(response, 'does not exist on disk');
      expect(runTlcAndWait).not.toHaveBeenCalled();
    });

    // @tests REQ-CODEX-001, SCN-CODEX-001-01
    it('tlaplus_mcp_tlc_explore: cfgFile non-existent returns error', async () => {
      await setupWithSpec();
      (fs.existsSync as jest.Mock).mockImplementation((p: string) => {
        if (p === '/mock/spec.tla') return true;
        if (p === '/tmp/nonexistent.cfg') return false;
        return true;
      });

      const response = await callRegisteredTool(mockServer, 'tlaplus_mcp_tlc_explore', {
        fileName: '/mock/spec.tla',
        behaviorLength: 5,
        cfgFile: '/tmp/nonexistent.cfg',
      });

      expectMcpTextResponse(response, 'Config file');
      expectMcpTextResponse(response, 'does not exist on disk');
      expect(runTlcAndWait).not.toHaveBeenCalled();
    });

    // @tests REQ-CODEX-001, SCN-CODEX-001-01
    it('tlaplus_mcp_tlc_trace: cfgFile non-existent returns error', async () => {
      await setupWithSpec();
      (fs.existsSync as jest.Mock).mockImplementation((p: string) => {
        if (p === '/mock/spec.tla') return true;
        if (p === '/tmp/nonexistent.cfg') return false;
        return true;
      });

      const response = await callRegisteredTool(mockServer, 'tlaplus_mcp_tlc_trace', {
        fileName: '/mock/spec.tla',
        traceFile: '/mock/trace.tlc',
        cfgFile: '/tmp/nonexistent.cfg',
      });

      expectMcpTextResponse(response, 'Config file');
      expectMcpTextResponse(response, 'does not exist on disk');
      expect(runTlcAndWait).not.toHaveBeenCalled();
    });

    // @tests REQ-CODEX-001, SCN-CODEX-001-02
    it('cfgFile relative path is resolved to absolute in error message', async () => {
      const configWithDir = { ...MINIMAL_CONFIG, workingDir: '/workspace' };
      mockServer = createMockMcpServer();
      await registerTlcTools(mockServer, configWithDir);

      const mocks = mockTlcSuccess(TLC_SUCCESS_OUTPUT, 0);
      (getSpecFiles as jest.Mock).mockImplementation(mocks.getSpecFiles);
      (runTlcAndWait as jest.Mock).mockImplementation(mocks.runTlcAndWait);

      // resolveAndValidatePath simulates resolution for relative cfgFile
      (resolveAndValidatePath as jest.Mock).mockImplementation((p: string) => {
        if (p === 'custom/missing.cfg') return '/workspace/custom/missing.cfg';
        return p;
      });

      (fs.existsSync as jest.Mock).mockImplementation((p: string) => {
        if (p === '/mock/spec.tla') return true;
        if (p === '/workspace/custom/missing.cfg') return false;
        return true;
      });

      const response = await callRegisteredTool(mockServer, 'tlaplus_mcp_tlc_check', {
        fileName: '/mock/spec.tla',
        cfgFile: 'custom/missing.cfg',
      });

      expectMcpTextResponse(response, 'Config file /workspace/custom/missing.cfg does not exist on disk.');
    });

    // @tests REQ-CODEX-001, SCN-CODEX-001-03
    it('tlaplus_mcp_tlc_trace: cfgFile error before traceFile error', async () => {
      await setupWithSpec();
      (fs.existsSync as jest.Mock).mockImplementation((p: string) => {
        if (p === '/mock/spec.tla') return true;
        if (p === '/tmp/bad.cfg') return false;
        if (p === '/tmp/bad.tlc') return false;
        return true;
      });

      const response = await callRegisteredTool(mockServer, 'tlaplus_mcp_tlc_trace', {
        fileName: '/mock/spec.tla',
        traceFile: '/tmp/bad.tlc',
        cfgFile: '/tmp/bad.cfg',
      });

      // cfgFile error returned first (not traceFile error)
      expectMcpTextResponse(response, 'Config file');
      expectMcpTextResponse(response, '/tmp/bad.cfg');
      expect(response.content[0].text).not.toContain('Trace file');
    });

    // @tests REQ-CODEX-001
    // TC-CROSS-001: All 4 tools produce same error format
    it('all four TLC tools produce same error format for missing cfgFile', async () => {
      await setupWithSpec();
      const cfgPath = '/tmp/nonexistent.cfg';

      (fs.existsSync as jest.Mock).mockImplementation((p: string) => {
        if (p === cfgPath) return false;
        return true;
      });

      const toolNames = [
        'tlaplus_mcp_tlc_check',
        'tlaplus_mcp_tlc_smoke',
        'tlaplus_mcp_tlc_explore',
        'tlaplus_mcp_tlc_trace',
      ];

      const responses = [];
      for (const tool of toolNames) {
        const args: any = { fileName: '/mock/spec.tla', cfgFile: cfgPath };
        if (tool === 'tlaplus_mcp_tlc_explore') args.behaviorLength = 5;
        if (tool === 'tlaplus_mcp_tlc_trace') args.traceFile = '/mock/trace.tlc';
        responses.push(await callRegisteredTool(mockServer, tool, args));
      }

      const expectedText = `Config file ${cfgPath} does not exist on disk.`;
      for (const response of responses) {
        expect(response.content[0].text).toBe(expectedText);
      }
    });

    // @tests-invariant INV-CODEX-001
    it('error response has no isError field', async () => {
      await setupWithSpec();
      (fs.existsSync as jest.Mock).mockImplementation((p: string) => {
        if (p === '/tmp/nonexistent.cfg') return false;
        return true;
      });

      const response = await callRegisteredTool(mockServer, 'tlaplus_mcp_tlc_check', {
        fileName: '/mock/spec.tla',
        cfgFile: '/tmp/nonexistent.cfg',
      });

      expect(response).not.toHaveProperty('isError');
    });
  });

  // --- REQ-CODEX-002: Existing cfgFile Behavior Preserved ---

  describe('REQ-CODEX-002: existing cfgFile used as config', () => {
    // @tests REQ-CODEX-002, SCN-CODEX-002-01
    it('existing cfgFile overrides auto-detected config', async () => {
      await setupWithSpec();
      (fs.existsSync as jest.Mock).mockReturnValue(true);

      await callRegisteredTool(mockServer, 'tlaplus_mcp_tlc_check', {
        fileName: '/mock/spec.tla',
        cfgFile: '/workspace/custom.cfg',
      });

      expect(runTlcAndWait).toHaveBeenCalledWith(
        '/mock/spec.tla',
        'custom.cfg',
        ['-cleanup', '-modelcheck'],
        [],
        MINIMAL_CONFIG.toolsDir,
        undefined
      );
    });

    // @tests REQ-CODEX-002
    it('no cfgFile uses auto-detected config', async () => {
      await setupWithSpec();
      (fs.existsSync as jest.Mock).mockReturnValue(true);

      await callRegisteredTool(mockServer, 'tlaplus_mcp_tlc_check', {
        fileName: '/mock/spec.tla',
      });

      // Should use spec.cfg (from mockTlcSuccess's getSpecFiles)
      expect(runTlcAndWait).toHaveBeenCalledWith(
        '/mock/spec.tla',
        'spec.cfg',
        ['-cleanup', '-modelcheck'],
        [],
        MINIMAL_CONFIG.toolsDir,
        undefined
      );
    });
  });

  // --- Adversarial: TC-ADV-005 ---

  describe('TC-ADV-005: cfgFile edge cases', () => {
    // @tests REQ-CODEX-001
    it('empty string cfgFile is treated as not provided (falsy)', async () => {
      // In JavaScript, empty string is falsy, so `if (cfgFile)` is false.
      // The tool should proceed with auto-detected config.
      await setupWithSpec();
      (fs.existsSync as jest.Mock).mockReturnValue(true);

      const response = await callRegisteredTool(mockServer, 'tlaplus_mcp_tlc_check', {
        fileName: '/mock/spec.tla',
        cfgFile: '',
      });

      // Empty string cfgFile is falsy -> auto-detected config used -> success
      expectMcpTextResponse(response, 'Model check completed');
    });

    // @tests REQ-CODEX-001
    it('null cfgFile skips cfgFile logic entirely', async () => {
      await setupWithSpec();
      (fs.existsSync as jest.Mock).mockReturnValue(true);

      const response = await callRegisteredTool(mockServer, 'tlaplus_mcp_tlc_check', {
        fileName: '/mock/spec.tla',
        cfgFile: undefined,
      });

      // undefined cfgFile -> auto-detected config used -> success
      expectMcpTextResponse(response, 'Model check completed');
    });
  });

  // --- TC-SEC-006: cfgFile traversal ---

  describe('TC-SEC-006: cfgFile path traversal', () => {
    // @tests REQ-CODEX-001
    it('cfgFile with path traversal is blocked by resolveAndValidatePath', async () => {
      const configWithDir = { ...MINIMAL_CONFIG, workingDir: '/workspace' };
      mockServer = createMockMcpServer();
      await registerTlcTools(mockServer, configWithDir);

      const mocks = mockTlcSuccess(TLC_SUCCESS_OUTPUT, 0);
      (getSpecFiles as jest.Mock).mockImplementation(mocks.getSpecFiles);

      (resolveAndValidatePath as jest.Mock).mockImplementation((p: string) => {
        if (p === '../../etc/malicious.cfg') {
          throw new Error('Access denied: Path ../../etc/malicious.cfg is outside the working directory /workspace');
        }
        return p;
      });
      (fs.existsSync as jest.Mock).mockReturnValue(true);

      const response = await callRegisteredTool(mockServer, 'tlaplus_mcp_tlc_check', {
        fileName: '/workspace/spec.tla',
        cfgFile: '../../etc/malicious.cfg',
      });

      // The error from resolveAndValidatePath is caught by the outer try/catch
      expectMcpErrorResponse(response, 'Access denied');
    });
  });
});
