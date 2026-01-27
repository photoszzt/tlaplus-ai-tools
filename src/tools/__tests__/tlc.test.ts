import { registerTlcTools } from '../tlc';
import { createMockMcpServer, callRegisteredTool } from '../../__tests__/helpers/mock-server';
import { expectMcpTextResponse, expectMcpErrorResponse, expectToolRegistered } from '../../__tests__/helpers/assertions';
import { mockTlcSuccess, mockTlcNoConfig, mockTlcError, mockFsExists } from '../../__tests__/helpers/mock-utils';
import { MINIMAL_CONFIG, NO_TOOLS_CONFIG } from '../../__tests__/fixtures/config-samples';
import { TLC_SUCCESS_OUTPUT, TLC_VIOLATION_OUTPUT } from '../../__tests__/fixtures/sample-modules';

// Mock dependencies
jest.mock('../../utils/paths');
jest.mock('../../utils/tlc-helpers');
jest.mock('fs');

import { resolveAndValidatePath } from '../../utils/paths';
import { getSpecFiles, runTlcAndWait } from '../../utils/tlc-helpers';
import * as fs from 'fs';

describe('TLC Tools', () => {
  let mockServer: ReturnType<typeof createMockMcpServer>;

  beforeEach(() => {
    jest.clearAllMocks();
    mockServer = createMockMcpServer();
    (resolveAndValidatePath as jest.Mock).mockImplementation((path) => path);
  });

  describe('Tool Registration', () => {
    it('registers all three TLC tools', async () => {
      await registerTlcTools(mockServer, MINIMAL_CONFIG);

      expectToolRegistered(mockServer, 'tlaplus_mcp_tlc_check');
      expectToolRegistered(mockServer, 'tlaplus_mcp_tlc_smoke');
      expectToolRegistered(mockServer, 'tlaplus_mcp_tlc_explore');

      expect(mockServer.tool).toHaveBeenCalledTimes(3);
    });
  });

  describe('tlaplus_mcp_tlc_check', () => {
    beforeEach(async () => {
      await registerTlcTools(mockServer, MINIMAL_CONFIG);
    });

    it('runs model check with default config', async () => {
      (fs.existsSync as jest.Mock).mockReturnValue(true);
      const mocks = mockTlcSuccess(TLC_SUCCESS_OUTPUT, 0);
      (getSpecFiles as jest.Mock).mockImplementation(mocks.getSpecFiles);
      (runTlcAndWait as jest.Mock).mockImplementation(mocks.runTlcAndWait);

      const response = await callRegisteredTool(mockServer, 'tlaplus_mcp_tlc_check', {
        fileName: '/mock/spec.tla'
      });

      expectMcpTextResponse(response, 'Model check completed');
      expectMcpTextResponse(response, 'exit code 0');
      expectMcpTextResponse(response, 'No error has been found');

      expect(runTlcAndWait).toHaveBeenCalledWith(
        '/mock/spec.tla',
        'spec.cfg',
        ['-cleanup', '-modelcheck'],
        [],
        MINIMAL_CONFIG.toolsDir,
        undefined
      );
    });

    it('handles violations in model check', async () => {
      (fs.existsSync as jest.Mock).mockReturnValue(true);
      const mocks = mockTlcSuccess(TLC_VIOLATION_OUTPUT, 12);
      (getSpecFiles as jest.Mock).mockImplementation(mocks.getSpecFiles);
      (runTlcAndWait as jest.Mock).mockImplementation(mocks.runTlcAndWait);

      const response = await callRegisteredTool(mockServer, 'tlaplus_mcp_tlc_check', {
        fileName: '/mock/spec.tla'
      });

      expectMcpTextResponse(response, 'exit code 12');
      expectMcpTextResponse(response, 'Invariant Inv is violated');
    });

    it('returns error for missing file', async () => {
      (fs.existsSync as jest.Mock).mockReturnValue(false);

      const response = await callRegisteredTool(mockServer, 'tlaplus_mcp_tlc_check', {
        fileName: '/mock/missing.tla'
      });

      expectMcpErrorResponse(response, 'does not exist');
    });

    it('returns error when tools directory not configured', async () => {
      await registerTlcTools(mockServer, NO_TOOLS_CONFIG);
      (fs.existsSync as jest.Mock).mockReturnValue(true);

      const response = await callRegisteredTool(mockServer, 'tlaplus_mcp_tlc_check', {
        fileName: '/mock/spec.tla'
      });

      expectMcpErrorResponse(response, 'tools directory not configured');
    });

    it('returns error when no config file found', async () => {
      (fs.existsSync as jest.Mock).mockReturnValue(true);
      const mocks = mockTlcNoConfig();
      (getSpecFiles as jest.Mock).mockImplementation(mocks.getSpecFiles);

      const response = await callRegisteredTool(mockServer, 'tlaplus_mcp_tlc_check', {
        fileName: '/mock/spec.tla'
      });

      expectMcpErrorResponse(response, 'No spec.cfg or MCspec.tla/MCspec.cfg files found');
      expectMcpErrorResponse(response, 'Please create an MCspec.tla and MCspec.cfg file');
    });

    it('uses custom config file when provided', async () => {
      (fs.existsSync as jest.Mock).mockReturnValue(true);
      const mocks = mockTlcSuccess(TLC_SUCCESS_OUTPUT, 0);
      (getSpecFiles as jest.Mock).mockImplementation(mocks.getSpecFiles);
      (runTlcAndWait as jest.Mock).mockImplementation(mocks.runTlcAndWait);

      await callRegisteredTool(mockServer, 'tlaplus_mcp_tlc_check', {
        fileName: '/mock/spec.tla',
        cfgFile: '/mock/custom.cfg'
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

    it('passes extraOpts to TLC', async () => {
      (fs.existsSync as jest.Mock).mockReturnValue(true);
      const mocks = mockTlcSuccess(TLC_SUCCESS_OUTPUT, 0);
      (getSpecFiles as jest.Mock).mockImplementation(mocks.getSpecFiles);
      (runTlcAndWait as jest.Mock).mockImplementation(mocks.runTlcAndWait);

      await callRegisteredTool(mockServer, 'tlaplus_mcp_tlc_check', {
        fileName: '/mock/spec.tla',
        extraOpts: ['-workers', '4']
      });

      expect(runTlcAndWait).toHaveBeenCalledWith(
        '/mock/spec.tla',
        'spec.cfg',
        ['-cleanup', '-modelcheck', '-workers', '4'],
        [],
        MINIMAL_CONFIG.toolsDir,
        undefined
      );
    });

    it('passes extraJavaOpts to TLC', async () => {
      (fs.existsSync as jest.Mock).mockReturnValue(true);
      const mocks = mockTlcSuccess(TLC_SUCCESS_OUTPUT, 0);
      (getSpecFiles as jest.Mock).mockImplementation(mocks.getSpecFiles);
      (runTlcAndWait as jest.Mock).mockImplementation(mocks.runTlcAndWait);

      await callRegisteredTool(mockServer, 'tlaplus_mcp_tlc_check', {
        fileName: '/mock/spec.tla',
        extraJavaOpts: ['-Xmx4G']
      });

      expect(runTlcAndWait).toHaveBeenCalledWith(
        '/mock/spec.tla',
        'spec.cfg',
        ['-cleanup', '-modelcheck'],
        ['-Xmx4G'],
        MINIMAL_CONFIG.toolsDir,
        undefined
      );
    });

    it('handles TLC execution errors', async () => {
      (fs.existsSync as jest.Mock).mockReturnValue(true);
      const mocks = mockTlcError('Java heap space');
      (getSpecFiles as jest.Mock).mockImplementation(mocks.getSpecFiles);
      (runTlcAndWait as jest.Mock).mockImplementation(mocks.runTlcAndWait);

      const response = await callRegisteredTool(mockServer, 'tlaplus_mcp_tlc_check', {
        fileName: '/mock/spec.tla'
      });

      expectMcpErrorResponse(response, 'Error [FILE_IO_ERROR]');
      expectMcpErrorResponse(response, 'Java heap space');
      expectMcpErrorResponse(response, 'Suggested Actions:');
    });
  });

  describe('tlaplus_mcp_tlc_smoke', () => {
    beforeEach(async () => {
      await registerTlcTools(mockServer, MINIMAL_CONFIG);
    });

    it('runs smoke test with simulation mode', async () => {
      (fs.existsSync as jest.Mock).mockReturnValue(true);
      const mocks = mockTlcSuccess(['TLC2 Version 2.18', 'Running Random Simulation...', 'Generated 100 states'], 0);
      (getSpecFiles as jest.Mock).mockImplementation(mocks.getSpecFiles);
      (runTlcAndWait as jest.Mock).mockImplementation(mocks.runTlcAndWait);

      const response = await callRegisteredTool(mockServer, 'tlaplus_mcp_tlc_smoke', {
        fileName: '/mock/spec.tla'
      });

      expectMcpTextResponse(response, 'Smoke test completed');
      expectMcpTextResponse(response, 'Random Simulation');

      expect(runTlcAndWait).toHaveBeenCalledWith(
        '/mock/spec.tla',
        'spec.cfg',
        ['-cleanup', '-simulate'],
        ['-Dtlc2.TLC.stopAfter=3'],
        MINIMAL_CONFIG.toolsDir,
        undefined
      );
    });

    it('includes stopAfter Java option by default', async () => {
      (fs.existsSync as jest.Mock).mockReturnValue(true);
      const mocks = mockTlcSuccess([], 0);
      (getSpecFiles as jest.Mock).mockImplementation(mocks.getSpecFiles);
      (runTlcAndWait as jest.Mock).mockImplementation(mocks.runTlcAndWait);

      await callRegisteredTool(mockServer, 'tlaplus_mcp_tlc_smoke', {
        fileName: '/mock/spec.tla'
      });

      expect(runTlcAndWait).toHaveBeenCalledWith(
        '/mock/spec.tla',
        'spec.cfg',
        ['-cleanup', '-simulate'],
        ['-Dtlc2.TLC.stopAfter=3'],
        MINIMAL_CONFIG.toolsDir,
        undefined
      );
    });

    it('merges extraJavaOpts with stopAfter', async () => {
      (fs.existsSync as jest.Mock).mockReturnValue(true);
      const mocks = mockTlcSuccess([], 0);
      (getSpecFiles as jest.Mock).mockImplementation(mocks.getSpecFiles);
      (runTlcAndWait as jest.Mock).mockImplementation(mocks.runTlcAndWait);

      await callRegisteredTool(mockServer, 'tlaplus_mcp_tlc_smoke', {
        fileName: '/mock/spec.tla',
        extraJavaOpts: ['-Xmx2G']
      });

      expect(runTlcAndWait).toHaveBeenCalledWith(
        '/mock/spec.tla',
        'spec.cfg',
        ['-cleanup', '-simulate'],
        ['-Dtlc2.TLC.stopAfter=3', '-Xmx2G'],
        MINIMAL_CONFIG.toolsDir,
        undefined
      );
    });

    it('returns error when no config found', async () => {
      (fs.existsSync as jest.Mock).mockReturnValue(true);
      const mocks = mockTlcNoConfig();
      (getSpecFiles as jest.Mock).mockImplementation(mocks.getSpecFiles);

      const response = await callRegisteredTool(mockServer, 'tlaplus_mcp_tlc_smoke', {
        fileName: '/mock/spec.tla'
      });

      expectMcpErrorResponse(response, 'No spec.cfg or MCspec.tla/MCspec.cfg files found');
    });
  });

  describe('tlaplus_mcp_tlc_explore', () => {
    beforeEach(async () => {
      await registerTlcTools(mockServer, MINIMAL_CONFIG);
    });

    it('explores behaviors with specified length', async () => {
      (fs.existsSync as jest.Mock).mockReturnValue(true);
      const mocks = mockTlcSuccess(['State 1:', '/\\ x = 0', 'State 2:', '/\\ x = 1'], 0);
      (getSpecFiles as jest.Mock).mockImplementation(mocks.getSpecFiles);
      (runTlcAndWait as jest.Mock).mockImplementation(mocks.runTlcAndWait);

      const response = await callRegisteredTool(mockServer, 'tlaplus_mcp_tlc_explore', {
        fileName: '/mock/spec.tla',
        behaviorLength: 5
      });

      expectMcpTextResponse(response, 'Behavior exploration completed');
      expectMcpTextResponse(response, 'State 1');

      expect(runTlcAndWait).toHaveBeenCalledWith(
        '/mock/spec.tla',
        'spec.cfg',
        ['-cleanup', '-simulate', '-invlevel', '5'],
        ['-Dtlc2.TLC.stopAfter=3'],
        MINIMAL_CONFIG.toolsDir,
        undefined
      );
    });

    it('passes behaviorLength as string to -invlevel', async () => {
      (fs.existsSync as jest.Mock).mockReturnValue(true);
      const mocks = mockTlcSuccess([], 0);
      (getSpecFiles as jest.Mock).mockImplementation(mocks.getSpecFiles);
      (runTlcAndWait as jest.Mock).mockImplementation(mocks.runTlcAndWait);

      await callRegisteredTool(mockServer, 'tlaplus_mcp_tlc_explore', {
        fileName: '/mock/spec.tla',
        behaviorLength: 10
      });

      expect(runTlcAndWait).toHaveBeenCalledWith(
        '/mock/spec.tla',
        'spec.cfg',
        ['-cleanup', '-simulate', '-invlevel', '10'],
        ['-Dtlc2.TLC.stopAfter=3'],
        MINIMAL_CONFIG.toolsDir,
        undefined
      );
    });

    it('supports custom config file', async () => {
      (fs.existsSync as jest.Mock).mockReturnValue(true);
      const mocks = mockTlcSuccess([], 0);
      (getSpecFiles as jest.Mock).mockImplementation(mocks.getSpecFiles);
      (runTlcAndWait as jest.Mock).mockImplementation(mocks.runTlcAndWait);

      await callRegisteredTool(mockServer, 'tlaplus_mcp_tlc_explore', {
        fileName: '/mock/spec.tla',
        behaviorLength: 5,
        cfgFile: '/mock/custom.cfg'
      });

      expect(runTlcAndWait).toHaveBeenCalledWith(
        '/mock/spec.tla',
        'custom.cfg',
        ['-cleanup', '-simulate', '-invlevel', '5'],
        ['-Dtlc2.TLC.stopAfter=3'],
        MINIMAL_CONFIG.toolsDir,
        undefined
      );
    });

    it('handles exploration errors', async () => {
      (fs.existsSync as jest.Mock).mockReturnValue(true);
      const mocks = mockTlcError('Invalid configuration');
      (getSpecFiles as jest.Mock).mockImplementation(mocks.getSpecFiles);
      (runTlcAndWait as jest.Mock).mockImplementation(mocks.runTlcAndWait);

      const response = await callRegisteredTool(mockServer, 'tlaplus_mcp_tlc_explore', {
        fileName: '/mock/spec.tla',
        behaviorLength: 5
      });

      expectMcpErrorResponse(response, 'Error [FILE_IO_ERROR]');
      expectMcpErrorResponse(response, 'Invalid configuration');
      expectMcpErrorResponse(response, 'Suggested Actions:');
    });
  });
});
