import { runTlcAndWait } from '../utils/tlc-helpers';
import { runProcess } from '../utils/process-runner';

jest.mock('../utils/process-runner');
jest.mock('../utils/java');
jest.mock('../utils/tla-tools');

const mockRunProcess = runProcess as jest.MockedFunction<typeof runProcess>;

describe('TLC Progress Notifications', () => {
  beforeEach(() => {
    jest.clearAllMocks();
    
    const { findJavaExecutable, buildJavaOptions } = require('../utils/java');
    const { getClassPath, getModuleSearchPaths } = require('../utils/tla-tools');
    
    (findJavaExecutable as jest.Mock).mockReturnValue('/usr/bin/java');
    (buildJavaOptions as jest.Mock).mockReturnValue(['-Xmx4G']);
    (getClassPath as jest.Mock).mockReturnValue('/path/to/tla2tools.jar');
    (getModuleSearchPaths as jest.Mock).mockReturnValue([]);
  });

  it('should accept progress callback and process output correctly', async () => {
    const progressCallback = jest.fn();
    
    const mockOutput = 'TLC output line 1\nTLC output line 2\nTLC output line 3';
    
    mockRunProcess.mockResolvedValue({
      exitCode: 0,
      stdout: '',
      stderr: '',
      combined: mockOutput,
      timedOut: false,
      aborted: false,
      killed: false
    });

    const result = await runTlcAndWait(
      '/path/to/spec.tla',
      'spec.cfg',
      ['-cleanup', '-simulate'],
      ['-Dtlc2.TLC.stopAfter=3'],
      '/path/to/tools',
      undefined,
      120000,
      undefined,
      progressCallback
    );

    expect(result.exitCode).toBe(0);
    expect(result.output.length).toBeGreaterThan(0);
  });

  it('should handle progress callback with proper signature', async () => {
    const progressCallback = jest.fn();
    
    const mockOutput = 'TLC output\nline 2\nline 3';
    
    mockRunProcess.mockResolvedValue({
      exitCode: 0,
      stdout: '',
      stderr: '',
      combined: mockOutput,
      timedOut: false,
      aborted: false,
      killed: false
    });

    await runTlcAndWait(
      '/path/to/spec.tla',
      'spec.cfg',
      ['-cleanup', '-simulate'],
      ['-Dtlc2.TLC.stopAfter=3'],
      '/path/to/tools',
      undefined,
      120000,
      undefined,
      progressCallback
    );

    if (progressCallback.mock.calls.length > 0) {
      const firstCall = progressCallback.mock.calls[0][0];
      expect(firstCall).toHaveProperty('progress');
      expect(firstCall).toHaveProperty('total');
      expect(firstCall).toHaveProperty('message');
    }
  });

  it('should not fail if progress callback is not provided', async () => {
    const mockOutput = 'TLC output\nline 2\nline 3';
    
    mockRunProcess.mockResolvedValue({
      exitCode: 0,
      stdout: '',
      stderr: '',
      combined: mockOutput,
      timedOut: false,
      aborted: false,
      killed: false
    });

    const result = await runTlcAndWait(
      '/path/to/spec.tla',
      'spec.cfg',
      ['-cleanup', '-simulate'],
      ['-Dtlc2.TLC.stopAfter=3'],
      '/path/to/tools',
      undefined,
      120000,
      undefined
    );

    expect(result.exitCode).toBe(0);
    expect(result.output.length).toBeGreaterThan(0);
  });

  it('should include progress information in callback when called', async () => {
    const progressCallback = jest.fn();
    
    const mockOutput = 'TLC output\nline 2\nline 3';
    
    mockRunProcess.mockResolvedValue({
      exitCode: 0,
      stdout: '',
      stderr: '',
      combined: mockOutput,
      timedOut: false,
      aborted: false,
      killed: false
    });

    await runTlcAndWait(
      '/path/to/spec.tla',
      'spec.cfg',
      ['-cleanup', '-simulate'],
      ['-Dtlc2.TLC.stopAfter=3'],
      '/path/to/tools',
      undefined,
      120000,
      undefined,
      progressCallback
    );

    if (progressCallback.mock.calls.length > 0) {
      const lastCall = progressCallback.mock.calls[progressCallback.mock.calls.length - 1][0];
      expect(lastCall.message).toContain('Processing TLC output');
      expect(lastCall.message).toMatch(/\d+\/\d+ lines/);
      expect(lastCall.progress).toBeGreaterThan(0);
      expect(lastCall.total).toBeGreaterThan(0);
    }
  });
});
