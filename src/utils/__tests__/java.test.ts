import * as path from 'path';
import { EventEmitter } from 'events';

const mockSpawn = jest.fn();
const mockExecSync = jest.fn();
const mockExistsSync = jest.fn();

jest.mock('child_process', () => ({
  spawn: (...args: unknown[]) => mockSpawn(...args),
  execSync: (...args: unknown[]) => mockExecSync(...args)
}));

jest.mock('fs', () => ({
  existsSync: (...args: unknown[]) => mockExistsSync(...args)
}));

import { findJavaExecutable, buildJavaOptions, runJavaCommand } from '../java';

class MockChildProcess extends EventEmitter {
  pid = 12345;
  stdout = new EventEmitter();
  stderr = new EventEmitter();
  exitCode: number | null = null;
  killed = false;

  kill(signal?: string) {
    this.killed = true;
    return true;
  }
}

describe('java', () => {
  const originalPlatform = process.platform;
  const originalArch = process.arch;
  const originalEnv = { ...process.env };

  beforeEach(() => {
    mockSpawn.mockReset();
    mockExecSync.mockReset();
    mockExistsSync.mockReset();

    Object.defineProperty(process, 'platform', { value: originalPlatform, configurable: true });
    Object.defineProperty(process, 'arch', { value: originalArch, configurable: true });
    process.env = { ...originalEnv };
  });

  afterEach(() => {
    Object.defineProperty(process, 'platform', { value: originalPlatform, configurable: true });
    Object.defineProperty(process, 'arch', { value: originalArch, configurable: true });
    process.env = originalEnv;
  });

  describe('findJavaExecutable', () => {
    it('finds java in provided javaHome on Unix', () => {
      Object.defineProperty(process, 'platform', { value: 'linux', configurable: true });
      mockExistsSync.mockReturnValue(true);

      const result = findJavaExecutable('/usr/lib/jvm/java-17');
      expect(result).toBe(path.join('/usr/lib/jvm/java-17', 'bin', 'java'));
    });

    it('finds java.exe in provided javaHome on Windows', () => {
      Object.defineProperty(process, 'platform', { value: 'win32', configurable: true });
      mockExistsSync.mockReturnValue(true);

      const javaHome = 'C:\\Program Files\\Java\\jdk-17';
      const result = findJavaExecutable(javaHome);
      expect(result).toContain(javaHome);
      expect(result).toContain('bin');
    });

    it('throws error when java not found in provided javaHome', () => {
      mockExistsSync.mockReturnValue(false);

      expect(() => findJavaExecutable('/invalid/java/home'))
        .toThrow('Java executable not found');
    });

    it('uses JAVA_HOME when no javaHome provided', () => {
      process.env.JAVA_HOME = '/env/java/home';
      mockExistsSync.mockReturnValue(true);

      const result = findJavaExecutable();
      expect(result).toContain('/env/java/home');
    });

    it('prioritizes ARM64 environment variables on Apple Silicon', () => {
      Object.defineProperty(process, 'platform', { value: 'darwin', configurable: true });
      Object.defineProperty(process, 'arch', { value: 'arm64', configurable: true });

      process.env.JAVA_HOME_17_ARM64 = '/opt/homebrew/java/17-arm64';
      process.env.JAVA_HOME_17_X64 = '/usr/local/java/17-x64';
      process.env.JAVA_HOME = '/default/java';

      mockExistsSync.mockReturnValue(true);

      const result = findJavaExecutable();
      expect(result).toBe(path.join('/opt/homebrew/java/17-arm64', 'bin', 'java'));
    });

    it('uses JDK_HOME as fallback', () => {
      delete process.env.JAVA_HOME;
      process.env.JDK_HOME = '/jdk/home';
      mockExistsSync.mockReturnValue(true);

      const result = findJavaExecutable();
      expect(result).toContain('/jdk/home');
    });

    it('falls back to java command when no JAVA_HOME', () => {
      delete process.env.JAVA_HOME;
      delete process.env.JDK_HOME;
      mockExistsSync.mockReturnValue(false);

      const result = findJavaExecutable();
      expect(result).toMatch(/^java(\.exe)?$/);
    });

    it('deduplicates environment variables with same value', () => {
      process.env.JAVA_HOME = '/same/path';
      process.env.JDK_HOME = '/same/path';
      mockExistsSync.mockReturnValueOnce(true);

      const result = findJavaExecutable();
      expect(result).toContain('/same/path');
      expect(mockExistsSync).toHaveBeenCalledTimes(1);
    });
  });

  describe('buildJavaOptions', () => {
    it('builds classpath with jarPath', () => {
      const result = buildJavaOptions([], '/path/to/tool.jar');
      expect(result).toContain('-cp');
      expect(result).toContain('/path/to/tool.jar');
    });

    it('includes custom java options', () => {
      const result = buildJavaOptions(['-Xmx4g', '-Xms1g'], '/path/to/tool.jar');
      expect(result).toContain('-Xmx4g');
      expect(result).toContain('-Xms1g');
    });

    it('adds default GC option when none provided', () => {
      const result = buildJavaOptions([], '/path/to/tool.jar');
      expect(result).toContain('-XX:+UseParallelGC');
    });

    it('does not add default GC when custom GC provided', () => {
      const result = buildJavaOptions(['-XX:+UseG1GC'], '/path/to/tool.jar');
      expect(result).toContain('-XX:+UseG1GC');
      expect(result).not.toContain('-XX:+UseParallelGC');
    });

    it('merges custom classpath with default', () => {
      const result = buildJavaOptions(['-cp', '/custom/lib.jar'], '/default/tool.jar');
      expect(result).toContain('-cp');
      const cpIndex = result.indexOf('-cp');
      const classpath = result[cpIndex + 1];
      expect(classpath).toContain('/custom/lib.jar');
      expect(classpath).toContain('/default/tool.jar');
    });

    it('preserves classpath if it already contains tla2tools.jar', () => {
      const result = buildJavaOptions(['-cp', '/my/tla2tools.jar'], '/other/path/tla2tools.jar');
      const cpIndex = result.indexOf('-cp');
      const classpath = result[cpIndex + 1];
      expect(classpath).toBe('/my/tla2tools.jar');
    });

    it('handles -classpath option same as -cp', () => {
      const result = buildJavaOptions(['-classpath', '/custom/lib.jar'], '/default/tool.jar');
      const cpIndex = result.indexOf('-classpath');
      const classpath = result[cpIndex + 1];
      expect(classpath).toContain('/custom/lib.jar');
      expect(classpath).toContain('/default/tool.jar');
    });
  });

  describe('runJavaCommand', () => {
    function createMockProcess() {
      const proc = new MockChildProcess();
      (proc.stdout as EventEmitter & { pipe: jest.Mock }).pipe = jest.fn().mockReturnThis();
      (proc.stderr as EventEmitter & { pipe: jest.Mock }).pipe = jest.fn().mockReturnThis();
      return proc;
    }

    it('spawns java process with correct arguments', async () => {
      mockExistsSync.mockReturnValue(true);
      process.env.JAVA_HOME = '/test/java';

      const mockProc = createMockProcess();
      mockSpawn.mockReturnValue(mockProc);

      const promise = runJavaCommand('/path/to/tool.jar', 'tla2sany.SANY', ['Module.tla']);
      setImmediate(() => mockProc.emit('spawn'));
      const result = await promise;

      expect(mockSpawn).toHaveBeenCalled();
      expect(result.process).toBe(mockProc);
    });

    it('uses shell and windowsHide on Windows', async () => {
      Object.defineProperty(process, 'platform', { value: 'win32', configurable: true });
      mockExistsSync.mockReturnValue(true);
      process.env.JAVA_HOME = '/test/java';

      const mockProc = createMockProcess();
      mockSpawn.mockReturnValue(mockProc);

      const promise = runJavaCommand('/path/to/tool.jar', 'MainClass', []);
      setImmediate(() => mockProc.emit('spawn'));
      await promise;

      expect(mockSpawn).toHaveBeenCalledWith(
        expect.any(String),
        expect.any(Array),
        expect.objectContaining({
          shell: true,
          windowsHide: true
        })
      );
    });

    it('does not use shell on Unix', async () => {
      Object.defineProperty(process, 'platform', { value: 'linux', configurable: true });
      mockExistsSync.mockReturnValue(true);
      process.env.JAVA_HOME = '/test/java';

      const mockProc = createMockProcess();
      mockSpawn.mockReturnValue(mockProc);

      const promise = runJavaCommand('/path/to/tool.jar', 'MainClass', []);
      setImmediate(() => mockProc.emit('spawn'));
      await promise;

      const [, , options] = mockSpawn.mock.calls[0];
      expect(options.shell).toBeUndefined();
    });

    it('provides cross-platform kill function', async () => {
      mockExistsSync.mockReturnValue(true);
      process.env.JAVA_HOME = '/test/java';

      const mockProc = createMockProcess();
      mockSpawn.mockReturnValue(mockProc);

      const promise = runJavaCommand('/path/to/tool.jar', 'MainClass', []);
      setImmediate(() => mockProc.emit('spawn'));
      const result = await promise;

      expect(result.kill).toBeDefined();
      expect(typeof result.kill).toBe('function');
    });

    it('uses taskkill on Windows', async () => {
      Object.defineProperty(process, 'platform', { value: 'win32', configurable: true });
      mockExistsSync.mockReturnValue(true);
      process.env.JAVA_HOME = '/test/java';

      const mockProc = createMockProcess();
      mockSpawn.mockReturnValue(mockProc);

      const promise = runJavaCommand('/path/to/tool.jar', 'MainClass', []);
      setImmediate(() => mockProc.emit('spawn'));
      const result = await promise;

      result.kill!();

      expect(mockExecSync).toHaveBeenCalledWith(
        expect.stringContaining('taskkill'),
        expect.any(Object)
      );
    });

    it('falls back to SIGKILL on Windows when taskkill fails', async () => {
      Object.defineProperty(process, 'platform', { value: 'win32', configurable: true });
      mockExistsSync.mockReturnValue(true);
      process.env.JAVA_HOME = '/test/java';
      mockExecSync.mockImplementation(() => { throw new Error('taskkill failed'); });

      const mockProc = createMockProcess();
      mockSpawn.mockReturnValue(mockProc);

      const promise = runJavaCommand('/path/to/tool.jar', 'MainClass', []);
      setImmediate(() => mockProc.emit('spawn'));
      const result = await promise;

      result.kill!();

      expect(mockProc.killed).toBe(true);
    });

    it('uses SIGTERM on Unix', async () => {
      Object.defineProperty(process, 'platform', { value: 'linux', configurable: true });
      mockExistsSync.mockReturnValue(true);
      process.env.JAVA_HOME = '/test/java';

      const mockProc = createMockProcess();
      const killSpy = jest.spyOn(mockProc, 'kill');
      mockSpawn.mockReturnValue(mockProc);

      const promise = runJavaCommand('/path/to/tool.jar', 'MainClass', []);
      setImmediate(() => mockProc.emit('spawn'));
      const result = await promise;

      result.kill!();

      expect(killSpy).toHaveBeenCalledWith('SIGTERM');
    });

    it('rejects when spawn fails with retry', async () => {
      mockExistsSync.mockReturnValue(true);
      process.env.JAVA_HOME = '/test/java';

      // Mock spawn to emit error for every attempt
      mockSpawn.mockImplementation(() => {
        const mockProc = createMockProcess();
        setImmediate(() => mockProc.emit('error', new Error('spawn failed')));
        return mockProc;
      });

      const promise = runJavaCommand('/path/to/tool.jar', 'MainClass', []);

      await expect(promise).rejects.toThrow('Failed to launch Java process');
    }, 20000); // Increase timeout to allow for retries (100ms + 1s + 10s)

    it('handles process that already exited before spawn event', async () => {
      mockExistsSync.mockReturnValue(true);
      process.env.JAVA_HOME = '/test/java';

      const mockProc = createMockProcess();
      mockProc.exitCode = 0;
      mockSpawn.mockReturnValue(mockProc);

      const promise = runJavaCommand('/path/to/tool.jar', 'MainClass', []);
      setImmediate(() => mockProc.emit('spawn'));
      const result = await promise;

      expect(result.process).toBe(mockProc);
    });

    it('passes workingDir to spawn options', async () => {
      mockExistsSync.mockReturnValue(true);
      process.env.JAVA_HOME = '/test/java';

      const mockProc = createMockProcess();
      mockSpawn.mockReturnValue(mockProc);

      const promise = runJavaCommand('/path/to/tool.jar', 'MainClass', [], [], undefined, '/custom/workdir');
      setImmediate(() => mockProc.emit('spawn'));
      await promise;

      const [, , options] = mockSpawn.mock.calls[0];
      expect(options.cwd).toBe('/custom/workdir');
    });

    it('uses process.cwd() when no workingDir specified', async () => {
      mockExistsSync.mockReturnValue(true);
      process.env.JAVA_HOME = '/test/java';

      const mockProc = createMockProcess();
      mockSpawn.mockReturnValue(mockProc);

      const promise = runJavaCommand('/path/to/tool.jar', 'MainClass', []);
      setImmediate(() => mockProc.emit('spawn'));
      await promise;

      const [, , options] = mockSpawn.mock.calls[0];
      expect(options.cwd).toBe(process.cwd());
    });

    it('clears timeout when process exits', async () => {
      jest.useFakeTimers();
      mockExistsSync.mockReturnValue(true);
      process.env.JAVA_HOME = '/test/java';

      const mockProc = createMockProcess();
      mockSpawn.mockReturnValue(mockProc);

      const promise = runJavaCommand('/path/to/tool.jar', 'MainClass', [], [], undefined, undefined, 5000);
      
      setImmediate(() => {
        mockProc.emit('spawn');
        mockProc.emit('exit', 0);
      });

      jest.runAllTimers();

      await promise;
      jest.useRealTimers();
    });

    it('includes javaOpts in command', async () => {
      mockExistsSync.mockReturnValue(true);
      process.env.JAVA_HOME = '/test/java';

      const mockProc = createMockProcess();
      mockSpawn.mockReturnValue(mockProc);

      const promise = runJavaCommand('/path/to/tool.jar', 'MainClass', ['arg1'], ['-Xmx2g']);
      setImmediate(() => mockProc.emit('spawn'));
      await promise;

      const [, args] = mockSpawn.mock.calls[0];
      expect(args).toContain('-Xmx2g');
    });
  });
});
