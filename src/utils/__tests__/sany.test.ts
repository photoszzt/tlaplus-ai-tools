import { Readable, PassThrough } from 'stream';
import { EventEmitter } from 'events';
import * as path from 'path';
import { ProcessInfo } from '../java';
import { parseSanyOutput, SanyParseResult, runSanyParse } from '../sany';

const mockRunJavaCommand = jest.fn();
const mockGetClassPath = jest.fn();
const mockGetModuleSearchPaths = jest.fn();

jest.mock('../java', () => ({
  runJavaCommand: (...args: unknown[]) => mockRunJavaCommand(...args)
}));

jest.mock('../tla-tools', () => ({
  getClassPath: (...args: unknown[]) => mockGetClassPath(...args),
  getModuleSearchPaths: (...args: unknown[]) => mockGetModuleSearchPaths(...args)
}));

function createMockProcessInfo(output: string): ProcessInfo {
  const mergedOutput = new PassThrough();
  const proc = new EventEmitter() as EventEmitter & { exitCode: number | null };
  proc.exitCode = 0;

  setImmediate(() => {
    mergedOutput.write(output);
    mergedOutput.end();
  });

  return {
    process: proc as ProcessInfo['process'],
    stdout: null,
    stderr: null,
    mergedOutput,
    kill: jest.fn()
  };
}

describe('sany', () => {
  const originalPlatform = process.platform;

  beforeEach(() => {
    mockRunJavaCommand.mockReset();
    mockGetClassPath.mockReset();
    mockGetModuleSearchPaths.mockReset();
  });

  afterEach(() => {
    Object.defineProperty(process, 'platform', { value: originalPlatform, configurable: true });
  });

  describe('runSanyParse', () => {
    it('runs SANY with correct arguments', async () => {
      const mockProc = createMockProcessInfo('');
      mockRunJavaCommand.mockResolvedValue(mockProc);
      mockGetClassPath.mockReturnValue('/tools/tla2tools.jar');
      mockGetModuleSearchPaths.mockReturnValue(['/tools/modules']);

      await runSanyParse('/home/user/specs/Test.tla', '/tools', '/java');

      expect(mockRunJavaCommand).toHaveBeenCalledWith(
        '/tools/tla2tools.jar',
        'tla2sany.SANY',
        ['Test.tla'],
        expect.arrayContaining([expect.stringMatching(/-DTLA-Library=/)]),
        '/java',
        '/home/user/specs'
      );
    });

    it('handles empty module search paths', async () => {
      const mockProc = createMockProcessInfo('');
      mockRunJavaCommand.mockResolvedValue(mockProc);
      mockGetClassPath.mockReturnValue('/tools/tla2tools.jar');
      mockGetModuleSearchPaths.mockReturnValue([]);

      await runSanyParse('/home/user/specs/Test.tla', '/tools');

      expect(mockRunJavaCommand).toHaveBeenCalledWith(
        '/tools/tla2tools.jar',
        'tla2sany.SANY',
        ['Test.tla'],
        [],
        undefined,
        '/home/user/specs'
      );
    });

    it('filters out jarfile paths from module search paths', async () => {
      const mockProc = createMockProcessInfo('');
      mockRunJavaCommand.mockResolvedValue(mockProc);
      mockGetClassPath.mockReturnValue('/tools/tla2tools.jar');
      mockGetModuleSearchPaths.mockReturnValue([
        '/tools/modules',
        'jarfile:/tools/archive.jar',
        '/tools/other'
      ]);

      await runSanyParse('/home/user/specs/Test.tla', '/tools');

      const call = mockRunJavaCommand.mock.calls[0];
      const javaOpts = call[3] as string[];
      expect(javaOpts).toHaveLength(1);
      expect(javaOpts[0]).not.toContain('jarfile:');
      expect(javaOpts[0]).toContain('/tools/modules');
      expect(javaOpts[0]).toContain('/tools/other');
    });

    it('returns process info from runJavaCommand', async () => {
      const mockProc = createMockProcessInfo('');
      mockRunJavaCommand.mockResolvedValue(mockProc);
      mockGetClassPath.mockReturnValue('/tools/tla2tools.jar');
      mockGetModuleSearchPaths.mockReturnValue([]);

      const result = await runSanyParse('/home/user/specs/Test.tla', '/tools');

      expect(result).toBe(mockProc);
    });
  });

  describe('parseSanyOutput', () => {
    it('parses Unix file paths correctly', async () => {
      const output = `Parsing file /home/user/specs/Module.tla
Semantic processing of module Module
SANY finished.
`;

      const procInfo = createMockProcessInfo(output);
      const result = await parseSanyOutput(procInfo);

      expect(result.success).toBe(true);
      expect(result.errors).toHaveLength(0);
    });

    it('parses lexical errors correctly', async () => {
      const output = `Parsing file /home/user/specs/Module.tla
  Lexical error at line 10, column 5. Undefined operator Add
SANY finished.
`;

      const procInfo = createMockProcessInfo(output);
      const result = await parseSanyOutput(procInfo);

      expect(result.success).toBe(false);
      expect(result.errors).toHaveLength(1);
      expect(result.errors[0].file).toBe('/home/user/specs/Module.tla');
      expect(result.errors[0].line).toBe(10);
      expect(result.errors[0].column).toBe(5);
      expect(result.errors[0].message).toBe('Undefined operator Add');
    });

    it('parses Windows file paths correctly', async () => {
      Object.defineProperty(process, 'platform', { value: 'win32', configurable: true });

      const output = `Parsing file C:\\Users\\user\\specs\\Module.tla
Semantic processing of module Module
SANY finished.
`;

      const procInfo = createMockProcessInfo(output);
      const result = await parseSanyOutput(procInfo);

      expect(result.success).toBe(true);
      expect(result.errors).toHaveLength(0);
    });

    it('normalizes Windows backslashes internally and denormalizes in output', async () => {
      Object.defineProperty(process, 'platform', { value: 'win32', configurable: true });

      const output = `Parsing file C:\\Users\\user\\specs\\Module.tla
  Lexical error at line 5, column 10. Syntax error
SANY finished.
`;

      const procInfo = createMockProcessInfo(output);
      const result = await parseSanyOutput(procInfo);

      expect(result.success).toBe(false);
      expect(result.errors[0].file).toBe('C:\\Users\\user\\specs\\Module.tla');
    });

    it('handles error blocks with ranges', async () => {
      const output = `Parsing file /path/Module.tla
*** Errors:
line 42, col 15 to line 42, col 20 of module Module
Undefined operator Foo

SANY finished.`;

      const procInfo = createMockProcessInfo(output);
      const result = await parseSanyOutput(procInfo);

      expect(result.errors.length).toBeGreaterThanOrEqual(1);
      expect(result.errors[0].line).toBe(42);
      expect(result.errors[0].column).toBe(15);
      expect(result.errors[0].message).toContain('Undefined operator Foo');
    });

    it('handles warning blocks', async () => {
      const output = `Parsing file /path/Module.tla
*** Warnings:
line 10, col 5 to line 10, col 10 of module Module
Unused variable x

SANY finished.`;

      const procInfo = createMockProcessInfo(output);
      const result = await parseSanyOutput(procInfo);

      expect(result.success).toBe(true);
      expect(result.warnings.length).toBeGreaterThanOrEqual(1);
      expect(result.warnings[0].line).toBe(10);
      expect(result.warnings[0].column).toBe(5);
      expect(result.warnings[0].message).toContain('Unused variable x');
    });

    it('handles parse error blocks', async () => {
      const output = `Parsing file /path/Module.tla
***Parse Error***
at line 20, col 3 Found something unexpected
SANY finished.
`;

      const procInfo = createMockProcessInfo(output);
      const result = await parseSanyOutput(procInfo);

      expect(result.errors.length).toBeGreaterThan(0);
    });

    it('handles abort messages', async () => {
      const output = `Parsing file /path/Module.tla
*** Abort messages:
line 5, col 1 to line 5, col 10 of module Module
Fatal error occurred
SANY finished.
`;

      const procInfo = createMockProcessInfo(output);
      const result = await parseSanyOutput(procInfo);

      expect(result.errors.length).toBeGreaterThan(0);
    });

    it('handles fatal errors', async () => {
      const output = `Parsing file /path/Module.tla
Fatal errors while parsing TLA+ spec
SANY finished.
`;

      const procInfo = createMockProcessInfo(output);
      const result = await parseSanyOutput(procInfo);

      expect(result.errors.length).toBeGreaterThan(0);
    });

    it('skips residual stack traces', async () => {
      const output = `Parsing file /path/Module.tla
*** Errors:
line 1, col 1 to line 1, col 5 of module Module
Error message
Residual stack trace follows:
java.lang.Exception
  at SomeClass.method
SANY finished.
`;

      const procInfo = createMockProcessInfo(output);
      const result = await parseSanyOutput(procInfo);

      expect(result.errors).toHaveLength(1);
      expect(result.errors[0].message).not.toContain('java.lang.Exception');
    });

    it('handles multi-line error messages', async () => {
      const output = `Parsing file /path/Module.tla
*** Errors:
line 20, col 3 to line 21, col 10 of module Module
This is an error message
SANY finished.`;

      const procInfo = createMockProcessInfo(output);
      const result = await parseSanyOutput(procInfo);

      expect(result.errors[0].message).toContain('error message');
    });

    it('handles pending error message without range', async () => {
      const output = `Parsing file /path/Module.tla
*** Errors:
Some error without location
SANY finished.
`;

      const procInfo = createMockProcessInfo(output);
      const result = await parseSanyOutput(procInfo);

      expect(result.errors).toHaveLength(1);
      expect(result.errors[0].line).toBe(1);
      expect(result.errors[0].column).toBe(1);
    });

    it('handles pending warning message without range', async () => {
      const output = `Parsing file /path/Module.tla
*** Warnings:
Some warning without location
SANY finished.
`;

      const procInfo = createMockProcessInfo(output);
      const result = await parseSanyOutput(procInfo);

      expect(result.warnings).toHaveLength(1);
      expect(result.warnings[0].line).toBe(1);
      expect(result.warnings[0].column).toBe(1);
    });

    it('handles at line X, column Y format', async () => {
      const output = `Parsing file /path/Module.tla
*** Errors:
at line 15, column 8 some error
SANY finished.
`;

      const procInfo = createMockProcessInfo(output);
      const result = await parseSanyOutput(procInfo);

      expect(result.errors.length).toBeGreaterThan(0);
    });

    it('waits for process to close if not already completed', async () => {
      const mergedOutput = new PassThrough();
      const proc = new EventEmitter() as EventEmitter & { exitCode: number | null; once: (event: string, cb: () => void) => void };
      proc.exitCode = null;

      const procInfo: ProcessInfo = {
        process: proc as ProcessInfo['process'],
        stdout: null,
        stderr: null,
        mergedOutput,
        kill: jest.fn()
      };

      setImmediate(() => {
        mergedOutput.write(`Parsing file /path/Module.tla
SANY finished.
`);
        mergedOutput.end();
        proc.exitCode = 0;
        proc.emit('close');
      });

      const result = await parseSanyOutput(procInfo);

      expect(result.success).toBe(true);
    });

    it('keeps forward slashes on Unix', async () => {
      Object.defineProperty(process, 'platform', { value: 'linux', configurable: true });

      const output = `Parsing file /home/user/specs/Module.tla
  Lexical error at line 1, column 1. Error
SANY finished.
`;

      const procInfo = createMockProcessInfo(output);
      const result = await parseSanyOutput(procInfo);

      expect(result.errors[0].file).toBe('/home/user/specs/Module.tla');
      expect(result.errors[0].file).not.toContain('\\');
    });

    it('handles empty output', async () => {
      const output = '';

      const procInfo = createMockProcessInfo(output);
      const result = await parseSanyOutput(procInfo);

      expect(result.success).toBe(true);
      expect(result.errors).toHaveLength(0);
      expect(result.warnings).toHaveLength(0);
    });

    it('handles semantic processing message', async () => {
      const output = `Parsing file /path/Module.tla
Semantic processing of module Module
Semantic processing of module Integers
SANY finished.
`;

      const procInfo = createMockProcessInfo(output);
      const result = await parseSanyOutput(procInfo);

      expect(result.success).toBe(true);
    });
  });
});
