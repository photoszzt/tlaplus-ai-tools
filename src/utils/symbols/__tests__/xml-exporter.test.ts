import { PassThrough } from 'stream';
import { EventEmitter } from 'events';
import { ProcessInfo } from '../../java';
import { runXmlExporter } from '../xml-exporter';

const mockRunJavaCommand = jest.fn();
const mockGetClassPath = jest.fn();

jest.mock('../../java', () => ({
  runJavaCommand: (...args: unknown[]) => mockRunJavaCommand(...args)
}));

jest.mock('../../tla-tools', () => ({
  getClassPath: (...args: unknown[]) => mockGetClassPath(...args)
}));

function createMockProcessInfo(stdout: string, stderr = ''): ProcessInfo {
  const stdoutStream = new PassThrough();
  const stderrStream = new PassThrough();
  const mergedOutput = new PassThrough();
  const proc = new EventEmitter() as EventEmitter & { exitCode: number | null };
  proc.exitCode = 0;

  setImmediate(() => {
    if (stdout) {
      stdoutStream.write(stdout);
      mergedOutput.write(stdout);
    }
    if (stderr) {
      stderrStream.write(stderr);
      mergedOutput.write(stderr);
    }
    stdoutStream.end();
    stderrStream.end();
    mergedOutput.end();
  });

  return {
    process: proc as ProcessInfo['process'],
    stdout: stdoutStream,
    stderr: stderrStream,
    mergedOutput,
    kill: jest.fn()
  };
}

describe('xml-exporter', () => {
  beforeEach(() => {
    mockRunJavaCommand.mockReset();
    mockGetClassPath.mockReset();
    mockGetClassPath.mockReturnValue('/tools/tla2tools.jar:/tools/CommunityModules-deps.jar');
  });

  describe('runXmlExporter', () => {
    it('runs XMLExporter with correct main class', async () => {
      const xml = '<modules></modules>';
      mockRunJavaCommand.mockResolvedValue(createMockProcessInfo(xml));

      await runXmlExporter('/home/user/Counter.tla', '/tools', false);

      expect(mockRunJavaCommand).toHaveBeenCalledWith(
        expect.any(String),
        'tla2sany.xml.XMLExporter',
        expect.any(Array),
        expect.any(Array),
        undefined,
        '/home/user'
      );
    });

    it('passes -o -u flags always', async () => {
      const xml = '<modules></modules>';
      mockRunJavaCommand.mockResolvedValue(createMockProcessInfo(xml));

      await runXmlExporter('/home/user/Counter.tla', '/tools', false);

      const args = mockRunJavaCommand.mock.calls[0][2] as string[];
      expect(args).toContain('-o');
      expect(args).toContain('-u');
    });

    it('passes -r flag when includeExtendedModules=false', async () => {
      const xml = '<modules></modules>';
      mockRunJavaCommand.mockResolvedValue(createMockProcessInfo(xml));

      await runXmlExporter('/home/user/Counter.tla', '/tools', false);

      const args = mockRunJavaCommand.mock.calls[0][2] as string[];
      expect(args).toContain('-r');
    });

    it('omits -r flag when includeExtendedModules=true', async () => {
      const xml = '<modules></modules>';
      mockRunJavaCommand.mockResolvedValue(createMockProcessInfo(xml));

      await runXmlExporter('/home/user/Counter.tla', '/tools', true);

      const args = mockRunJavaCommand.mock.calls[0][2] as string[];
      expect(args).not.toContain('-r');
    });

    it('passes filename as last argument', async () => {
      const xml = '<modules></modules>';
      mockRunJavaCommand.mockResolvedValue(createMockProcessInfo(xml));

      await runXmlExporter('/home/user/Counter.tla', '/tools', false);

      const args = mockRunJavaCommand.mock.calls[0][2] as string[];
      expect(args[args.length - 1]).toBe('Counter.tla');
    });

    it('sets working directory to file directory', async () => {
      const xml = '<modules></modules>';
      mockRunJavaCommand.mockResolvedValue(createMockProcessInfo(xml));

      await runXmlExporter('/home/user/specs/Counter.tla', '/tools', false);

      expect(mockRunJavaCommand).toHaveBeenCalledWith(
        expect.any(String),
        expect.any(String),
        expect.any(Array),
        expect.any(Array),
        undefined,
        '/home/user/specs'
      );
    });

    it('returns collected stdout as xml', async () => {
      const xml = '<modules><context></context></modules>';
      mockRunJavaCommand.mockResolvedValue(createMockProcessInfo(xml));

      const result = await runXmlExporter('/home/user/Counter.tla', '/tools', false);

      expect(result.xml).toBe(xml);
    });

    it('passes javaHome when provided', async () => {
      const xml = '<modules></modules>';
      mockRunJavaCommand.mockResolvedValue(createMockProcessInfo(xml));

      await runXmlExporter('/home/user/Counter.tla', '/tools', false, '/custom/java');

      expect(mockRunJavaCommand).toHaveBeenCalledWith(
        expect.any(String),
        expect.any(String),
        expect.any(Array),
        expect.any(Array),
        '/custom/java',
        expect.any(String)
      );
    });
  });
});
