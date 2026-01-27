import { PassThrough } from 'stream';
import { EventEmitter } from 'events';
import { ProcessInfo } from '../../java';
import { extractSymbols } from '../extract';

const mockRunJavaCommand = jest.fn();
const mockGetClassPath = jest.fn();

jest.mock('../../java', () => ({
  runJavaCommand: (...args: unknown[]) => mockRunJavaCommand(...args)
}));

jest.mock('../../tla-tools', () => ({
  getClassPath: (...args: unknown[]) => mockGetClassPath(...args)
}));

function createMockProcessInfo(stdout: string): ProcessInfo {
  const stdoutStream = new PassThrough();
  const stderrStream = new PassThrough();
  const mergedOutput = new PassThrough();
  const proc = new EventEmitter() as EventEmitter & { exitCode: number | null };
  proc.exitCode = 0;

  setImmediate(() => {
    stdoutStream.write(stdout);
    mergedOutput.write(stdout);
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

describe('extract', () => {
  beforeEach(() => {
    mockRunJavaCommand.mockReset();
    mockGetClassPath.mockReset();
    mockGetClassPath.mockReturnValue('/tools/tla2tools.jar');
  });

  describe('extractSymbols', () => {
    it('returns SymbolExtractionResult with schemaVersion 1', async () => {
      const xml = `<?xml version="1.0" encoding="UTF-8"?>
<modules>
  <RootModule>Counter</RootModule>
  <context>
    <entry>
      <UserDefinedOpKind>
        <uniquename>Counter!Init</uniquename>
        <location><filename>Counter</filename><line><begin>10</begin><end>10</end></line><column><begin>1</begin><end>15</end></column></location>
        <level>1</level>
        <arity>0</arity>
      </UserDefinedOpKind>
    </entry>
  </context>
</modules>`;
      mockRunJavaCommand.mockResolvedValue(createMockProcessInfo(xml));

      const result = await extractSymbols('/home/user/Counter.tla', '/tools', false);

      expect(result.schemaVersion).toBe(1);
    });

    it('sets rootModule from file path', async () => {
      const xml = '<modules><context></context></modules>';
      mockRunJavaCommand.mockResolvedValue(createMockProcessInfo(xml));

      const result = await extractSymbols('/home/user/Counter.tla', '/tools', false);

      expect(result.rootModule).toBe('Counter');
    });

    it('sets file path in result', async () => {
      const xml = '<modules><context></context></modules>';
      mockRunJavaCommand.mockResolvedValue(createMockProcessInfo(xml));

      const result = await extractSymbols('/home/user/Counter.tla', '/tools', false);

      expect(result.file).toBe('/home/user/Counter.tla');
    });

    it('sets includeExtendedModules flag to false', async () => {
      const xml = '<modules><context></context></modules>';
      mockRunJavaCommand.mockResolvedValue(createMockProcessInfo(xml));

      const result = await extractSymbols('/home/user/Counter.tla', '/tools', false);
      expect(result.includeExtendedModules).toBe(false);
    });

    it('sets includeExtendedModules flag to true', async () => {
      const xml = '<modules><context></context></modules>';
      mockRunJavaCommand.mockResolvedValue(createMockProcessInfo(xml));

      const result = await extractSymbols('/home/user/Counter.tla', '/tools', true);
      expect(result.includeExtendedModules).toBe(true);
    });

    it('populates candidates with grouped symbols', async () => {
      const xml = `<?xml version="1.0" encoding="UTF-8"?>
<modules>
  <context>
    <entry>
      <OpDeclNode>
        <uniquename>Counter!MaxValue</uniquename>
        <location><filename>Counter</filename><line><begin>3</begin><end>3</end></line><column><begin>1</begin><end>8</end></column></location>
        <level>0</level>
        <arity>0</arity>
      </OpDeclNode>
    </entry>
    <entry>
      <OpDeclNode>
        <uniquename>Counter!count</uniquename>
        <location><filename>Counter</filename><line><begin>5</begin><end>5</end></line><column><begin>1</begin><end>5</end></column></location>
        <level>1</level>
        <arity>0</arity>
      </OpDeclNode>
    </entry>
    <entry>
      <UserDefinedOpKind>
        <uniquename>Counter!Init</uniquename>
        <location><filename>Counter</filename><line><begin>10</begin><end>10</end></line><column><begin>1</begin><end>15</end></column></location>
        <level>1</level>
        <arity>0</arity>
      </UserDefinedOpKind>
    </entry>
  </context>
</modules>`;
      mockRunJavaCommand.mockResolvedValue(createMockProcessInfo(xml));

      const result = await extractSymbols('/home/user/Counter.tla', '/tools', false);

      expect(result.candidates.constants).toHaveLength(1);
      expect(result.candidates.constants[0].name).toBe('MaxValue');
      expect(result.candidates.variables).toHaveLength(1);
      expect(result.candidates.variables[0].name).toBe('count');
      expect(result.candidates.statePredicates).toHaveLength(1);
      expect(result.candidates.statePredicates[0].name).toBe('Init');
    });

    it('populates bestGuess with Init/Next/Spec', async () => {
      const xml = `<?xml version="1.0" encoding="UTF-8"?>
<modules>
  <context>
    <entry>
      <UserDefinedOpKind>
        <uniquename>Counter!Init</uniquename>
        <location><filename>Counter</filename><line><begin>10</begin><end>10</end></line><column><begin>1</begin><end>15</end></column></location>
        <level>1</level>
        <arity>0</arity>
      </UserDefinedOpKind>
    </entry>
    <entry>
      <UserDefinedOpKind>
        <uniquename>Counter!Next</uniquename>
        <location><filename>Counter</filename><line><begin>15</begin><end>18</end></line><column><begin>1</begin><end>1</end></column></location>
        <level>2</level>
        <arity>0</arity>
      </UserDefinedOpKind>
    </entry>
    <entry>
      <UserDefinedOpKind>
        <uniquename>Counter!Spec</uniquename>
        <location><filename>Counter</filename><line><begin>20</begin><end>20</end></line><column><begin>1</begin><end>30</end></column></location>
        <level>3</level>
        <arity>0</arity>
      </UserDefinedOpKind>
    </entry>
  </context>
</modules>`;
      mockRunJavaCommand.mockResolvedValue(createMockProcessInfo(xml));

      const result = await extractSymbols('/home/user/Counter.tla', '/tools', false);

      expect(result.bestGuess.init).not.toBeNull();
      expect(result.bestGuess.init!.name).toBe('Init');
      expect(result.bestGuess.next).not.toBeNull();
      expect(result.bestGuess.next!.name).toBe('Next');
      expect(result.bestGuess.spec).not.toBeNull();
      expect(result.bestGuess.spec!.name).toBe('Spec');
    });

    it('separates extended modules when includeExtendedModules=true', async () => {
      const xml = `<?xml version="1.0" encoding="UTF-8"?>
<modules>
  <context>
    <entry>
      <UserDefinedOpKind>
        <uniquename>Counter!Init</uniquename>
        <location><filename>Counter</filename><line><begin>10</begin><end>10</end></line><column><begin>1</begin><end>15</end></column></location>
        <level>1</level>
        <arity>0</arity>
      </UserDefinedOpKind>
    </entry>
    <entry>
      <UserDefinedOpKind>
        <uniquename>Helper!HelperOp</uniquename>
        <location><filename>Helper</filename><line><begin>5</begin><end>5</end></line><column><begin>1</begin><end>10</end></column></location>
        <level>1</level>
        <arity>0</arity>
      </UserDefinedOpKind>
    </entry>
  </context>
</modules>`;
      mockRunJavaCommand.mockResolvedValue(createMockProcessInfo(xml));

      const result = await extractSymbols('/home/user/Counter.tla', '/tools', true);

      expect(result.candidates.statePredicates.map((s: { name: string }) => s.name)).toContain('Init');
      expect(result.candidates.statePredicates.map((s: { name: string }) => s.name)).not.toContain('HelperOp');
      expect(result.extendedModules).toHaveProperty('Helper');
      expect(result.extendedModules['Helper'].candidates.statePredicates[0].name).toBe('HelperOp');
    });
  });
});
