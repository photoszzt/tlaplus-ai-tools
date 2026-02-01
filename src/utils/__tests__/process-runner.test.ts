import { runProcess } from '../process-runner';

describe('process-runner', () => {
  const node = process.execPath;

  beforeAll(() => {
    jest.setTimeout(15000);
  });

  it('never-ending stream cannot hang the runner (timeout)', async () => {
    const result = await runProcess({
      command: node,
      args: ['-e', "setInterval(() => process.stdout.write('tick\\n'), 5)"],
      timeoutMs: 200,
      killGraceMs: 100
    });

    expect(result.timedOut).toBe(true);
    expect(result.killed).toBe(true);
    if (process.platform === 'win32') {
      expect(result.stdout.length).toBeGreaterThanOrEqual(0);
    } else {
      expect(result.stdout.length).toBeGreaterThan(0);
    }
  });

  it('timeout kills process and returns partial logs', async () => {
    const result = await runProcess({
      command: node,
      args: ['-e', "let i = 0; setInterval(() => console.log('line-' + (i++)), 5)"],
      timeoutMs: 150,
      killGraceMs: 100
    });

    expect(result.timedOut).toBe(true);
    expect(result.killed).toBe(true);
    expect(result.stdout).toContain('line-');
  });

  it('AbortSignal cancellation kills process immediately', async () => {
    const controller = new AbortController();
    const start = Date.now();

    const promise = runProcess({
      command: node,
      args: ['-e', "setInterval(() => process.stdout.write('running\\n'), 10)"],
      signal: controller.signal,
      killGraceMs: 2000
    });

    setTimeout(() => controller.abort(), 50);

    const result = await promise;
    const duration = Date.now() - start;

    expect(result.aborted).toBe(true);
    expect(result.timedOut).toBe(false);
    expect(result.killed).toBe(true);
    expect(duration).toBeLessThan(1000);
  });

  it('large output does not OOM (bounded buffer)', async () => {
    const result = await runProcess({
      command: node,
      args: ['-e', "const chunk = 'x'.repeat(1024); for (let i = 0; i < 5000; i++) process.stdout.write(chunk);"],
      timeoutMs: 2000,
      maxOutputBytes: 2048
    });

    expect(result.stdout.length).toBeLessThanOrEqual(2048);
    expect(result.combined.length).toBeLessThanOrEqual(2048);
  });
});
