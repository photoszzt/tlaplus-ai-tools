import { runProcess } from "../process-runner";

describe("process-runner", () => {
  const node = process.execPath;

  beforeAll(() => {
    jest.setTimeout(15000);
  });

  it("delivers output while the process is still running", async () => {
    const controller = new AbortController();
    let observed = false;
    const options = {
      command: node,
      args: ["-e", "process.stdout.write('ready\\n'); setInterval(() => {}, 1000)"],
      signal: controller.signal,
      timeoutMs: 3000,
      onOutput: (chunk: Buffer, stream: "stdout" | "stderr") => {
        if (stream === "stdout" && chunk.toString().includes("ready")) {
          observed = true;
          controller.abort();
        }
      },
    };
    const result = await runProcess(options);
    expect(observed).toBe(true);
    expect(result.aborted).toBe(true);
    expect(result.timedOut).toBe(false);
    expect(result.stdout).toContain("ready");
  });

  it("never-ending stream cannot hang the runner (timeout)", async () => {
    const started = Date.now();
    const result = await runProcess({
      command: node,
      args: ["-e", "setInterval(() => process.stdout.write('tick\\n'), 5)"],
      timeoutMs: 200,
      killGraceMs: 100,
    });

    expect(result.timedOut).toBe(true);
    expect(result.killed).toBe(true);
    // A loaded runner may time out before Node emits its first line.
    expect(Date.now() - started).toBeLessThan(5000);
  });

  it("preserves output and completes when its live output observer throws", async () => {
    const result = await runProcess({
      command: node,
      args: ["-e", "process.stdout.write('ready'); process.stderr.write('diagnostic')"],
      timeoutMs: 3000,
      onOutput: () => {
        throw new Error("observer-private-details");
      },
    });
    expect(result.exitCode).toBe(0);
    expect(result.stdout).toContain("ready");
    expect(result.stderr).toContain("diagnostic");
    expect(result.combined).toContain("Output observer failed");
    expect(result.combined).not.toContain("observer-private-details");
  });

  it("timeout kills process and returns partial logs", async () => {
    const result = await runProcess({
      command: node,
      args: ["-e", "process.stdout.write('line-0\\n'); setInterval(() => {}, 1000)"],
      timeoutMs: 3000,
      killGraceMs: 100,
    });

    expect(result.timedOut).toBe(true);
    expect(result.killed).toBe(true);
    expect(result.stdout).toContain("line-");
  });

  it("AbortSignal cancellation kills process immediately", async () => {
    const controller = new AbortController();
    const start = Date.now();

    const promise = runProcess({
      command: node,
      args: ["-e", "setInterval(() => process.stdout.write('running\\n'), 10)"],
      signal: controller.signal,
      killGraceMs: 2000,
    });

    setTimeout(() => controller.abort(), 50);

    const result = await promise;
    const duration = Date.now() - start;

    expect(result.aborted).toBe(true);
    expect(result.timedOut).toBe(false);
    expect(result.killed).toBe(true);
    expect(duration).toBeLessThan(1000);
  });

  it("large output does not OOM (bounded buffer)", async () => {
    const result = await runProcess({
      command: node,
      args: [
        "-e",
        "const chunk = 'x'.repeat(1024); for (let i = 0; i < 5000; i++) process.stdout.write(chunk);",
      ],
      timeoutMs: 2000,
      maxOutputBytes: 2048,
    });

    expect(result.stdout.length).toBeLessThanOrEqual(2048);
    expect(result.combined.length).toBeLessThanOrEqual(2048);
  });
});
