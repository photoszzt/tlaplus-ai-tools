import { runTlcAndWait } from "../utils/tlc-helpers";
import { runProcess } from "../utils/process-runner";

jest.mock("../utils/process-runner");
jest.mock("../utils/java");
jest.mock("../utils/tla-tools");

const mockRunProcess = runProcess as jest.MockedFunction<typeof runProcess>;

describe("TLC Progress Notifications", () => {
  beforeEach(() => {
    jest.clearAllMocks();

    const { findJavaExecutable, buildJavaOptions } = require("../utils/java");
    const { getClassPath, getModuleSearchPaths } = require("../utils/tla-tools");

    (findJavaExecutable as jest.Mock).mockReturnValue("/usr/bin/java");
    (buildJavaOptions as jest.Mock).mockReturnValue(["-Xmx4G"]);
    (getClassPath as jest.Mock).mockReturnValue("/path/to/tla2tools.jar");
    (getModuleSearchPaths as jest.Mock).mockReturnValue([]);
  });

  it("reports upstream TLC statistics before process completion without a fabricated total", async () => {
    const callback = jest.fn();
    let finished = false;
    mockRunProcess.mockImplementation(async (options) => {
      const observer = options.onOutput;
      const output =
        "@!@!@STARTMSG 2200:0 @!@!@\nProgress(12) at 2026-10-10 00:00:00: 2,500 states generated (1,000 s/min), 1,234 distinct states found (500 ds/min), 321 states left on queue.\n@!@!@ENDMSG 2200 @!@!@\n";
      observer?.(Buffer.from(output.slice(0, 87)), "stdout");
      observer?.(Buffer.from(output.slice(87)), "stdout");
      await new Promise((resolve) => setImmediate(resolve));
      expect(
        callback.mock.calls.some(([event]) => event.message.includes("321 states left on queue")),
      ).toBe(true);
      expect(finished).toBe(false);
      finished = true;
      return {
        exitCode: 0,
        stdout: output,
        stderr: "",
        combined: output,
        timedOut: false,
        aborted: false,
        killed: false,
      };
    });
    await runTlcAndWait(
      "/path/spec.tla",
      "spec.cfg",
      [],
      [],
      "/tools",
      undefined,
      undefined,
      undefined,
      callback,
    );
    const events = callback.mock.calls.map(([event]) => event);
    expect(events.every((event) => event.total === undefined)).toBe(true);
    expect(events.map((event) => event.progress)).toEqual([...events.keys()]);
    expect(events.some((event) => event.message.includes("1,234 distinct states"))).toBe(true);
  });

  it("a blocked notification cannot hold a timed-out tool open forever", async () => {
    mockRunProcess.mockResolvedValue({
      exitCode: null,
      stdout: "",
      stderr: "",
      combined: "",
      timedOut: true,
      aborted: false,
      killed: true,
    });
    const started = Date.now();
    const result = await runTlcAndWait(
      "/path/spec.tla",
      "spec.cfg",
      [],
      [],
      "/tools",
      undefined,
      1,
      undefined,
      () => new Promise(() => {}),
    );
    expect(result.exitCode).toBe(124);
    expect(Date.now() - started).toBeLessThan(2500);
  });

  it("keeps arbitrary user output and checkpoint paths out of notifications", async () => {
    const callback = jest.fn();
    const output = [
      "user-secret-\u03bb",
      "@!@!@STARTMSG 2200:0 @!@!@",
      "Progress(1) at 2026-10-10 00:00:00: user-secret-\u03bb",
      "@!@!@ENDMSG 2200 @!@!@",
      "@!@!@STARTMSG 2195:0 @!@!@",
      "Checkpointing to /private/user-secret",
      "@!@!@ENDMSG 2195 @!@!@",
    ].join("\n");
    mockRunProcess.mockImplementation(async (options) => {
      const bytes = Buffer.from(output);
      for (const byte of bytes) options.onOutput?.(Buffer.from([byte]), "stderr");
      return {
        exitCode: 0,
        stdout: "",
        stderr: output,
        combined: output,
        timedOut: false,
        aborted: false,
        killed: false,
      };
    });
    const result = await runTlcAndWait(
      "/path/spec.tla",
      "spec.cfg",
      [],
      [],
      "/tools",
      undefined,
      undefined,
      undefined,
      callback,
    );
    expect(result.output.join("\n")).toContain("user-secret-\u03bb");
    const messages = callback.mock.calls.map(([event]) => event.message);
    expect(messages).toContain("TLC checkpoint started");
    expect(messages.join("\n")).not.toContain("user-secret");
    expect(messages.join("\n")).not.toContain("/private/");
  });

  it("cancellation releases a blocked notification immediately", async () => {
    const controller = new AbortController();
    mockRunProcess.mockImplementation(async () => {
      await new Promise((resolve) => setImmediate(resolve));
      controller.abort();
      return {
        exitCode: null,
        stdout: "",
        stderr: "",
        combined: "",
        timedOut: false,
        aborted: true,
        killed: true,
      };
    });
    let timer: ReturnType<typeof setTimeout> | undefined;
    try {
      const result = await Promise.race([
        runTlcAndWait(
          "/path/spec.tla",
          "spec.cfg",
          [],
          [],
          "/tools",
          undefined,
          undefined,
          controller.signal,
          () => new Promise(() => {}),
        ),
        new Promise<never>((_resolve, reject) => {
          timer = setTimeout(() => reject(new Error("Cancellation blocked on notifications")), 250);
        }),
      ]);
      expect(result.exitCode).toBe(130);
    } finally {
      clearTimeout(timer);
    }
  });

  it.each([
    { timedOut: true, aborted: false, expected: 124 },
    { timedOut: false, aborted: true, expected: 130 },
  ])("never reports success after interruption: %j", async ({ timedOut, aborted, expected }) => {
    mockRunProcess.mockResolvedValue({
      exitCode: 0,
      stdout: "",
      stderr: "",
      combined: "Partial output",
      timedOut,
      aborted,
      killed: true,
    });
    const result = await runTlcAndWait(
      "/path/to/spec.tla",
      "/external/spec.cfg",
      [],
      [],
      "/tools",
      undefined,
      1000,
    );
    expect(result.exitCode).toBe(expected);
    expect(result.output).toContain("Partial output");
  });

  it("should accept progress callback and process output correctly", async () => {
    const progressCallback = jest.fn();

    const mockOutput = "TLC output line 1\nTLC output line 2\nTLC output line 3";

    mockRunProcess.mockResolvedValue({
      exitCode: 0,
      stdout: "",
      stderr: "",
      combined: mockOutput,
      timedOut: false,
      aborted: false,
      killed: false,
    });

    const result = await runTlcAndWait(
      "/path/to/spec.tla",
      "spec.cfg",
      ["-cleanup", "-simulate"],
      ["-Dtlc2.TLC.stopAfter=3"],
      "/path/to/tools",
      undefined,
      120000,
      undefined,
      progressCallback,
    );

    expect(result.exitCode).toBe(0);
    expect(result.output.length).toBeGreaterThan(0);
  });

  it("should handle progress callback with proper signature", async () => {
    const progressCallback = jest.fn();

    const mockOutput = "TLC output\nline 2\nline 3";

    mockRunProcess.mockResolvedValue({
      exitCode: 0,
      stdout: "",
      stderr: "",
      combined: mockOutput,
      timedOut: false,
      aborted: false,
      killed: false,
    });

    await runTlcAndWait(
      "/path/to/spec.tla",
      "spec.cfg",
      ["-cleanup", "-simulate"],
      ["-Dtlc2.TLC.stopAfter=3"],
      "/path/to/tools",
      undefined,
      120000,
      undefined,
      progressCallback,
    );

    expect(progressCallback).toHaveBeenCalled();
    const firstCall = progressCallback.mock.calls[0][0];
    expect(firstCall.progress).toBe(0);
    expect(firstCall.total).toBeUndefined();
    expect(firstCall.message).toBe("Starting TLC");
  });

  it("should not fail if progress callback is not provided", async () => {
    const mockOutput = "TLC output\nline 2\nline 3";

    mockRunProcess.mockResolvedValue({
      exitCode: 0,
      stdout: "",
      stderr: "",
      combined: mockOutput,
      timedOut: false,
      aborted: false,
      killed: false,
    });

    const result = await runTlcAndWait(
      "/path/to/spec.tla",
      "spec.cfg",
      ["-cleanup", "-simulate"],
      ["-Dtlc2.TLC.stopAfter=3"],
      "/path/to/tools",
      undefined,
      120000,
      undefined,
    );

    expect(result.exitCode).toBe(0);
    expect(result.output.length).toBeGreaterThan(0);
  });

  it("should include progress information in callback when called", async () => {
    const progressCallback = jest.fn();

    const mockOutput = "TLC output\nline 2\nline 3";

    mockRunProcess.mockResolvedValue({
      exitCode: 0,
      stdout: "",
      stderr: "",
      combined: mockOutput,
      timedOut: false,
      aborted: false,
      killed: false,
    });

    await runTlcAndWait(
      "/path/to/spec.tla",
      "spec.cfg",
      ["-cleanup", "-simulate"],
      ["-Dtlc2.TLC.stopAfter=3"],
      "/path/to/tools",
      undefined,
      120000,
      undefined,
      progressCallback,
    );

    expect(progressCallback).toHaveBeenCalled();
    const lastCall = progressCallback.mock.calls[progressCallback.mock.calls.length - 1][0];
    expect(lastCall.message).toContain("TLC finished with exit code 0");
    expect(lastCall.progress).toBeGreaterThan(0);
    expect(lastCall.total).toBeUndefined();
  });
});
