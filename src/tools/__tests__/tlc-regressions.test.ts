import * as fs from "fs";
import * as os from "os";
import * as path from "path";
import { z } from "zod";
import { registerTlcTools } from "../tlc";
import { runTlcAndWait } from "../../utils/tlc-helpers";
import { createMockMcpServer, callRegisteredTool } from "../../__tests__/helpers/mock-server";
import { MINIMAL_CONFIG } from "../../__tests__/fixtures/config-samples";

jest.mock("../../utils/tlc-helpers", () => ({
  ...jest.requireActual("../../utils/tlc-helpers"),
  runTlcAndWait: jest.fn(),
}));

const runTlc = jest.mocked(runTlcAndWait);
const tools = ["check", "smoke", "explore", "trace"];

describe("TLC config and result regressions", () => {
  let dir: string;
  let spec: string;
  let cfg: string;
  let trace: string;
  let server: ReturnType<typeof createMockMcpServer>;

  beforeEach(async () => {
    jest.clearAllMocks();
    dir = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), "tlc-regression-")));
    spec = path.join(dir, "Probe.tla");
    cfg = path.join(dir, "external", "Probe.cfg");
    trace = path.join(dir, "trace.tlc");
    fs.mkdirSync(path.dirname(cfg));
    fs.writeFileSync(spec, "---- MODULE Probe ----\n====\n");
    fs.writeFileSync(cfg, "INVARIANT Fail\n");
    fs.writeFileSync(trace, "trace fixture");
    server = createMockMcpServer();
    await registerTlcTools(server, {
      ...MINIMAL_CONFIG,
      toolsDir: path.join(dir, "tools"),
      workingDir: dir,
    });
    runTlc.mockResolvedValue({ exitCode: 0, output: ["Model checking completed."] });
  });

  afterEach(() => {
    fs.rmSync(dir, { recursive: true, force: true });
    delete process.env.TLC_CHECK_TIMEOUT_MS;
  });

  function call(tool: string, extra = {}, context = {}) {
    return callRegisteredTool(
      server,
      `tlaplus_mcp_tlc_${tool}`,
      {
        fileName: spec,
        cfgFile: cfg,
        behaviorLength: 3,
        traceFile: trace,
        ...extra,
      },
      context,
    );
  }

  describe.each(tools)("%s", (tool) => {
    it.each([false, true])(
      "uses the exact explicit config with adjacent config: %s",
      async (adjacent) => {
        if (adjacent) fs.writeFileSync(path.join(dir, "Probe.cfg"), "INVARIANT Safe\n");
        // Auto-discovery must not select a different MC module when an explicit config is supplied.
        fs.writeFileSync(path.join(dir, "MCProbe.tla"), "---- MODULE MCProbe ----\n====\n");
        fs.writeFileSync(path.join(dir, "MCProbe.cfg"), "INVARIANT Safe\n");
        const result = await call(tool);
        expect(result.isError).not.toBe(true);
        expect(runTlc.mock.calls[0].slice(0, 2)).toEqual([spec, cfg]);
      },
    );

    it("uses an explicit config without any adjacent config or MC module", async () => {
      const result = await call(tool);
      expect(result.isError).not.toBe(true);
      expect(runTlc.mock.calls[0].slice(0, 2)).toEqual([spec, cfg]);
    });

    it("marks missing config as an MCP error and never launches TLC", async () => {
      fs.rmSync(cfg);
      const result = await call(tool);
      expect(result.isError).toBe(true);
      expect(result.content[0].text).toContain(cfg);
      expect(runTlc).not.toHaveBeenCalled();
    });

    it.each([12, 124, 130])("marks unsuccessful exit %s as an MCP error", async (exitCode) => {
      runTlc.mockResolvedValue({ exitCode, output: ["Stopped"] });
      expect((await call(tool)).isError).toBe(true);
    });
  });

  it("passes exhaustive-check timeout and cancellation to the process runner", async () => {
    const controller = new AbortController();
    await call("check", { timeoutMs: 5000 }, { signal: controller.signal });
    expect(runTlc.mock.calls[0][6]).toBe(5000);
    expect(runTlc.mock.calls[0][7]).toBe(controller.signal);
  });

  it("supports exhaustive-check timeout from the environment", async () => {
    process.env.TLC_CHECK_TIMEOUT_MS = "7000";
    await call("check");
    expect(runTlc.mock.calls[0][6]).toBe(7000);
  });

  it("rejects fractional exploration lengths at the MCP boundary", () => {
    const schema = z.object(server.getRegisteredTools().get("tlaplus_mcp_tlc_explore")!.schema);
    expect(schema.safeParse({ fileName: spec, behaviorLength: 1.5 }).success).toBe(false);
    expect(schema.safeParse({ fileName: spec, behaviorLength: 3 }).success).toBe(true);
  });
});
