import * as fs from "fs";
import * as os from "os";
import * as path from "path";
import { registerSanyTools } from "../../tools/sany";
import { registerTlcTools } from "../../tools/tlc";
import { createMockMcpServer, callRegisteredTool } from "../helpers/mock-server";
import { MINIMAL_CONFIG } from "../fixtures/config-samples";

const toolsDir = path.resolve(__dirname, "../../../tools");
const describeWithTools = fs.existsSync(path.join(toolsDir, "tla2tools.jar"))
  ? describe
  : describe.skip;

describeWithTools("Verification with the real Java toolchain", () => {
  let dir: string;
  let spec: string;
  let cfg: string;
  let server: ReturnType<typeof createMockMcpServer>;

  beforeEach(async () => {
    dir = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), "verification-")));
    spec = path.join(dir, "Probe.tla");
    cfg = path.join(dir, "external", "Probe.cfg");
    fs.mkdirSync(path.dirname(cfg));
    fs.writeFileSync(
      spec,
      `---- MODULE Probe ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = 1 - x
Safe == x \\in {0,1}
Fail == x = 0
TraceView == [seen |-> x]
====
`,
    );
    fs.writeFileSync(cfg, "INIT Init\nNEXT Next\nINVARIANT Fail\n");
    server = createMockMcpServer();
    const config = { ...MINIMAL_CONFIG, toolsDir, workingDir: dir };
    await registerSanyTools(server, config);
    await registerTlcTools(server, config);
  });

  afterEach(() => fs.rmSync(dir, { recursive: true, force: true }));

  const check = (extra = {}) =>
    callRegisteredTool(server, "tlaplus_mcp_tlc_check", {
      fileName: spec,
      cfgFile: cfg,
      timeoutMs: 10000,
      ...extra,
    });

  it.each([false, true])(
    "checks the failing external config with adjacent config: %s",
    async (adjacent) => {
      if (adjacent)
        fs.writeFileSync(path.join(dir, "Probe.cfg"), "INIT Init\nNEXT Next\nINVARIANT Safe\n");
      const result = await check();
      expect(result.isError).toBe(true);
      expect(result.content[0].text).toContain("Invariant Fail is violated");
    },
    20000,
  );

  it("reports a missing module as a parse failure", async () => {
    fs.writeFileSync(spec, "---- MODULE Probe ----\nEXTENDS MissingModuleAudit\n====\n");
    const result = await callRegisteredTool(server, "tlaplus_mcp_sany_parse", { fileName: spec });
    expect(result.isError).toBe(true);
    expect(result.content[0].text).toContain("MissingModuleAudit");
    expect(result.content[0].text).not.toContain("No errors found");
  });

  it("saves and replays a counterexample using its ALIAS", async () => {
    const trace = path.join(dir, "saved.tlc");
    await check({ extraOpts: ["-fp", "0", "-dumpTrace", "tlc", trace] });
    expect(fs.existsSync(trace)).toBe(true);
    fs.appendFileSync(cfg, "ALIAS TraceView\n");
    const result = await callRegisteredTool(server, "tlaplus_mcp_tlc_trace", {
      fileName: spec,
      cfgFile: cfg,
      traceFile: trace,
      extraOpts: ["-fp", "0"],
    });
    expect(result.content[0].text).toContain("Invariant Fail is violated");
    expect(result.content[0].text).toMatch(/seen = 1/);
  }, 20000);
});
