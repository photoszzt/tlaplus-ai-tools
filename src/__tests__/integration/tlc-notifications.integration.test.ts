import * as fs from "fs";
import * as os from "os";
import * as path from "path";
import { Client } from "@modelcontextprotocol/sdk/client/index.js";
import { InMemoryTransport } from "@modelcontextprotocol/sdk/inMemory.js";
import {
  ProgressNotificationSchema,
  type JSONRPCMessage,
} from "@modelcontextprotocol/sdk/types.js";
import { TLAPlusMCPServer } from "../../server";
import { MINIMAL_CONFIG } from "../fixtures/config-samples";

const toolsDir = path.resolve(__dirname, "../../../tools");
const describeWithTools = fs.existsSync(path.join(toolsDir, "tla2tools.jar"))
  ? describe
  : describe.skip;

describeWithTools("TLC notifications through the real MCP SDK and Java", () => {
  let dir: string;
  let spec: string;
  let client: Client;
  let server: Awaited<ReturnType<TLAPlusMCPServer["createMCPServer"]>>;
  let messages: { message: JSONRPCMessage; beforeResult: boolean }[];
  let completed: boolean;

  beforeEach(async () => {
    dir = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), "tlc-notifications-")));
    spec = path.join(dir, "Counter.tla");
    fs.writeFileSync(
      spec,
      "---- MODULE Counter ----\nEXTENDS Integers\nVARIABLE x\nInit == x = 0\nNext == x' = 1 - x\nFail == x = 0\n====\n",
    );
    fs.writeFileSync(path.join(dir, "Counter.cfg"), "INIT Init\nNEXT Next\n");
    server = await new TLAPlusMCPServer({
      ...MINIMAL_CONFIG,
      toolsDir,
      workingDir: dir,
    }).createMCPServer();
    client = new Client({ name: "tlc-notification-test", version: "1" });
    const [clientTransport, serverTransport] = InMemoryTransport.createLinkedPair();
    const send = serverTransport.send.bind(serverTransport);
    messages = [];
    completed = false;
    serverTransport.send = async (message, options) => {
      messages.push({ message, beforeResult: !completed });
      await send(message, options);
    };
    await server.connect(serverTransport);
    await client.connect(clientTransport);
  });

  afterEach(async () => {
    await client.close();
    await server.close();
    fs.rmSync(dir, { recursive: true, force: true });
  });

  it("streams native statistics before the tool result, including progress token zero", async () => {
    const result = await client.callTool({
      name: "tlaplus_mcp_tlc_smoke",
      arguments: {
        fileName: spec,
        extraJavaOpts: ["-Dtlc2.TLC.progressInterval=1"],
        timeoutMs: 15000,
      },
      _meta: { progressToken: 0 },
    });
    completed = true;
    expect(result.isError).toBe(false);
    const progress = messages.flatMap(({ message, beforeResult }) =>
      "method" in message && message.method === "notifications/progress"
        ? [{ ...ProgressNotificationSchema.parse(message).params, beforeResult }]
        : [],
    );
    expect(progress.length).toBeGreaterThan(2);
    expect(progress.every((event) => event.progressToken === 0 && event.total === undefined)).toBe(
      true,
    );
    expect(
      progress.some(
        (event) =>
          event.beforeResult &&
          String(event.message).includes("states generated") &&
          String(event.message).includes("-1 distinct states found"),
      ),
    ).toBe(true);
    for (let i = 1; i < progress.length; i++) {
      expect(progress[i].progress).toBeGreaterThan(progress[i - 1].progress);
    }
    expect(
      messages.some(
        ({ message }) => "method" in message && message.method === "notifications/message",
      ),
    ).toBe(true);
  }, 20000);

  it("honors logging/setLevel while preserving error logs and an empty progress token", async () => {
    await client.setLoggingLevel("error");
    const args = { fileName: spec, timeoutMs: 15000 };
    const success = await client.callTool({ name: "tlaplus_mcp_tlc_check", arguments: args });
    expect(success.isError).toBe(false);
    expect(
      messages.some(
        ({ message }) => "method" in message && message.method === "notifications/message",
      ),
    ).toBe(false);
    fs.appendFileSync(path.join(dir, "Counter.cfg"), "INVARIANT Fail\n");
    const failure = await client.callTool({
      name: "tlaplus_mcp_tlc_check",
      arguments: args,
      _meta: { progressToken: "" },
    });
    expect(failure.isError).toBe(true);
    const logs = messages.flatMap(({ message }) =>
      "method" in message && message.method === "notifications/message" ? [message.params] : [],
    );
    expect(logs).toEqual([
      { level: "error", logger: "tlc", data: { message: "TLC finished with exit code 12" } },
    ]);
    expect(
      messages.some(
        ({ message }) =>
          "method" in message &&
          message.method === "notifications/progress" &&
          message.params?.progressToken === "",
      ),
    ).toBe(true);
  }, 20000);
});
