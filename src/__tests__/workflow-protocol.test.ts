import * as fs from "fs";
import * as os from "os";
import * as path from "path";
import { Client } from "@modelcontextprotocol/sdk/client/index.js";
import { McpServer } from "@modelcontextprotocol/sdk/server/mcp.js";
import { InMemoryTransport } from "@modelcontextprotocol/sdk/inMemory.js";
import {
  ElicitRequestSchema,
  CreateMessageRequestSchema,
  CallToolResultSchema,
  CancelledNotificationSchema,
  type ElicitResult,
  type CreateMessageRequest,
  type CallToolResult,
} from "@modelcontextprotocol/sdk/types.js";
import { registerWorkflowPrompts } from "../tools/workflows";
import { registerPrepareConfigTool } from "../tools/prepare-config";
import { MINIMAL_CONFIG } from "./fixtures/config-samples";

describe("Production workflow prompts and config assistance through MCP", () => {
  let dir: string;
  let server: McpServer;
  let client: Client;
  let elicitation: ElicitResult;
  let samples: CreateMessageRequest["params"][];

  beforeEach(async () => {
    dir = fs.mkdtempSync(path.join(os.tmpdir(), "tla-workflow-"));
    fs.writeFileSync(path.join(dir, "Counter.tla"), "spec-data-not-uploaded-implicitly");
    fs.writeFileSync(path.join(dir, "Counter.cfg"), "INIT Init\nNEXT Next\n");
    server = new McpServer({ name: "workflow-server", version: "1" });
    await registerWorkflowPrompts(server, { ...MINIMAL_CONFIG, workingDir: dir });
    registerPrepareConfigTool(server);
    samples = [];
    elicitation = { action: "accept", content: {} };
    client = new Client(
      { name: "workflow-client", version: "1" },
      {
        capabilities: {
          sampling: {},
          elicitation: { form: {} },
        },
      },
    );
    client.setRequestHandler(ElicitRequestSchema, async () => elicitation);
    client.setRequestHandler(CreateMessageRequestSchema, async (request) => {
      samples.push(request.params);
      return {
        role: "assistant",
        content: { type: "text", text: "CONSTANT Max = 3, unverified" },
        model: "test-model",
      };
    });
    const [a, b] = InMemoryTransport.createLinkedPair();
    await server.connect(b);
    await client.connect(a);
  });

  afterEach(async () => {
    await client.close();
    await server.close();
    fs.rmSync(dir, { recursive: true, force: true });
  });

  const draft = async (args = {}) =>
    CallToolResultSchema.parse(
      await client.callTool({
        name: "tlaplus_mcp_tlc_prepare_config",
        arguments: args,
      }),
    );
  const text = (result: CallToolResult) => {
    const block = result.content[0];
    if (block.type !== "text") throw new Error("Expected text response");
    return block.text;
  };

  it("exposes maintained skills as simple/argument prompts and readable reference templates", async () => {
    const listed = await client.listPrompts();
    expect(listed.prompts.some((prompt) => prompt.name === "tla-check")).toBe(true);
    expect(listed.prompts.find((prompt) => prompt.name === "tla-check")?.description).toContain(
      "exhaustive model checking",
    );
    const simple = await client.getPrompt({ name: "tla-getting-started" });
    expect(simple.messages[0].content.type).toBe("resource");
    const prompt = await client.getPrompt({
      name: "tla-check",
      arguments: { fileName: "Counter.tla", cfgFile: "Counter.cfg" },
    });
    const serialized = JSON.stringify(prompt);
    expect(serialized).toContain("tlaplus_mcp_tlc_check");
    expect(serialized).not.toContain("mcp__plugin_tlaplus_tlaplus__");
    expect(serialized).toContain("Counter.cfg");
    const resource = await client.readResource({ uri: "tlaplus://skills/tla-check" });
    expect(resource.contents[0]).toMatchObject({ mimeType: "text/markdown" });
    const shared = await client.readResource({
      uri: "tlaplus://skills/shared/cfg-selection-algorithm.md",
    });
    expect(JSON.stringify(shared)).toContain("cfg");
    await expect(
      client.readResource({ uri: "tlaplus://skills/tla-check/..%2F..%2Fpackage.json" }),
    ).rejects.toThrow();
  });

  it("completes actual prompt files and known template names", async () => {
    const prompt = await client.complete({
      ref: { type: "ref/prompt", name: "tla-check" },
      argument: { name: "fileName", value: "Coun" },
    });
    expect(prompt.completion.values).toEqual(["Counter.tla"]);
    const template = await client.complete({
      ref: { type: "ref/resource", uri: "tlaplus://skills/{skill}" },
      argument: { name: "skill", value: "tla-ch" },
    });
    expect(template.completion.values).toEqual(["tla-check"]);
    const reference = await client.complete({
      ref: { type: "ref/resource", uri: "tlaplus://skills/{skill}/{file}" },
      argument: { name: "file", value: "cfg" },
      context: { arguments: { skill: "shared" } },
    });
    expect(reference.completion.values).toEqual(["cfg-selection-algorithm.md"]);
  });

  it("prepares a deterministic draft without asking, sampling, or writing", async () => {
    const result = await draft({ invariants: ["TypeOK"] });
    expect(result.isError).not.toBe(true);
    expect(JSON.parse(text(result))).toMatchObject({
      status: "draft",
      mode: "check",
      workers: 1,
      config: "INIT Init\nNEXT Next\nINVARIANT TypeOK\nCHECK_DEADLOCK TRUE\n",
    });
    expect(samples).toHaveLength(0);
    expect(fs.readdirSync(dir).sort()).toEqual(["Counter.cfg", "Counter.tla"]);
    expect(fs.readFileSync(path.join(dir, "Counter.cfg"), "utf8")).toBe("INIT Init\nNEXT Next\n");
  });

  it("elicits defaults and titled enums, and only samples explicitly supplied text", async () => {
    let form: Record<string, unknown> | undefined;
    client.setRequestHandler(ElicitRequestSchema, async (request) => {
      form = request.params;
      return {
        action: "accept",
        content: { mode: "simulate", workers: 2, invariants: ["TypeOK"] },
      };
    });
    const result = await draft({
      askUser: true,
      useSampling: true,
      specText: "explicit-spec-data",
      invariants: ["TypeOK", "Safe"],
    });
    expect(result.isError).not.toBe(true);
    expect(JSON.parse(text(result))).toMatchObject({
      mode: "simulate",
      workers: 2,
      unverifiedSuggestion: "CONSTANT Max = 3, unverified",
    });
    expect(JSON.stringify(form)).toContain('"oneOf"');
    expect(JSON.stringify(form)).toContain('"anyOf"');
    expect(JSON.stringify(form)).toContain('"default":true');
    expect(samples).toHaveLength(1);
    expect(samples[0].includeContext).toBe("none");
    expect(samples[0].messages).toEqual([
      { role: "user", content: { type: "text", text: "explicit-spec-data" } },
    ]);
    expect(JSON.stringify(samples)).not.toContain("spec-data-not-uploaded-implicitly");
  });

  it.each(["decline", "cancel"] as const)(
    "honors elicitation %s without sampling",
    async (action) => {
      elicitation = { action };
      const result = await draft({ askUser: true, useSampling: true, specText: "explicit-data" });
      expect(text(result)).toContain("no draft was generated");
      expect(samples).toHaveLength(0);
    },
  );

  it("rejects unsupported capabilities, missing sampling text, and injected identifiers", async () => {
    expect((await draft({ useSampling: true })).isError).toBe(true);
    expect((await draft({ init: "Init\nCONSTANT X=1" })).isError).toBe(true);
    await client.close();
    client = new Client({ name: "limited-client", version: "1" });
    const limited = new McpServer({ name: "limited-server", version: "1" });
    registerPrepareConfigTool(limited);
    const [a, b] = InMemoryTransport.createLinkedPair();
    await limited.connect(b);
    await client.connect(a);
    try {
      expect((await draft({ askUser: true })).isError).toBe(true);
      expect((await draft({ useSampling: true, specText: "explicit-data" })).isError).toBe(true);
    } finally {
      await limited.close();
    }
  });

  it("sends cancellation for the outstanding elicitation when its parent tool is cancelled", async () => {
    let ready: () => void = () => {};
    const received = new Promise<void>((resolve) => {
      ready = resolve;
    });
    let cancelled: () => void = () => {};
    const aborted = new Promise<void>((resolve) => {
      cancelled = resolve;
    });
    let questionId: string | number | undefined;
    let finishQuestion: (reply: ElicitResult) => void = () => {};
    client.setNotificationHandler(CancelledNotificationSchema, ({ params }) => {
      expect(params.requestId).toBe(questionId);
      finishQuestion({ action: "cancel" });
      cancelled();
    });
    client.setRequestHandler(ElicitRequestSchema, async (_request, extra) => {
      questionId = extra.requestId;
      ready();
      return new Promise<ElicitResult>((resolve) => {
        finishQuestion = resolve;
      });
    });
    const controller = new AbortController();
    const result = client.callTool(
      { name: "tlaplus_mcp_tlc_prepare_config", arguments: { askUser: true } },
      undefined,
      { signal: controller.signal },
    );
    const rejected = expect(result).rejects.toThrow();
    await received;
    controller.abort();
    await rejected;
    await aborted;
    expect(samples).toHaveLength(0);
  });
});
