import { Client } from "@modelcontextprotocol/sdk/client/index.js";
import { McpServer } from "@modelcontextprotocol/sdk/server/mcp.js";
import { InMemoryTransport } from "@modelcontextprotocol/sdk/inMemory.js";
import { CallToolResultSchema } from "@modelcontextprotocol/sdk/types.js";
import { RenderService } from "../tools/animation/RenderService";
import { registerTraceAudioTool } from "../tools/trace-audio";
import { registerWorkflowPrompts } from "../tools/workflows";
import { MINIMAL_CONFIG } from "./fixtures/config-samples";

let canvasAvailable = false;
try {
  require("@napi-rs/canvas");
  canvasAvailable = true;
} catch {}
const nativeImageTest = canvasAvailable ? it : it.skip;

describe("native production content through MCP", () => {
  let server: McpServer;
  let client: Client;
  beforeEach(async () => {
    server = new McpServer({ name: "content", version: "1" });
    registerTraceAudioTool(server);
    await registerWorkflowPrompts(server, MINIMAL_CONFIG);
    client = new Client({ name: "content-client", version: "1" });
    const [a, b] = InMemoryTransport.createLinkedPair();
    await server.connect(b);
    await client.connect(a);
  });
  afterEach(async () => {
    await client.close();
    await server.close();
  });

  it.each([
    [0],
    [7, 7],
    [-Number.MAX_VALUE, 0, Number.MAX_VALUE],
    Array(32).fill(1),
    [-Number.MIN_VALUE, 0, Number.MIN_VALUE],
  ])("returns bounded audible PCM for %j", async (...values: number[]) => {
    const result = CallToolResultSchema.parse(
      await client.callTool({ name: "tlaplus_mcp_trace_audio", arguments: { values } }),
    );
    expect(result.isError).not.toBe(true);
    const audio = result.content.find((block) => block.type === "audio");
    if (!audio || audio.type !== "audio") throw new Error("Missing audio");
    expect(audio.mimeType).toBe("audio/wav");
    const wav = Buffer.from(audio.data, "base64");
    expect(wav.toString("ascii", 0, 4)).toBe("RIFF");
    expect(wav.toString("ascii", 8, 16)).toBe("WAVEfmt ");
    expect(wav.readUInt16LE(20)).toBe(1);
    expect(wav.readUInt16LE(22)).toBe(1);
    expect(wav.readUInt32LE(24)).toBe(8000);
    expect(wav.readUInt16LE(34)).toBe(16);
    expect(wav.length).toBe(44 + values.length * 2400);
    expect(wav.readUInt32LE(4)).toBe(wav.length - 8);
    expect(wav.readUInt32LE(40)).toBe(wav.length - 44);
    const samples = Array.from({ length: (wav.length - 44) / 2 }, (_, i) =>
      wav.readInt16LE(44 + i * 2),
    );
    expect(Math.max(...samples)).toBeGreaterThan(3000);
    expect(Math.max(...samples.map(Math.abs))).toBeLessThanOrEqual(4096);
    expect(samples[0]).toBe(0);
    expect(samples.at(-1)).toBe(0);
  });

  it.each([[], Array(33).fill(0), [null], ["1"], [NaN], [Infinity], [-Infinity]])(
    "rejects invalid scalar sequences %j",
    async (...values: unknown[]) => {
      const result = await client.callTool({
        name: "tlaplus_mcp_trace_audio",
        arguments: { values },
      });
      expect(result.isError).toBe(true);
    },
  );

  nativeImageTest(
    "adds a native PNG only to the animation prompt's declared arguments",
    async () => {
      const listed = await client.listPrompts();
      expect(
        listed.prompts
          .filter((prompt) => prompt.arguments?.some((arg) => arg.name === "svgContent"))
          .map((prompt) => prompt.name),
      ).toEqual(["tla-create-animations"]);
      const result = await client.getPrompt({
        name: "tla-create-animations",
        arguments: {
          svgContent: '<svg width="32" height="24"><rect width="32" height="24" fill="red"/></svg>',
        },
      });
      expect(result.messages.map((message) => message.content.type)).toEqual([
        "resource",
        "text",
        "image",
      ]);
      const content = result.messages[2].content;
      if (content.type !== "image") throw new Error("Missing image");
      const png = Buffer.from(content.data, "base64");
      expect(png.subarray(0, 8).toString("hex")).toBe("89504e470d0a1a0a");
      expect(png.readUInt32BE(16)).toBe(32);
      expect(png.readUInt32BE(20)).toBe(24);
      expect((await client.getPrompt({ name: "tla-create-animations" })).messages).toHaveLength(2);
    },
  );

  it("does not complete a cancelled image request after rendering", async () => {
    const abort = new AbortController();
    let started!: () => void;
    let finish!: () => void;
    const ready = new Promise<void>((resolve) => {
      started = resolve;
    });
    const pending = new Promise<void>((resolve) => {
      finish = resolve;
    });
    const render = jest.spyOn(RenderService.prototype, "render").mockImplementation(async () => {
      started();
      await pending;
      return { protocol: "mcp", frameIndex: 0, width: 1, height: 1, png: Buffer.alloc(0) };
    });
    try {
      const request = client.getPrompt(
        { name: "tla-create-animations", arguments: { svgContent: '<svg width="1" height="1"/>' } },
        { signal: abort.signal },
      );
      await ready;
      abort.abort();
      await expect(request).rejects.toThrow();
      finish();
    } finally {
      finish();
      render.mockRestore();
    }
  });

  nativeImageTest("renders hostile SVG as a safe PNG without embedding source", async () => {
    const result = await client.getPrompt({
      name: "tla-create-animations",
      arguments: {
        svgContent:
          '<svg width="16" height="16"><script>throw 1</script><image href="file:///etc/passwd"/><rect width="16" height="16" fill="red"/></svg>',
      },
    });
    expect(result.messages[2].content.type).toBe("image");
    expect(JSON.stringify(result)).not.toContain("file:///etc/passwd");
  });

  it.each(["", "invalid", '<svg width="5000" height="1"/>', " ".repeat(1024 * 1024 + 1)])(
    "fails image prompts with invalid or oversized sources",
    async (svgContent) => {
      await expect(
        client.getPrompt({ name: "tla-create-animations", arguments: { svgContent } }),
      ).rejects.toThrow();
    },
  );
});
