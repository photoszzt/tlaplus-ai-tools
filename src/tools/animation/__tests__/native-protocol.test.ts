import * as fs from "fs";
import * as os from "os";
import * as path from "path";
import { execFileSync } from "child_process";
import { Client } from "@modelcontextprotocol/sdk/client/index.js";
import { McpServer } from "@modelcontextprotocol/sdk/server/mcp.js";
import { InMemoryTransport } from "@modelcontextprotocol/sdk/inMemory.js";
import { CallToolResultSchema } from "@modelcontextprotocol/sdk/types.js";
import { registerAnimationTools } from "../../animation";
import { RenderService } from "../RenderService";
import { MINIMAL_CONFIG } from "../../../__tests__/fixtures/config-samples";

let canvasAvailable = false;
try {
  require("@napi-rs/canvas");
  canvasAvailable = true;
} catch {
  /* Optional rasterizer. */
}
const describeWithCanvas = canvasAvailable ? describe : describe.skip;
const svg =
  '<svg xmlns="http://www.w3.org/2000/svg" width="64" height="32"><rect width="20" height="10" fill="red"/></svg>';
const template = "tlaplus://animation/{frameId}/{format}";

describeWithCanvas("Native animation through the real MCP SDK", () => {
  let dir: string;
  let server: McpServer;
  let client: Client;
  beforeEach(async () => {
    dir = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), "native-animation-")));
    server = new McpServer({ name: "native-animation", version: "1" });
    await registerAnimationTools(server, { ...MINIMAL_CONFIG, workingDir: dir });
    client = new Client({ name: "native-animation-client", version: "1" });
    const [a, b] = InMemoryTransport.createLinkedPair();
    await server.connect(b);
    await client.connect(a);
  });
  afterEach(async () => {
    await client.close();
    await server.close();
    fs.rmSync(dir, { recursive: true, force: true });
  });
  const render = async (extra = {}) =>
    CallToolResultSchema.parse(
      await client.callTool({
        name: "tlaplus_mcp_animation_render",
        arguments: { protocol: "mcp", useCase: "static", frameIndex: 0, svgContent: svg, ...extra },
      }),
    );

  it("returns PNG pixels, embedded SVG, readable binary/text resources, and completion", async () => {
    const result = await render();
    expect(result.isError).not.toBe(true);
    const image = result.content.find((item) => item.type === "image");
    if (!image || image.type !== "image") throw new Error("Expected PNG content");
    const png = Buffer.from(image.data, "base64");
    expect(png.subarray(0, 8).equals(Buffer.from([137, 80, 78, 71, 13, 10, 26, 10]))).toBe(true);
    expect([png.readUInt32BE(16), png.readUInt32BE(20)]).toEqual([64, 32]);
    const embedded = result.content.find((item) => item.type === "resource");
    if (!embedded || embedded.type !== "resource" || !("text" in embedded.resource))
      throw new Error("Expected embedded SVG");
    expect(embedded.resource.mimeType).toBe("image/svg+xml");
    expect(embedded.resource.text).toContain("<rect");
    const pngUri = embedded.resource.uri.replace("frame.svg", "frame.png");
    const binary = (await client.readResource({ uri: pngUri })).contents[0];
    expect("blob" in binary && binary.blob).toBe(image.data);
    const text = (await client.readResource({ uri: embedded.resource.uri })).contents[0];
    expect("text" in text && text.text).toBe(embedded.resource.text);
    expect(
      (await client.listResourceTemplates()).resourceTemplates.some(
        (item) => item.uriTemplate === template,
      ),
    ).toBe(true);
    const frameId = new URL(pngUri).pathname.split("/")[1];
    expect(
      (
        await client.complete({
          ref: { type: "ref/resource", uri: template },
          argument: { name: "frameId", value: frameId.slice(0, 6) },
        })
      ).completion.values,
    ).toContain(frameId);
    expect(
      (
        await client.complete({
          ref: { type: "ref/resource", uri: template },
          argument: { name: "format", value: "frame." },
          context: { arguments: { frameId } },
        })
      ).completion.values,
    ).toEqual(["frame.png", "frame.svg"]);
  });

  it("omits active SVG and prevents reading arbitrary resource paths", async () => {
    const result = await render({
      svgContent:
        '<svg width="64" height="32"><script>steal()</script><rect width="20" height="10"/></svg>',
    });
    expect(result.isError).not.toBe(true);
    expect(result.content.some((item) => item.type === "image")).toBe(true);
    expect(result.content.some((item) => item.type === "resource")).toBe(false);
    const resources = (await client.listResources()).resources;
    expect(resources).toHaveLength(1);
    expect(resources[0].mimeType).toBe("image/png");
    await expect(
      client.readResource({ uri: resources[0].uri.replace("frame.png", "frame.svg") }),
    ).rejects.toThrow();
    await expect(
      client.readResource({ uri: "tlaplus://animation/../../etc/passwd" }),
    ).rejects.toThrow();
  });

  it("confines SVG file sources, including symlinks", async () => {
    const outside = fs.mkdtempSync(path.join(os.tmpdir(), "native-outside-"));
    try {
      const source = path.join(outside, "frame.svg");
      fs.writeFileSync(source, svg);
      const result = await render({ svgContent: undefined, svgFilePath: source });
      expect(result.isError).toBe(true);
      expect(result.content[0].type === "text" && result.content[0].text).toContain(
        "Access denied",
      );
      if (process.platform !== "win32") {
        const alias = path.join(dir, "alias.svg");
        fs.symlinkSync(source, alias);
        expect((await render({ svgContent: undefined, svgFilePath: alias })).isError).toBe(true);
      }
      const local = path.join(dir, "frame.svg");
      fs.writeFileSync(local, svg);
      expect((await render({ svgContent: undefined, svgFilePath: local })).isError).not.toBe(true);
      if (process.platform !== "win32") {
        const localAlias = path.join(dir, "local-alias.svg");
        fs.symlinkSync(local, localAlias);
        expect((await render({ svgContent: undefined, svgFilePath: localAlias })).isError).toBe(
          true,
        );
      }
      expect(fs.readdirSync(dir)).toEqual([
        ...(process.platform === "win32" ? [] : ["alias.svg"]),
        "frame.svg",
        ...(process.platform === "win32" ? [] : ["local-alias.svg"]),
      ]);
    } finally {
      fs.rmSync(outside, { recursive: true, force: true });
    }
  });

  (process.platform === "win32" ? it.skip : it)(
    "rejects a source replaced by a symlink immediately before open",
    async () => {
      const fsPromises: typeof import("fs/promises") = require("fs/promises");
      const originalOpen = fsPromises.open;
      const outside = fs.mkdtempSync(path.join(os.tmpdir(), "native-race-"));
      const local = path.join(dir, "racing.svg"),
        foreign = path.join(outside, "foreign.svg");
      fs.writeFileSync(local, svg);
      fs.writeFileSync(foreign, svg);
      const raced = jest.spyOn(fsPromises, "open").mockImplementation(async (...args) => {
        if (args[0] === local) {
          fs.unlinkSync(local);
          fs.symlinkSync(foreign, local);
        }
        return originalOpen(...args);
      });
      try {
        const result = await render({ svgContent: undefined, svgFilePath: local });
        expect(result.isError).toBe(true);
        expect((await client.listResources()).resources).toEqual([]);
      } finally {
        raced.mockRestore();
        fs.rmSync(outside, { recursive: true, force: true });
      }
    },
  );

  it("rejects non-regular and oversized source files", async () => {
    const oversized = path.join(dir, "oversized.svg");
    fs.writeFileSync(oversized, " ".repeat(1024 * 1024 + 1));
    expect((await render({ svgContent: undefined, svgFilePath: oversized })).isError).toBe(true);
    expect((await render({ svgContent: undefined, svgFilePath: dir })).isError).toBe(true);
    if (process.platform !== "win32") {
      const fifo = path.join(dir, "pipe.svg");
      execFileSync("mkfifo", [fifo]);
      expect((await render({ svgContent: undefined, svgFilePath: fifo })).isError).toBe(true);
    }
  });

  it("evicts old frames and isolates resources between MCP connections", async () => {
    let firstUri = "";
    for (let frameIndex = 0; frameIndex < 9; frameIndex++) {
      await render({ frameIndex });
      if (!frameIndex) firstUri = (await client.listResources()).resources[0].uri;
    }
    expect((await client.listResources()).resources).toHaveLength(16);
    await expect(client.readResource({ uri: firstUri })).rejects.toThrow();
    const otherServer = new McpServer({ name: "other-animation", version: "1" });
    const otherClient = new Client({ name: "other-client", version: "1" });
    try {
      await registerAnimationTools(otherServer, { ...MINIMAL_CONFIG, workingDir: dir });
      const [a, b] = InMemoryTransport.createLinkedPair();
      await otherServer.connect(b);
      await otherClient.connect(a);
      expect((await otherClient.listResources()).resources).toEqual([]);
      await expect(
        otherClient.readResource({ uri: (await client.listResources()).resources[0].uri }),
      ).rejects.toThrow();
    } finally {
      await otherClient.close();
      await otherServer.close();
    }
  });

  it("does not retain a frame after request cancellation", async () => {
    const actualRender = RenderService.prototype.render;
    let started = () => {};
    const rendering = new Promise<void>((resolve) => {
      started = resolve;
    });
    const pause = jest
      .spyOn(RenderService.prototype, "render")
      .mockImplementation(async function (this: RenderService, input) {
        started();
        await new Promise((resolve) => setTimeout(resolve, 50));
        return actualRender.call(this, input);
      });
    const controller = new AbortController();
    try {
      const call = client.callTool(
        {
          name: "tlaplus_mcp_animation_render",
          arguments: { protocol: "mcp", useCase: "static", frameIndex: 0, svgContent: svg },
        },
        undefined,
        { signal: controller.signal },
      );
      await rendering;
      controller.abort();
      await expect(call).rejects.toThrow();
      await new Promise((resolve) => setTimeout(resolve, 100));
      expect((await client.listResources()).resources).toEqual([]);
    } finally {
      pause.mockRestore();
    }
  });

  it("returns only inline content in stateless HTTP mode", async () => {
    const stateless = new McpServer({ name: "stateless-animation", version: "1" });
    const httpClient = new Client({ name: "stateless-client", version: "1" });
    try {
      await registerAnimationTools(stateless, {
        ...MINIMAL_CONFIG,
        http: true,
        httpSession: false,
        workingDir: dir,
      });
      const [a, b] = InMemoryTransport.createLinkedPair();
      await stateless.connect(b);
      await httpClient.connect(a);
      const result = CallToolResultSchema.parse(
        await httpClient.callTool({
          name: "tlaplus_mcp_animation_render",
          arguments: { protocol: "mcp", useCase: "static", frameIndex: 0, svgContent: svg },
        }),
      );
      expect(result.isError).not.toBe(true);
      const metadata = result.content[0];
      if (metadata.type !== "text") throw new Error("Expected frame metadata");
      const parsed = JSON.parse(metadata.text);
      expect(parsed.embeddedOnly).toBe(true);
      expect(parsed).not.toHaveProperty("pngUri");
      expect(parsed).not.toHaveProperty("svgUri");
      expect(result.content.map((item) => item.type)).toEqual(["text", "image", "resource"]);
      expect((await httpClient.listResources()).resources).toEqual([]);
    } finally {
      await httpClient.close();
      await stateless.close();
    }
  });
});
