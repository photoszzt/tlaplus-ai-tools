import { RenderService } from "../RenderService";
import { isAnimationError, type AnimView, type RasterizerService } from "../types";

const view: AnimView = {
  frame: "0",
  title: "Frame",
  width: 64,
  height: 32,
  elements: [{ shape: "rect", x: 0, y: 0, width: 20, height: 10, fill: "red" }],
};

function renderer(png = Buffer.alloc(100)) {
  const rasterizer: RasterizerService = {
    rasterizeSvg: jest.fn().mockResolvedValue(png),
    rasterizeAnimView: jest.fn().mockResolvedValue(png),
  };
  return { service: new RenderService({ rasterizer }), rasterizer };
}

describe("Native animation rendering limits and SVG safety", () => {
  it.each([
    [4097, 1],
    [4096, 4096],
    [Infinity, 1],
    [1.5, 32],
  ])("rejects dimensions %s x %s before rasterizing", async (width, height) => {
    const { service, rasterizer } = renderer();
    const result = await service.render({
      operation: "render",
      protocol: "mcp",
      useCase: "static",
      frameIndex: 0,
      animView: { ...view, width, height },
    });
    expect(isAnimationError(result)).toBe(true);
    expect(rasterizer.rasterizeSvg).not.toHaveBeenCalled();
    expect(rasterizer.rasterizeAnimView).not.toHaveBeenCalled();
  });

  it.each([
    '<svg width="1000000" height="2"/>',
    '<svg viewBox="0 0 1000000 2"/>',
    "<svg/><svg/>",
    `<svg width="64" height="32">${" ".repeat(1024 * 1024)}</svg>`,
    '<!DOCTYPE svg [<!ENTITY secret SYSTEM "file:///etc/passwd">]><svg>&secret;</svg>',
  ])("rejects an oversized or declared SVG before rasterizing", async (svgContent) => {
    const { service, rasterizer } = renderer();
    const result = await service.render({
      operation: "render",
      protocol: "mcp",
      useCase: "static",
      frameIndex: 0,
      svgContent,
    });
    expect(isAnimationError(result)).toBe(true);
    expect(rasterizer.rasterizeSvg).not.toHaveBeenCalled();
    expect(rasterizer.rasterizeAnimView).not.toHaveBeenCalled();
  });

  it("omits active SVG and rasterizes only its supported inert shapes", async () => {
    const { service, rasterizer } = renderer();
    const result = await service.render({
      operation: "render",
      protocol: "mcp",
      useCase: "static",
      frameIndex: 0,
      svgContent:
        '<svg width="64" height="32" onload="steal()"><script>secret</script><image href="https://evil.example"/><rect x="1" width="10" height="10" fill="url(https://evil.example)"/></svg>',
    });
    expect(isAnimationError(result)).toBe(false);
    if (isAnimationError(result) || result.protocol !== "mcp")
      throw new Error("Expected native render");
    expect(result.svg).toBeUndefined();
    expect(rasterizer.rasterizeSvg).not.toHaveBeenCalled();
    expect(rasterizer.rasterizeAnimView).toHaveBeenCalledWith(
      expect.objectContaining({
        elements: [{ shape: "rect", x: 1, width: 10, height: 10 }],
      }),
    );
  });

  it("sanitizes generated AnimView SVG without dropping the frame", async () => {
    const { service, rasterizer } = renderer();
    const result = await service.render({
      operation: "render",
      protocol: "mcp",
      useCase: "static",
      frameIndex: 0,
      animView: {
        ...view,
        title: "<script>title</script>",
        elements: [
          {
            shape: "text",
            text: "<script>text</script>",
            x: 1,
            y: 10,
            onload: "steal()",
            href: "https://evil.example",
            fill: "url(https://evil.example)",
          },
        ],
      },
    });
    if (isAnimationError(result) || result.protocol !== "mcp")
      throw new Error("Expected native render");
    expect(result.svg).toContain("&lt;script&gt;text&lt;/script&gt;");
    expect(result.svg).not.toMatch(/<script|onload|href|evil\.example/);
    expect(rasterizer.rasterizeSvg).toHaveBeenCalledWith(result.svg);
  });

  it("rejects PNG output above the existing 1MB ceiling", async () => {
    const { service } = renderer(Buffer.alloc(1024 * 1024 + 1));
    const result = await service.render({
      operation: "render",
      protocol: "mcp",
      useCase: "static",
      frameIndex: 0,
      animView: view,
    });
    expect(isAnimationError(result) && result.error).toBe("FRAME_TOO_LARGE");
  });
});
