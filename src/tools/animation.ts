/**
 * MCP tool handler for terminal graphics rendering.
 *
 * Spec: docs/tla-animations/spec.md
 * Contract: docs/tla-animations/contract.md
 *
 * @implements REQ-ARCH-001 (MCP tool with 3 operations: detect, render, frameCount)
 * @module tools/animation
 */

import { z } from "zod";
import { McpServer, ResourceTemplate } from "@modelcontextprotocol/sdk/server/mcp.js";
import { McpError, ErrorCode, type CallToolResult } from "@modelcontextprotocol/sdk/types.js";
import { randomUUID } from "crypto";
import * as fs from "fs/promises";
import { ServerConfig } from "../types";
import { DetectionService } from "./animation/DetectionService";
import { RenderService, NATIVE_SOURCE_LIMIT } from "./animation/RenderService";
import { FrameCountService } from "./animation/FrameCountService";
import { isAnimationError, type NativeRenderResult } from "./animation/types";
import { resolveAndValidatePath } from "../utils/paths";
import { createAnimationError } from "./animation/errors";
import { registerTool } from "./shared/tool-registration";

/**
 * Zod schema for AnimView validation
 * @implements REQ-RENDER-004
 * NORMATIVE: SC-ANIM-016
 */
const SvgElementSchema = z
  .object({
    shape: z.enum(["rect", "circle", "text", "line", "path", "g"]),
  })
  .passthrough();

const AnimViewSchema = z.object({
  frame: z.string(),
  title: z.string(),
  width: z.number().positive(),
  height: z.number().positive(),
  elements: z.array(SvgElementSchema),
});

/**
 * Zod schema for ASCII config validation
 * @implements REQ-FALLBACK-004
 * NORMATIVE: SC-ANIM-019
 */
const AsciiConfigSchema = z
  .object({
    columns: z.number().min(40).max(200).optional(),
    rows: z.number().min(20).max(60).optional(),
    colorEnabled: z.boolean().optional(),
  })
  .optional();

/**
 * Zod schema for detect operation input
 * @implements REQ-DETECT-001
 */
const DetectRequestSchema = z.object({
  timeout: z.number().positive().optional(),
});

/**
 * Zod schema for render operation input
 * @implements REQ-RENDER-004
 * NORMATIVE: SC-ANIM-012, SC-ANIM-016, SC-ANIM-023
 */
const RenderRequestSchema = z
  .object({
    protocol: z.enum(["kitty", "iterm2", "ascii", "browser", "mcp"]),
    useCase: z.enum(["live", "static", "trace"]),
    frameIndex: z.number().nonnegative(),
    animView: AnimViewSchema.optional(),
    svgContent: z.string().optional(),
    svgFilePath: z.string().optional(),
    traceDirectory: z.string().optional(),
    filePattern: z.string().optional(),
    asciiConfig: AsciiConfigSchema,
    fallbackPreference: z.enum(["ascii", "browser", "prompt", "none"]).optional(),
  })
  .refine(
    (data) => {
      const sources = [data.animView, data.svgContent, data.svgFilePath].filter(Boolean).length;
      return sources === 1;
    },
    { message: "Exactly one of animView, svgContent, or svgFilePath must be provided" },
  );

async function readNativeSource(
  fileName: string,
  workingDir: string | null,
  signal?: AbortSignal,
): Promise<string> {
  const filePath = resolveAndValidatePath(fileName, workingDir);
  if (!(await fs.lstat(filePath)).isFile())
    throw new Error("SVG source must be a regular file, not a symlink");
  const realPath = resolveAndValidatePath(await fs.realpath(filePath), workingDir);
  if (signal?.aborted) throw new Error("Animation render was cancelled");
  const file = await fs.open(
    realPath,
    fs.constants.O_RDONLY | (fs.constants.O_NOFOLLOW || 0) | (fs.constants.O_NONBLOCK || 0),
  );
  try {
    const stat = await file.stat();
    if (!stat.isFile() || stat.size > NATIVE_SOURCE_LIMIT)
      throw new Error("SVG source must be a regular file of at most 1MB");
    const buffer = Buffer.alloc(NATIVE_SOURCE_LIMIT + 1);
    let bytesRead = 0;
    while (bytesRead < buffer.length) {
      if (signal?.aborted) throw new Error("Animation render was cancelled");
      const next = await file.read(buffer, bytesRead, buffer.length - bytesRead, bytesRead);
      if (!next.bytesRead) break;
      bytesRead += next.bytesRead;
    }
    if (bytesRead > NATIVE_SOURCE_LIMIT) throw new Error("SVG source exceeds 1MB limit");
    return buffer.subarray(0, bytesRead).toString("utf8");
  } finally {
    await file.close();
  }
}

/**
 * Zod schema for frameCount operation input
 * @implements REQ-ARCH-008
 */
const FrameCountRequestSchema = z.object({
  traceDirectory: z.string(),
  filePattern: z.string().optional(),
});

/**
 * Format MCP response content
 * @param data - Data to format
 * @param isError - Whether this is an error response
 */
function formatResponse(
  data: unknown,
  isError: boolean = false,
): { content: { type: "text"; text: string }[]; isError?: boolean } {
  return {
    content: [{ type: "text" as const, text: JSON.stringify(data, null, 2) }],
    ...(isError && { isError: true }),
  };
}

/**
 * Handle detect operation
 * @implements REQ-DETECT-001, REQ-DETECT-002, REQ-DETECT-003
 * @invariant INV-DETECT-001 (detection completes within 500ms)
 * @param params - Detection parameters (optional timeout)
 * @returns DetectionResult or AnimationError
 */
export async function handleDetect(
  params: unknown,
): Promise<{ content: { type: "text"; text: string }[]; isError?: boolean }> {
  try {
    const validated = DetectRequestSchema.parse(params ?? {});
    const service = new DetectionService();
    const result = await service.detect(validated.timeout);

    if (isAnimationError(result)) {
      return formatResponse(result, true);
    }

    return formatResponse(result);
  } catch (error) {
    if (error instanceof z.ZodError) {
      const animError = createAnimationError("RENDER_FAILED", {
        specificError: `Invalid parameters: ${error.errors.map((e) => e.message).join(", ")}`,
      });
      return formatResponse(animError, true);
    }
    const animError = createAnimationError("RENDER_FAILED", {
      specificError: error instanceof Error ? error.message : String(error),
    });
    return formatResponse(animError, true);
  }
}

/**
 * Handle render operation
 * @implements REQ-RENDER-001, REQ-RENDER-002, REQ-RENDER-003, REQ-RENDER-004, REQ-RENDER-005, REQ-RENDER-006
 * @implements REQ-ARCH-005 (no re-detection in render)
 * @invariant INV-RENDER-001 (frame size never exceeds 1MB)
 * @invariant INV-INPUT-001 (exactly one source)
 * @param params - Render parameters
 * @returns RenderResult or AnimationError
 */
export async function handleRender(
  params: unknown,
): Promise<{ content: { type: "text"; text: string }[]; isError?: boolean }> {
  try {
    const validated = RenderRequestSchema.parse(params);
    const service = new RenderService();

    // Build RenderInput from validated params
    const renderInput = {
      operation: "render" as const,
      protocol: validated.protocol,
      useCase: validated.useCase,
      frameIndex: validated.frameIndex,
      animView: validated.animView,
      svgContent: validated.svgContent,
      svgFilePath: validated.svgFilePath,
      traceDirectory: validated.traceDirectory,
      filePattern: validated.filePattern,
      asciiConfig: validated.asciiConfig,
      fallbackPreference: validated.fallbackPreference,
    };

    const result = await service.render(renderInput);

    if (isAnimationError(result)) {
      return formatResponse(result, true);
    }

    return formatResponse(result);
  } catch (error) {
    if (error instanceof z.ZodError) {
      // Check if it's the mutual exclusivity refinement error
      const refineError = error.errors.find((e) => e.code === "custom");
      if (refineError) {
        const animError = createAnimationError("INVALID_ANIMVIEW", {
          specificError: refineError.message,
        });
        return formatResponse(animError, true);
      }

      const animError = createAnimationError("RENDER_FAILED", {
        specificError: `Invalid parameters: ${error.errors.map((e) => e.message).join(", ")}`,
      });
      return formatResponse(animError, true);
    }
    const animError = createAnimationError("RENDER_FAILED", {
      specificError: error instanceof Error ? error.message : String(error),
    });
    return formatResponse(animError, true);
  }
}

/**
 * Handle frameCount operation
 * @implements REQ-ARCH-008
 * NORMATIVE: SC-ANIM-026
 * @param params - FrameCount parameters (traceDirectory, filePattern)
 * @returns FrameCountResult or AnimationError
 */
export async function handleFrameCount(
  params: unknown,
): Promise<{ content: { type: "text"; text: string }[]; isError?: boolean }> {
  try {
    const validated = FrameCountRequestSchema.parse(params);
    const service = new FrameCountService();
    const result = await service.frameCount(validated.traceDirectory, validated.filePattern);

    if (isAnimationError(result)) {
      return formatResponse(result, true);
    }

    return formatResponse(result);
  } catch (error) {
    if (error instanceof z.ZodError) {
      const animError = createAnimationError("FILE_NOT_FOUND", {
        specificError: `Invalid parameters: ${error.errors.map((e) => e.message).join(", ")}`,
      });
      return formatResponse(animError, true);
    }
    const animError = createAnimationError("RENDER_FAILED", {
      specificError: error instanceof Error ? error.message : String(error),
    });
    return formatResponse(animError, true);
  }
}

/**
 * Register animation tools with the MCP server
 * @implements REQ-ARCH-001 (MCP tool with detect/render/frameCount operations)
 * @param server - MCP server instance
 * @param config - Server configuration for native SVG source path confinement
 */
// @implements REQ-REVIEW-002, SCN-REVIEW-002-01
export async function registerAnimationTools(
  server: McpServer,
  config: ServerConfig,
): Promise<void> {
  const frames = new Map<string, NativeRenderResult>();
  const persistent = !config.http || Boolean(config.httpSession);
  let closed = false;
  const frameUri = (id: string, format: string) => `tlaplus://animation/${id}/${format}`;
  const formats = (frame: NativeRenderResult) =>
    frame.svg ? ["frame.png", "frame.svg"] : ["frame.png"];
  const previousClose = server.server.onclose;
  server.server.onclose = () => {
    closed = true;
    frames.clear();
    previousClose?.();
  };
  server.resource(
    "animation-frames",
    new ResourceTemplate("tlaplus://animation/{frameId}/{format}", {
      list: async () => ({
        resources: [...frames].flatMap(([id, frame]) =>
          formats(frame).map((format) => ({
            uri: frameUri(id, format),
            name: `Frame ${frame.frameIndex} ${format}`,
            mimeType: format === "frame.png" ? "image/png" : "image/svg+xml",
          })),
        ),
      }),
      complete: {
        frameId: (value) => [...frames.keys()].filter((id) => id.startsWith(value)),
        format: (value, context) => {
          const frame = frames.get(context?.arguments?.frameId ?? "");
          return (frame ? formats(frame) : []).filter((format) => format.startsWith(value));
        },
      },
    }),
    {
      description:
        "Recent animation frames rendered on this connection; at most eight frames are retained.",
    },
    async (uri, variables) => {
      const frame =
        typeof variables.frameId === "string" ? frames.get(variables.frameId) : undefined;
      if (
        !frame ||
        typeof variables.format !== "string" ||
        !formats(frame).includes(variables.format)
      ) {
        throw new McpError(ErrorCode.InvalidParams, "Unknown or expired animation frame");
      }
      return {
        contents:
          variables.format === "frame.png"
            ? [{ uri: uri.href, mimeType: "image/png", blob: frame.png.toString("base64") }]
            : [{ uri: uri.href, mimeType: "image/svg+xml", text: frame.svg ?? "" }],
      };
    },
  );
  const renderNative = async (params: unknown, signal?: AbortSignal): Promise<CallToolResult> => {
    try {
      if (closed || signal?.aborted) throw new Error("Animation render was cancelled");
      const input = RenderRequestSchema.parse(params);
      if (!Number.isSafeInteger(input.frameIndex))
        throw new Error("Native frameIndex must be a nonnegative safe integer");
      const source = input.svgFilePath
        ? {
            ...input,
            svgContent: await readNativeSource(input.svgFilePath, config.workingDir, signal),
            svgFilePath: undefined,
          }
        : input;
      const result = await new RenderService().render({ ...source, operation: "render" });
      if (closed || signal?.aborted) throw new Error("Animation render was cancelled");
      if (isAnimationError(result)) return formatResponse(result, true);
      if (result.protocol !== "mcp") throw new Error("Native rendering requires protocol mcp");
      const id = randomUUID();
      if (persistent) {
        frames.set(id, result);
        if (frames.size > 8) {
          const oldest = frames.keys().next().value;
          if (oldest !== undefined) frames.delete(oldest);
        }
        void server.server.sendResourceListChanged().catch(() => {});
      }
      const pngUri = frameUri(id, "frame.png"),
        svgUri = result.svg ? frameUri(id, "frame.svg") : undefined;
      const content: CallToolResult["content"] = [
        {
          type: "text",
          text: JSON.stringify({
            frameIndex: result.frameIndex,
            width: result.width,
            height: result.height,
            ...(persistent ? { pngUri, svgUri } : {}),
            embeddedOnly: !persistent,
            svgOmitted: !result.svg,
          }),
        },
        { type: "image", mimeType: "image/png", data: result.png.toString("base64") },
      ];
      if (result.svg && svgUri)
        content.push({
          type: "resource",
          resource: { uri: svgUri, mimeType: "image/svg+xml", text: result.svg },
        });
      return { content };
    } catch (error) {
      return formatResponse(
        createAnimationError("RENDER_FAILED", {
          specificError: error instanceof Error ? error.message : String(error),
        }),
        true,
      );
    }
  };
  // Tool 1: Detect terminal graphics capabilities
  registerTool(
    server,
    "tlaplus_mcp_animation_detect",
    "Detect terminal graphics capabilities. Returns information about supported graphics protocols (Kitty, iTerm2), terminal multiplexer status (tmux/screen), and passthrough configuration. Use this to determine the best rendering protocol before calling render.",
    {
      timeout: z
        .number()
        .positive()
        .optional()
        .describe("Optional timeout in milliseconds (default: 500)"),
    },
    async ({ timeout }: { timeout?: number }) => {
      return handleDetect({ timeout });
    },
  );

  // Tool 2: Render animation frame
  registerTool(
    server,
    "tlaplus_mcp_animation_render",
    "Render an animation frame as a native MCP PNG image with an inert SVG resource (protocol mcp), or as Kitty, iTerm2, ASCII, or browser output. Accepts exactly one AnimView, SVG string, or SVG file path. Native frames are limited to 4194304 pixels and 1MB per PNG/SVG; unsafe SVG is omitted. Resources retain the latest eight frames on this connection. For traces, call frameCount first, then render an explicit SVG file.",
    {
      protocol: z
        .enum(["kitty", "iterm2", "ascii", "browser", "mcp"])
        .describe("Target rendering protocol"),
      useCase: z
        .enum(["live", "static", "trace"])
        .describe(
          "Use case context: live (TLC exploration), static (single frame), trace (saved trace files)",
        ),
      frameIndex: z.number().nonnegative().describe("Frame index for navigation"),
      animView: AnimViewSchema.optional().describe("AnimView record from TLA+ (Option A)"),
      svgContent: z.string().optional().describe("Pre-rendered SVG string (Option B)"),
      svgFilePath: z.string().optional().describe("File path to SVG file (Option C)"),
      traceDirectory: z
        .string()
        .optional()
        .describe("Directory containing trace SVG files (metadata only)"),
      filePattern: z.string().optional().describe("Glob pattern for trace files (metadata only)"),
      asciiConfig: AsciiConfigSchema.describe("ASCII rendering configuration"),
      fallbackPreference: z
        .enum(["ascii", "browser", "prompt", "none"])
        .optional()
        .describe("Fallback preference when graphics not available"),
    },
    async (
      params: {
        protocol: "kitty" | "iterm2" | "ascii" | "browser" | "mcp";
        useCase: "live" | "static" | "trace";
        frameIndex: number;
        animView?: unknown;
        svgContent?: string;
        svgFilePath?: string;
        traceDirectory?: string;
        filePattern?: string;
        asciiConfig?: { columns?: number; rows?: number; colorEnabled?: boolean };
        fallbackPreference?: "ascii" | "browser" | "prompt" | "none";
      },
      context?: { signal?: AbortSignal },
    ) => {
      return params.protocol === "mcp"
        ? renderNative(params, context?.signal)
        : handleRender(params);
    },
  );

  // Tool 3: Get frame count for trace navigation
  registerTool(
    server,
    "tlaplus_mcp_animation_frameCount",
    "Get the number of animation frames in a trace directory for navigation. Returns count and sorted list of file paths. Call this before rendering trace frames to discover available files, then use render with explicit svgFilePath for each frame.",
    {
      traceDirectory: z.string().describe("Directory containing trace SVG files"),
      filePattern: z
        .string()
        .optional()
        .describe('Glob pattern for trace files (default: "*_anim_*.svg")'),
    },
    async ({ traceDirectory, filePattern }: { traceDirectory: string; filePattern?: string }) => {
      return handleFrameCount({ traceDirectory, filePattern });
    },
  );
}
