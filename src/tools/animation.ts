/**
 * MCP tool handler for terminal graphics rendering.
 *
 * Spec: docs/tla-animations/spec.md
 * Contract: docs/tla-animations/contract.md
 *
 * @implements REQ-ARCH-001 (MCP tool with 3 operations: detect, render, frameCount)
 * @module tools/animation
 */

import { z } from 'zod';
import { ServerConfig } from '../types';
import { DetectionService } from './animation/DetectionService';
import { RenderService } from './animation/RenderService';
import { FrameCountService } from './animation/FrameCountService';
import {
  isAnimationError
} from './animation/types';
import { createAnimationError } from './animation/errors';

/**
 * Zod schema for AnimView validation
 * @implements REQ-RENDER-004
 * NORMATIVE: SC-ANIM-016
 */
const SvgElementSchema = z.object({
  shape: z.enum(['rect', 'circle', 'text', 'line', 'path', 'g'])
}).passthrough();

const AnimViewSchema = z.object({
  frame: z.string(),
  title: z.string(),
  width: z.number().positive(),
  height: z.number().positive(),
  elements: z.array(SvgElementSchema)
});

/**
 * Zod schema for ASCII config validation
 * @implements REQ-FALLBACK-004
 * NORMATIVE: SC-ANIM-019
 */
const AsciiConfigSchema = z.object({
  columns: z.number().min(40).max(200).optional(),
  rows: z.number().min(20).max(60).optional(),
  colorEnabled: z.boolean().optional()
}).optional();

/**
 * Zod schema for detect operation input
 * @implements REQ-DETECT-001
 */
const DetectRequestSchema = z.object({
  timeout: z.number().positive().optional()
});

/**
 * Zod schema for render operation input
 * @implements REQ-RENDER-004
 * NORMATIVE: SC-ANIM-012, SC-ANIM-016, SC-ANIM-023
 */
const RenderRequestSchema = z.object({
  protocol: z.enum(['kitty', 'iterm2', 'ascii', 'browser']),
  useCase: z.enum(['live', 'static', 'trace']),
  frameIndex: z.number().nonnegative(),
  animView: AnimViewSchema.optional(),
  svgContent: z.string().optional(),
  svgFilePath: z.string().optional(),
  traceDirectory: z.string().optional(),
  filePattern: z.string().optional(),
  asciiConfig: AsciiConfigSchema,
  fallbackPreference: z.enum(['ascii', 'browser', 'prompt', 'none']).optional()
}).refine(
  (data) => {
    const sources = [data.animView, data.svgContent, data.svgFilePath].filter(Boolean).length;
    return sources === 1;
  },
  { message: 'Exactly one of animView, svgContent, or svgFilePath must be provided' }
);

/**
 * Zod schema for frameCount operation input
 * @implements REQ-ARCH-008
 */
const FrameCountRequestSchema = z.object({
  traceDirectory: z.string(),
  filePattern: z.string().optional()
});

/**
 * Format MCP response content
 * @param data - Data to format
 * @param isError - Whether this is an error response
 */
function formatResponse(data: unknown, isError: boolean = false): { content: { type: string; text: string }[]; isError?: boolean } {
  return {
    content: [{ type: 'text', text: JSON.stringify(data, null, 2) }],
    ...(isError && { isError: true })
  };
}

/**
 * Handle detect operation
 * @implements REQ-DETECT-001, REQ-DETECT-002, REQ-DETECT-003
 * @invariant INV-DETECT-001 (detection completes within 500ms)
 * @param params - Detection parameters (optional timeout)
 * @returns DetectionResult or AnimationError
 */
export async function handleDetect(params: unknown): Promise<{ content: { type: string; text: string }[]; isError?: boolean }> {
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
      const animError = createAnimationError('RENDER_FAILED', {
        specificError: `Invalid parameters: ${error.errors.map(e => e.message).join(', ')}`
      });
      return formatResponse(animError, true);
    }
    const animError = createAnimationError('RENDER_FAILED', {
      specificError: error instanceof Error ? error.message : String(error)
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
export async function handleRender(params: unknown): Promise<{ content: { type: string; text: string }[]; isError?: boolean }> {
  try {
    const validated = RenderRequestSchema.parse(params);
    const service = new RenderService();

    // Build RenderInput from validated params
    const renderInput = {
      operation: 'render' as const,
      protocol: validated.protocol,
      useCase: validated.useCase,
      frameIndex: validated.frameIndex,
      animView: validated.animView,
      svgContent: validated.svgContent,
      svgFilePath: validated.svgFilePath,
      traceDirectory: validated.traceDirectory,
      filePattern: validated.filePattern,
      asciiConfig: validated.asciiConfig,
      fallbackPreference: validated.fallbackPreference
    };

    const result = await service.render(renderInput);

    if (isAnimationError(result)) {
      return formatResponse(result, true);
    }

    return formatResponse(result);
  } catch (error) {
    if (error instanceof z.ZodError) {
      // Check if it's the mutual exclusivity refinement error
      const refineError = error.errors.find(e => e.code === 'custom');
      if (refineError) {
        const animError = createAnimationError('INVALID_ANIMVIEW', {
          specificError: refineError.message
        });
        return formatResponse(animError, true);
      }

      const animError = createAnimationError('RENDER_FAILED', {
        specificError: `Invalid parameters: ${error.errors.map(e => e.message).join(', ')}`
      });
      return formatResponse(animError, true);
    }
    const animError = createAnimationError('RENDER_FAILED', {
      specificError: error instanceof Error ? error.message : String(error)
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
export async function handleFrameCount(params: unknown): Promise<{ content: { type: string; text: string }[]; isError?: boolean }> {
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
      const animError = createAnimationError('FILE_NOT_FOUND', {
        specificError: `Invalid parameters: ${error.errors.map(e => e.message).join(', ')}`
      });
      return formatResponse(animError, true);
    }
    const animError = createAnimationError('RENDER_FAILED', {
      specificError: error instanceof Error ? error.message : String(error)
    });
    return formatResponse(animError, true);
  }
}

/**
 * Register animation tools with the MCP server
 * @implements REQ-ARCH-001 (MCP tool with detect/render/frameCount operations)
 * @param server - MCP server instance
 * @param _config - Server configuration (unused, reserved for future use)
 */
export async function registerAnimationTools(
  server: any,
  _config: ServerConfig
): Promise<void> {
  // Tool 1: Detect terminal graphics capabilities
  server.tool(
    'animation_detect',
    'Detect terminal graphics capabilities. Returns information about supported graphics protocols (Kitty, iTerm2), terminal multiplexer status (tmux/screen), and passthrough configuration. Use this to determine the best rendering protocol before calling render.',
    {
      timeout: z.number().positive().optional().describe('Optional timeout in milliseconds (default: 500)')
    },
    async ({ timeout }: { timeout?: number }) => {
      return handleDetect({ timeout });
    }
  );

  // Tool 2: Render animation frame
  server.tool(
    'animation_render',
    'Render a single animation frame to the specified protocol format (Kitty, iTerm2, ASCII art, or browser fallback). Accepts animation data as AnimView record, SVG content string, or SVG file path. Exactly one source must be provided. For trace visualization, call frameCount first to get the file list, then render each frame with explicit svgFilePath.',
    {
      protocol: z.enum(['kitty', 'iterm2', 'ascii', 'browser']).describe('Target rendering protocol'),
      useCase: z.enum(['live', 'static', 'trace']).describe('Use case context: live (TLC exploration), static (single frame), trace (saved trace files)'),
      frameIndex: z.number().nonnegative().describe('Frame index for navigation'),
      animView: AnimViewSchema.optional().describe('AnimView record from TLA+ (Option A)'),
      svgContent: z.string().optional().describe('Pre-rendered SVG string (Option B)'),
      svgFilePath: z.string().optional().describe('File path to SVG file (Option C)'),
      traceDirectory: z.string().optional().describe('Directory containing trace SVG files (metadata only)'),
      filePattern: z.string().optional().describe('Glob pattern for trace files (metadata only)'),
      asciiConfig: AsciiConfigSchema.describe('ASCII rendering configuration'),
      fallbackPreference: z.enum(['ascii', 'browser', 'prompt', 'none']).optional().describe('Fallback preference when graphics not available')
    },
    async (params: {
      protocol: 'kitty' | 'iterm2' | 'ascii' | 'browser';
      useCase: 'live' | 'static' | 'trace';
      frameIndex: number;
      animView?: unknown;
      svgContent?: string;
      svgFilePath?: string;
      traceDirectory?: string;
      filePattern?: string;
      asciiConfig?: { columns?: number; rows?: number; colorEnabled?: boolean };
      fallbackPreference?: 'ascii' | 'browser' | 'prompt' | 'none';
    }) => {
      return handleRender(params);
    }
  );

  // Tool 3: Get frame count for trace navigation
  server.tool(
    'animation_frameCount',
    'Get the number of animation frames in a trace directory for navigation. Returns count and sorted list of file paths. Call this before rendering trace frames to discover available files, then use render with explicit svgFilePath for each frame.',
    {
      traceDirectory: z.string().describe('Directory containing trace SVG files'),
      filePattern: z.string().optional().describe('Glob pattern for trace files (default: "*_anim_*.svg")')
    },
    async ({ traceDirectory, filePattern }: { traceDirectory: string; filePattern?: string }) => {
      return handleFrameCount({ traceDirectory, filePattern });
    }
  );
}
