/**
 * Type definitions for terminal graphics auto-detection and animation rendering.
 *
 * Spec: docs/tla-animations/spec.md
 * Contract: docs/tla-animations/contract.md
 *
 * @module animation/types
 */

/**
 * Supported terminal graphics protocols
 * @implements REQ-DETECT-003
 * NORMATIVE: SC-ANIM-003
 */
export type GraphicsProtocol = 'kitty' | 'iterm2' | 'none';

/**
 * Supported terminal multiplexers
 * @implements REQ-DETECT-003
 * NORMATIVE: SC-ANIM-003
 */
export type Multiplexer = 'tmux' | 'screen' | 'none';

/**
 * How terminal detection was performed
 * @implements REQ-DETECT-003
 * NORMATIVE: SC-ANIM-003
 */
export type DetectionMethod = 'env' | 'query' | 'probe';

/**
 * Confidence level in detection result
 * @implements REQ-DETECT-003
 * NORMATIVE: SC-ANIM-003
 */
export type ConfidenceLevel = 'high' | 'medium' | 'low';

/**
 * Available fallback options
 * @implements REQ-FALLBACK-001
 * NORMATIVE: SC-ANIM-007
 */
export type FallbackOption = 'ascii' | 'browser';

/**
 * Environment variables captured during detection
 * @implements REQ-DETECT-003
 * NORMATIVE: SC-ANIM-003
 */
export interface DetectionEnvironment {
  TERM?: string;
  TERM_PROGRAM?: string;
  KITTY_WINDOW_ID?: string;
  TMUX?: string;
  STY?: string;
  LC_TERMINAL?: string;
}

/**
 * Result of terminal graphics capability detection
 * @implements REQ-DETECT-003
 * NORMATIVE: SC-ANIM-003
 */
export interface DetectionResult {
  /** Detected graphics protocol capability */
  protocol: GraphicsProtocol;

  /** Detected terminal multiplexer */
  multiplexer: Multiplexer;

  /** Whether graphics passthrough is enabled (for multiplexers) */
  passthroughEnabled: boolean;

  /** Whether passthrough was verified via active probe (always false for v1) */
  passthroughVerified: boolean;

  /** Available fallback options */
  fallbackAvailable: FallbackOption[];

  /** How detection was performed */
  detectionMethod: DetectionMethod;

  /** Confidence in detection result */
  confidence: ConfidenceLevel;

  /** Raw environment variables for diagnostics */
  environment: DetectionEnvironment;
}

/**
 * Supported SVG element shapes
 * @implements REQ-RENDER-004
 * NORMATIVE: SC-ANIM-016
 */
export type SvgShape = 'rect' | 'circle' | 'text' | 'line' | 'path' | 'g';

/**
 * SVG element record from TLA+ animation
 * @implements REQ-RENDER-004
 * NORMATIVE: SC-ANIM-016
 */
export interface SvgElement {
  /** Shape type */
  shape: SvgShape;

  /** Shape-specific attributes (x, y, width, height, cx, cy, r, etc.) */
  [key: string]: unknown;
}

/**
 * AnimView record from TLA+ (parsed from tlc_explore output)
 * @implements REQ-RENDER-004
 * NORMATIVE: SC-ANIM-016
 */
export interface AnimView {
  /** Frame identifier */
  frame: string;

  /** Animation title */
  title: string;

  /** Canvas width in pixels */
  width: number;

  /** Canvas height in pixels */
  height: number;

  /** SVG element records */
  elements: SvgElement[];
}

/**
 * Render use case
 * @implements REQ-ARCH-003
 * NORMATIVE: SC-ANIM-012
 */
export type RenderUseCase = 'live' | 'static' | 'trace';

/**
 * Protocol to use for rendering
 * @implements REQ-ARCH-005
 * NORMATIVE: SC-ANIM-023
 */
export type RenderProtocol = 'kitty' | 'iterm2' | 'ascii' | 'browser';

/**
 * Fallback preference
 * @implements REQ-FALLBACK-002
 * NORMATIVE: SC-ANIM-008
 */
export type FallbackPreference = 'ascii' | 'browser' | 'prompt' | 'none';

/**
 * ASCII rendering configuration
 * @implements REQ-FALLBACK-004
 * NORMATIVE: SC-ANIM-019
 */
export interface AsciiConfig {
  /** Canvas width in columns. Default: 80, Min: 40, Max: 200 */
  columns?: number;

  /** Canvas height in rows. Default: 24, Min: 20, Max: 60 */
  rows?: number;

  /** Whether to use ANSI color codes. Default: true */
  colorEnabled?: boolean;
}

/**
 * Render operation input
 * @implements REQ-RENDER-004, REQ-ARCH-003, REQ-ARCH-005
 * NORMATIVE: SC-ANIM-012, SC-ANIM-016, SC-ANIM-017, SC-ANIM-018, SC-ANIM-023
 */
export interface RenderInput {
  /** Operation type (always "render") */
  operation: 'render';

  /** Target protocol (Claude's decision, MCP trusts it) */
  protocol: RenderProtocol;

  /** Use case context */
  useCase: RenderUseCase;

  /** Frame index for navigation */
  frameIndex: number;

  // Exactly one of the following three MUST be provided:

  /** AnimView record from TLA+ (Option A) */
  animView?: AnimView;

  /** Pre-rendered SVG string (Option B) */
  svgContent?: string;

  /** File path to SVG file (Option C) */
  svgFilePath?: string;

  // Optional metadata for trace use case (NOT used for file resolution):
  // NOTE: These fields are for context/logging only. Claude uses frameCount to get
  // the file list, then passes explicit svgFilePath to each render call.

  /** Directory containing trace SVG files (metadata only) */
  traceDirectory?: string;

  /** Glob pattern for trace files (metadata only) */
  filePattern?: string;

  // Optional configuration:

  /** ASCII rendering configuration */
  asciiConfig?: AsciiConfig;

  /** Fallback preference when graphics not available */
  fallbackPreference?: FallbackPreference;
}

/**
 * Successful render result for terminal graphics (Kitty/iTerm2)
 * @implements REQ-RENDER-002
 * NORMATIVE: SC-ANIM-005
 */
export interface TerminalRenderResult {
  /** Escape sequence to output to terminal */
  output: string;

  /** Protocol used */
  protocol: 'kitty' | 'iterm2';

  /** Frame index rendered */
  frameIndex: number;
}

/**
 * Successful render result for ASCII art
 * @implements REQ-FALLBACK-003
 * NORMATIVE: SC-ANIM-009
 */
export interface AsciiRenderResult {
  /** ASCII art output (may include ANSI color codes) */
  output: string;

  /** Protocol used */
  protocol: 'ascii';

  /** Frame index rendered */
  frameIndex: number;

  /** Actual dimensions of ASCII output */
  dimensions: {
    cols: number;
    rows: number;
  };
}

/**
 * Successful render result for browser fallback
 * @implements REQ-FALLBACK-001
 * NORMATIVE: SC-ANIM-007
 */
export interface BrowserRenderResult {
  /** File path to saved HTML/SVG file */
  filePath: string;

  /** Protocol used */
  protocol: 'browser';

  /** Frame index rendered */
  frameIndex: number;
}

/**
 * Union type for all successful render results
 */
export type RenderResult = TerminalRenderResult | AsciiRenderResult | BrowserRenderResult;

/**
 * Frame count response for trace navigation
 * @implements REQ-ARCH-008
 * NORMATIVE: SC-ANIM-012 (trace use case)
 */
export interface FrameCountResult {
  /** Number of frames in trace */
  count: number;

  /** List of frame file paths */
  files: string[];
}

/**
 * Animation-specific error codes
 * @implements REQ-ERROR-001
 * NORMATIVE: SC-ANIM-014
 */
export type AnimationErrorCode =
  | 'DETECTION_TIMEOUT'
  | 'UNKNOWN_TERMINAL'
  | 'PASSTHROUGH_NOT_ENABLED'
  | 'RENDER_FAILED'
  | 'FRAME_TOO_LARGE'
  | 'INVALID_ANIMVIEW'
  | 'NO_FALLBACK_AVAILABLE'
  | 'FILE_NOT_FOUND'
  | 'INVALID_SVG';

/**
 * Error response structure
 * @implements REQ-ERROR-001
 * NORMATIVE: SC-ANIM-014, SC-ANIM-021
 * @invariant INV-ERROR-001 (remediation array must be non-empty)
 */
export interface AnimationError {
  /** Error code for programmatic handling */
  error: AnimationErrorCode;

  /** Human-readable error message */
  message: string;

  /** Actionable remediation steps (MUST be non-empty per INV-ERROR-001) */
  remediation: string[];
}

/**
 * Frame count operation input
 * @implements REQ-ARCH-008
 */
export interface FrameCountInput {
  /** Operation type (always "frameCount") */
  operation: 'frameCount';

  /** Directory containing trace files */
  traceDirectory: string;

  /** Glob pattern for trace files (default: "*_anim_*.svg") */
  filePattern?: string;
}

/**
 * Detection service options for testability
 * @implements REQ-DETECT-001, REQ-DETECT-002
 */
export interface DetectionServiceOptions {
  /** Function to read environment variables (for testing) */
  envReader?: () => DetectionEnvironment;

  /** Function to read tmux config (for testing) */
  tmuxConfigReader?: () => Promise<boolean>;

  /** Detection timeout in milliseconds (default: 500) */
  timeoutMs?: number;
}

/**
 * File system abstraction for testing
 */
export interface FileSystemService {
  readFile(path: string): Promise<Buffer>;
  writeFile(path: string, data: Buffer | string): Promise<void>;
  exists(path: string): Promise<boolean>;
  glob(pattern: string, cwd: string): Promise<string[]>;
}

/**
 * Rasterizer service abstraction for testing
 */
export interface RasterizerService {
  /**
   * Rasterize AnimView to PNG
   * @param animView - Animation view record with elements
   * @returns PNG data as Buffer
   */
  rasterizeAnimView(animView: AnimView): Promise<Buffer>;

  /**
   * Rasterize SVG string to PNG
   * @param svgContent - SVG content string
   * @returns PNG data as Buffer
   */
  rasterizeSvg(svgContent: string): Promise<Buffer>;
}

/**
 * Render service options for testability
 */
export interface RenderServiceOptions {
  /** Rasterizer service (for testing) */
  rasterizer?: RasterizerService;

  /** File system service (for testing) */
  fileSystem?: FileSystemService;
}

/**
 * Type guard for AnimationError
 */
export function isAnimationError(value: unknown): value is AnimationError {
  if (typeof value !== 'object' || value === null) {
    return false;
  }
  const obj = value as Record<string, unknown>;
  return (
    typeof obj.error === 'string' &&
    typeof obj.message === 'string' &&
    Array.isArray(obj.remediation) &&
    obj.remediation.length > 0 &&
    obj.remediation.every((r: unknown) => typeof r === 'string')
  );
}

/**
 * Type guard for RenderResult
 */
export function isRenderResult(value: unknown): value is RenderResult {
  if (typeof value !== 'object' || value === null) {
    return false;
  }
  const obj = value as Record<string, unknown>;
  if (typeof obj.protocol !== 'string' || typeof obj.frameIndex !== 'number') {
    return false;
  }
  if (obj.protocol === 'browser') {
    return typeof obj.filePath === 'string';
  }
  if (obj.protocol === 'ascii') {
    return (
      typeof obj.output === 'string' &&
      typeof obj.dimensions === 'object' &&
      obj.dimensions !== null
    );
  }
  if (obj.protocol === 'kitty' || obj.protocol === 'iterm2') {
    return typeof obj.output === 'string';
  }
  return false;
}
