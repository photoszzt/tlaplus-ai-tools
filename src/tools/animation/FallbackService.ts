/**
 * Fallback service for ASCII art and browser rendering.
 *
 * Spec: docs/tla-animations/spec.md
 * Contract: docs/tla-animations/contract.md
 *
 * @module animation/FallbackService
 */

import * as fs from 'fs/promises';
import * as path from 'path';
import * as os from 'os';

import {
  AnimView,
  AsciiConfig,
  AsciiRenderResult,
  BrowserRenderResult,
  AnimationError,
  SvgElement,
  FileSystemService
} from './types';
import { createAnimationError, errorService } from './errors';

/**
 * ASCII box-drawing characters
 * @implements REQ-FALLBACK-003
 * NORMATIVE: SC-ANIM-009
 */
const BOX_CHARS = {
  TOP_LEFT: '\u250C',         // ┌
  TOP_RIGHT: '\u2510',        // ┐
  BOTTOM_LEFT: '\u2514',      // └
  BOTTOM_RIGHT: '\u2518',     // ┘
  HORIZONTAL: '\u2500',       // ─
  VERTICAL: '\u2502',         // │
  FILLED_CIRCLE: '\u25CF',    // ●
  OUTLINE_CIRCLE: '\u25CB',   // ○
  SMALL_CIRCLE: 'O',
  MEDIUM_CIRCLE_LEFT: '(',
  MEDIUM_CIRCLE_RIGHT: ')'
};

/**
 * ASCII canvas constraints
 * @implements REQ-FALLBACK-004
 * NORMATIVE: SC-ANIM-019
 */
const ASCII_CONSTRAINTS = {
  MIN_COLUMNS: 40,
  MAX_COLUMNS: 200,
  DEFAULT_COLUMNS: 80,
  MIN_ROWS: 20,
  MAX_ROWS: 60,
  DEFAULT_ROWS: 24
};

/**
 * Default file system service using Node.js fs module
 */
function createDefaultFileSystem(): FileSystemService {
  return {
    async readFile(filePath: string): Promise<Buffer> {
      return fs.readFile(filePath);
    },
    async writeFile(filePath: string, data: Buffer | string): Promise<void> {
      await fs.writeFile(filePath, data);
    },
    async exists(filePath: string): Promise<boolean> {
      try {
        await fs.access(filePath);
        return true;
      } catch {
        return false;
      }
    },
    async glob(pattern: string, cwd: string): Promise<string[]> {
      const files = await fs.readdir(cwd);
      const regex = globToRegex(pattern);
      const matched = files
        .filter(f => regex.test(f))
        .map(f => path.join(cwd, f))
        .sort();
      return matched;
    }
  };
}

/**
 * Convert simple glob pattern to regex
 */
function globToRegex(pattern: string): RegExp {
  const escaped = pattern
    .replace(/[.+^${}()|[\]\\]/g, '\\$&')
    .replace(/\*/g, '.*')
    .replace(/\?/g, '.');
  return new RegExp(`^${escaped}$`);
}

/**
 * Escape XML special characters
 */
function escapeXml(str: string): string {
  return str
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;')
    .replace(/'/g, '&apos;');
}

/**
 * Convert AnimView to SVG string
 * @param animView - Animation view record
 * @returns SVG content string
 */
function animViewToSvg(animView: AnimView): string {
  const elements = animView.elements.map(el => svgElementToString(el)).join('\n  ');
  return `<svg xmlns="http://www.w3.org/2000/svg" width="${animView.width}" height="${animView.height}">
  <title>${escapeXml(animView.title)}</title>
  ${elements}
</svg>`;
}

/**
 * Convert SvgElement to SVG string
 */
function svgElementToString(element: SvgElement): string {
  const { shape, ...attrs } = element;
  const attrStrings = Object.entries(attrs)
    .filter(([, v]) => v !== undefined)
    .map(([k, v]) => `${k}="${escapeXml(String(v))}"`)
    .join(' ');

  if (shape === 'g') {
    return `<g ${attrStrings}></g>`;
  }
  if (shape === 'text') {
    const text = (attrs.text as string) || '';
    const filteredAttrs = Object.entries(attrs)
      .filter(([k, v]) => k !== 'text' && v !== undefined)
      .map(([k, v]) => `${k}="${escapeXml(String(v))}"`)
      .join(' ');
    return `<text ${filteredAttrs}>${escapeXml(text)}</text>`;
  }
  return `<${shape} ${attrStrings}/>`;
}

/**
 * Get ANSI color code for a color string
 * @implements REQ-FALLBACK-005
 * NORMATIVE: SC-ANIM-020
 */
function getAnsiColor(color: string): string {
  // Basic color mapping to ANSI 256-color codes
  const colorMap: Record<string, number> = {
    'black': 0,
    'red': 1,
    'green': 2,
    'yellow': 3,
    'blue': 21,
    'magenta': 5,
    'cyan': 6,
    'white': 7,
    '#000000': 0,
    '#ff0000': 196,
    '#00ff00': 46,
    '#0000ff': 21,
    '#ffff00': 226,
    '#ff00ff': 201,
    '#00ffff': 51,
    '#ffffff': 231,
    '#3498db': 39,
    'orange': 208
  };

  const lowerColor = color.toLowerCase();
  if (colorMap[lowerColor] !== undefined) {
    return `\x1b[38;5;${colorMap[lowerColor]}m`;
  }

  // Try to parse hex color
  if (color.startsWith('#') && color.length === 7) {
    const r = parseInt(color.slice(1, 3), 16);
    const g = parseInt(color.slice(3, 5), 16);
    const b = parseInt(color.slice(5, 7), 16);
    // Convert to 256-color palette (approximate)
    const code = 16 + 36 * Math.round(r / 51) + 6 * Math.round(g / 51) + Math.round(b / 51);
    return `\x1b[38;5;${code}m`;
  }

  return '';
}

/**
 * Detect if terminal supports 256-color or truecolor
 * @implements REQ-FALLBACK-005
 * NORMATIVE: SC-ANIM-020
 */
function detectColorSupport(): boolean {
  const term = process.env.TERM || '';
  return term.includes('256color') || term.includes('truecolor');
}

/**
 * Render a single SVG element to ASCII canvas
 * @implements REQ-FALLBACK-003
 * NORMATIVE: SC-ANIM-009
 */
function renderAsciiElement(
  canvas: string[][],
  element: SvgElement,
  scaleX: number,
  scaleY: number,
  colorEnabled: boolean
): void {
  const { shape } = element;
  const fillColor = element.fill as string | undefined;
  const ansiColor = colorEnabled && fillColor ? getAnsiColor(fillColor) : '';
  const resetColor = colorEnabled && fillColor ? '\x1b[0m' : '';

  switch (shape) {
    case 'rect':
      renderAsciiRect(canvas, element, scaleX, scaleY, ansiColor, resetColor);
      break;
    case 'circle':
      renderAsciiCircle(canvas, element, scaleX, scaleY, ansiColor, resetColor);
      break;
    case 'line':
      renderAsciiLine(canvas, element, scaleX, scaleY, ansiColor, resetColor);
      break;
    case 'text':
      renderAsciiText(canvas, element, scaleX, scaleY, ansiColor, resetColor);
      break;
    // 'path' and 'g' are complex and not fully rendered in ASCII
    default:
      break;
  }
}

/**
 * Render rectangle in ASCII
 * @implements REQ-FALLBACK-003
 * NORMATIVE: SC-ANIM-009
 * Uses Unicode box-drawing characters:
 * - Top-left corner: \u250C
 * - Top-right corner: \u2510
 * - Bottom-left corner: \u2514
 * - Bottom-right corner: \u2518
 * - Horizontal line: \u2500
 * - Vertical line: \u2502
 */
function renderAsciiRect(
  canvas: string[][],
  element: SvgElement,
  scaleX: number,
  scaleY: number,
  ansiColor: string,
  resetColor: string
): void {
  const x = Math.floor((element.x as number) * scaleX);
  const y = Math.floor((element.y as number) * scaleY);
  const w = Math.max(2, Math.floor((element.width as number) * scaleX));
  const h = Math.max(2, Math.floor((element.height as number) * scaleY));

  const maxRow = canvas.length;
  const maxCol = canvas[0]?.length ?? 0;

  // Top-left corner: \u250C
  if (y >= 0 && y < maxRow && x >= 0 && x < maxCol) {
    canvas[y][x] = ansiColor + BOX_CHARS.TOP_LEFT + resetColor;
  }
  // Top-right corner: \u2510
  if (y >= 0 && y < maxRow && x + w - 1 >= 0 && x + w - 1 < maxCol) {
    canvas[y][x + w - 1] = ansiColor + BOX_CHARS.TOP_RIGHT + resetColor;
  }
  // Bottom-left corner: \u2514
  if (y + h - 1 >= 0 && y + h - 1 < maxRow && x >= 0 && x < maxCol) {
    canvas[y + h - 1][x] = ansiColor + BOX_CHARS.BOTTOM_LEFT + resetColor;
  }
  // Bottom-right corner: \u2518
  if (y + h - 1 >= 0 && y + h - 1 < maxRow && x + w - 1 >= 0 && x + w - 1 < maxCol) {
    canvas[y + h - 1][x + w - 1] = ansiColor + BOX_CHARS.BOTTOM_RIGHT + resetColor;
  }

  // Top and bottom horizontal lines: \u2500
  for (let i = x + 1; i < x + w - 1; i++) {
    if (i >= 0 && i < maxCol) {
      if (y >= 0 && y < maxRow) {
        canvas[y][i] = ansiColor + BOX_CHARS.HORIZONTAL + resetColor;
      }
      if (y + h - 1 >= 0 && y + h - 1 < maxRow) {
        canvas[y + h - 1][i] = ansiColor + BOX_CHARS.HORIZONTAL + resetColor;
      }
    }
  }

  // Left and right vertical lines: \u2502
  for (let j = y + 1; j < y + h - 1; j++) {
    if (j >= 0 && j < maxRow) {
      if (x >= 0 && x < maxCol) {
        canvas[j][x] = ansiColor + BOX_CHARS.VERTICAL + resetColor;
      }
      if (x + w - 1 >= 0 && x + w - 1 < maxCol) {
        canvas[j][x + w - 1] = ansiColor + BOX_CHARS.VERTICAL + resetColor;
      }
    }
  }
}

/**
 * Render circle in ASCII
 * @implements REQ-FALLBACK-003
 * NORMATIVE: SC-ANIM-009
 * Circle approximation:
 * - Circle (r <= 5): O
 * - Circle (5 < r <= 10): () pair
 * - Circle (r > 10): \u25CF (filled) or \u25CB (outline)
 */
function renderAsciiCircle(
  canvas: string[][],
  element: SvgElement,
  scaleX: number,
  scaleY: number,
  ansiColor: string,
  resetColor: string
): void {
  const cx = Math.floor((element.cx as number) * scaleX);
  const cy = Math.floor((element.cy as number) * scaleY);
  const r = (element.r as number) || 5;
  const filled = element.fill !== 'none' && element.fill !== undefined;

  const maxRow = canvas.length;
  const maxCol = canvas[0]?.length ?? 0;

  // Per SC-ANIM-009:
  // Circle (r <= 5) -> 'O'
  // Circle (5 < r <= 10) -> '()' pair
  // Circle (r > 10) -> filled/outline unicode
  if (r <= 5) {
    if (cy >= 0 && cy < maxRow && cx >= 0 && cx < maxCol) {
      canvas[cy][cx] = ansiColor + BOX_CHARS.SMALL_CIRCLE + resetColor;
    }
  } else if (r <= 10) {
    if (cy >= 0 && cy < maxRow && cx - 1 >= 0 && cx - 1 < maxCol) {
      canvas[cy][cx - 1] = ansiColor + BOX_CHARS.MEDIUM_CIRCLE_LEFT + resetColor;
    }
    if (cy >= 0 && cy < maxRow && cx >= 0 && cx < maxCol) {
      canvas[cy][cx] = ansiColor + ' ' + resetColor;
    }
    if (cy >= 0 && cy < maxRow && cx + 1 >= 0 && cx + 1 < maxCol) {
      canvas[cy][cx + 1] = ansiColor + BOX_CHARS.MEDIUM_CIRCLE_RIGHT + resetColor;
    }
  } else {
    // r > 10: use filled or outline unicode circle
    const circleChar = filled ? BOX_CHARS.FILLED_CIRCLE : BOX_CHARS.OUTLINE_CIRCLE;
    if (cy >= 0 && cy < maxRow && cx >= 0 && cx < maxCol) {
      canvas[cy][cx] = ansiColor + circleChar + resetColor;
    }
  }
}

/**
 * Render line in ASCII
 * @implements REQ-FALLBACK-003
 * NORMATIVE: SC-ANIM-009
 */
function renderAsciiLine(
  canvas: string[][],
  element: SvgElement,
  scaleX: number,
  scaleY: number,
  ansiColor: string,
  resetColor: string
): void {
  const x1 = Math.floor((element.x1 as number) * scaleX);
  const y1 = Math.floor((element.y1 as number) * scaleY);
  const x2 = Math.floor((element.x2 as number) * scaleX);
  const y2 = Math.floor((element.y2 as number) * scaleY);

  const maxRow = canvas.length;
  const maxCol = canvas[0]?.length ?? 0;

  // Simple line drawing using Bresenham-like approach
  const dx = Math.abs(x2 - x1);
  const dy = Math.abs(y2 - y1);
  const sx = x1 < x2 ? 1 : -1;
  const sy = y1 < y2 ? 1 : -1;
  let err = dx - dy;

  let x = x1;
  let y = y1;

  const char = dx > dy ? BOX_CHARS.HORIZONTAL : BOX_CHARS.VERTICAL;

  while (true) {
    if (y >= 0 && y < maxRow && x >= 0 && x < maxCol) {
      canvas[y][x] = ansiColor + char + resetColor;
    }
    if (x === x2 && y === y2) break;
    const e2 = 2 * err;
    if (e2 > -dy) {
      err -= dy;
      x += sx;
    }
    if (e2 < dx) {
      err += dx;
      y += sy;
    }
  }
}

/**
 * Render text in ASCII
 * @implements REQ-FALLBACK-003
 */
function renderAsciiText(
  canvas: string[][],
  element: SvgElement,
  scaleX: number,
  scaleY: number,
  ansiColor: string,
  resetColor: string
): void {
  const x = Math.floor((element.x as number) * scaleX);
  const y = Math.floor((element.y as number) * scaleY);
  const text = (element.text as string) || '';

  const maxRow = canvas.length;
  const maxCol = canvas[0]?.length ?? 0;

  if (y >= 0 && y < maxRow) {
    for (let i = 0; i < text.length; i++) {
      const col = x + i;
      if (col >= 0 && col < maxCol) {
        canvas[y][col] = ansiColor + text[i] + resetColor;
      }
    }
  }
}

/**
 * Options for FallbackService
 */
export interface FallbackServiceOptions {
  /** File system service (for testing) */
  fileSystem?: FileSystemService;
}

/**
 * FallbackService provides ASCII art and browser fallback rendering.
 * @implements REQ-FALLBACK-001, REQ-FALLBACK-002, REQ-FALLBACK-003, REQ-FALLBACK-004, REQ-FALLBACK-005, REQ-FALLBACK-006
 */
export class FallbackService {
  private fileSystem: FileSystemService;

  /**
   * Create fallback service with dependency injection
   * @param options - Fallback service options for testability
   */
  constructor(options: FallbackServiceOptions = {}) {
    this.fileSystem = options.fileSystem ?? createDefaultFileSystem();
  }

  /**
   * Render ASCII art using box-drawing Unicode characters
   * @implements REQ-FALLBACK-003, REQ-FALLBACK-004, REQ-FALLBACK-005
   * NORMATIVE: SC-ANIM-009, SC-ANIM-019, SC-ANIM-020
   *
   * Uses exact Unicode characters from SC-ANIM-009:
   * - Rectangles: \u250C \u2510 \u2514 \u2518 \u2500 \u2502
   * - Circles: O (r<=5), () (r<=10), \u25CF/\u25CB (full)
   *
   * Canvas limits per SC-ANIM-019:
   * - MIN: 40x20
   * - MAX: 200x60
   * - DEFAULT: 80x24
   *
   * ANSI colors per SC-ANIM-020
   *
   * @param animView - Animation view record
   * @param config - ASCII rendering configuration (optional)
   * @returns ASCII render result
   */
  renderAscii(animView: AnimView, config?: AsciiConfig): AsciiRenderResult {
    // Apply constraints per SC-ANIM-019
    const effectiveConfig = config ?? {};

    // Enforce canvas size constraints: MIN 40x20, MAX 200x60, DEFAULT 80x24
    const cols = Math.max(
      ASCII_CONSTRAINTS.MIN_COLUMNS,
      Math.min(ASCII_CONSTRAINTS.MAX_COLUMNS, effectiveConfig.columns ?? ASCII_CONSTRAINTS.DEFAULT_COLUMNS)
    );
    const rows = Math.max(
      ASCII_CONSTRAINTS.MIN_ROWS,
      Math.min(ASCII_CONSTRAINTS.MAX_ROWS, effectiveConfig.rows ?? ASCII_CONSTRAINTS.DEFAULT_ROWS)
    );

    // Color enabled by default, but check terminal support per SC-ANIM-020
    const colorEnabled = effectiveConfig.colorEnabled ?? detectColorSupport();

    // Create ASCII canvas
    const canvas: string[][] = Array(rows).fill(null).map(() => Array(cols).fill(' '));

    // Scale factors from pixel coordinates to character coordinates
    const scaleX = cols / animView.width;
    const scaleY = rows / animView.height;

    // Render each element using box-drawing characters per SC-ANIM-009
    for (const element of animView.elements) {
      renderAsciiElement(canvas, element, scaleX, scaleY, colorEnabled);
    }

    // Convert canvas to string
    const output = canvas.map(row => row.join('')).join('\n');

    return {
      output,
      protocol: 'ascii',
      frameIndex: 0, // Will be set by caller
      dimensions: { cols, rows }
    };
  }

  /**
   * Save animation to file for browser viewing
   * @implements REQ-FALLBACK-001, REQ-FALLBACK-002
   * NORMATIVE: SC-ANIM-007
   *
   * Saves SVG file to temp or specified path and returns file path.
   * File naming: tlaplus_anim_frame_<frameIndex>.html
   *
   * @param animViewOrSvg - AnimView record or SVG string content
   * @param outputPath - Optional output path (defaults to temp directory)
   * @param frameIndex - Frame index for file naming (default: 0)
   * @returns Browser render result with file path
   */
  async renderBrowser(
    animViewOrSvg: AnimView | string,
    outputPath?: string,
    frameIndex: number = 0
  ): Promise<BrowserRenderResult | AnimationError> {
    let svgContent: string;

    // Convert AnimView to SVG if needed
    if (typeof animViewOrSvg === 'string') {
      svgContent = animViewOrSvg;
    } else {
      svgContent = animViewToSvg(animViewOrSvg);
    }

    // Create HTML wrapper for easy viewing
    const htmlContent = `<!DOCTYPE html>
<html>
<head>
  <meta charset="utf-8">
  <title>TLA+ Animation Frame ${frameIndex}</title>
  <style>
    body { margin: 0; display: flex; justify-content: center; align-items: center; min-height: 100vh; background: #1a1a1a; }
    svg { max-width: 100%; max-height: 100vh; }
  </style>
</head>
<body>
${svgContent}
</body>
</html>`;

    // Determine output path
    let filePath: string;
    if (outputPath) {
      filePath = outputPath;
    } else {
      // Save to temp directory with standard naming
      const tempDir = os.tmpdir();
      const fileName = `tlaplus_anim_frame_${frameIndex}.html`;
      filePath = path.join(tempDir, fileName);
    }

    try {
      await this.fileSystem.writeFile(filePath, htmlContent);

      return {
        filePath,
        protocol: 'browser',
        frameIndex
      };
    } catch (error) {
      const message = error instanceof Error ? error.message : String(error);
      return createAnimationError('RENDER_FAILED', { specificError: `Failed to save file: ${message}` });
    }
  }

  /**
   * Check if user has declined all fallbacks and return appropriate error
   * @implements REQ-FALLBACK-006
   * NORMATIVE: SC-ANIM-021
   * @returns NO_FALLBACK_AVAILABLE error
   */
  noFallbackAvailable(): AnimationError {
    return errorService.noFallbackAvailable();
  }
}

/**
 * Factory function for creating fallback service with dependency injection
 * @param fileSystem - File system abstraction (for testing)
 * @returns FallbackService instance
 */
export function createFallbackService(
  fileSystem?: FileSystemService
): FallbackService {
  return new FallbackService({ fileSystem });
}
