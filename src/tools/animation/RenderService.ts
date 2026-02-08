/**
 * Render service for animation frame rendering.
 *
 * Spec: docs/tla-animations/spec.md
 * Contract: docs/tla-animations/contract.md
 *
 * @module animation/RenderService
 */

import * as fs from 'fs/promises';
import * as path from 'path';
import * as os from 'os';

import {
  RenderInput,
  RenderResult,
  TerminalRenderResult,
  AsciiRenderResult,
  BrowserRenderResult,
  FrameCountResult,
  AnimationError,
  AnimView,
  AsciiConfig,
  RenderServiceOptions,
  RasterizerService,
  FileSystemService,
  SvgElement,
  isAnimationError
} from './types';
import { createAnimationError, ErrorService, errorService } from './errors';

/**
 * Frame size limit in bytes (1MB)
 * @invariant INV-RENDER-001 (frame size limit enforcement)
 * NORMATIVE: CON-ANIM-005, SC-ANIM-024
 */
const FRAME_SIZE_LIMIT = 1024 * 1024;

/**
 * Default file pattern for trace files
 */
const DEFAULT_FILE_PATTERN = '*_anim_*.svg';

/**
 * ASCII box-drawing characters
 * @implements REQ-FALLBACK-003
 * NORMATIVE: SC-ANIM-009
 */
const BOX_CHARS = {
  TOP_LEFT: '\u250C',     // ┌
  TOP_RIGHT: '\u2510',    // ┐
  BOTTOM_LEFT: '\u2514',  // └
  BOTTOM_RIGHT: '\u2518', // ┘
  HORIZONTAL: '\u2500',   // ─
  VERTICAL: '\u2502',     // │
  FILLED_CIRCLE: '\u25CF', // ●
  OUTLINE_CIRCLE: '\u25CB', // ○
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
      // Simple glob implementation for *_anim_*.svg pattern
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
 * Canvas module reference for lazy loading
 * @implements design.md Section 11.3 (lazy loading)
 */
let canvasModule: typeof import('@napi-rs/canvas') | null = null;

/**
 * Get canvas module with lazy loading
 * Per design.md Section 11.3, lazy-load to avoid startup impact
 * Uses @napi-rs/canvas which is a pure Rust implementation without system dependencies
 * @returns Canvas module
 */
async function getCanvas(): Promise<typeof import('@napi-rs/canvas')> {
  if (!canvasModule) {
    canvasModule = await import('@napi-rs/canvas');
  }
  return canvasModule;
}

/**
 * Default rasterizer service using node-canvas
 * @implements REQ-RENDER-005, REQ-RENDER-006
 * NORMATIVE: design.md Section 3.8
 */
function createDefaultRasterizer(): RasterizerService {
  return {
    async rasterizeAnimView(animView: AnimView): Promise<Buffer> {
      // REQ-RENDER-005: AnimView direct rasterization
      // Per design.md Section 3.8: AnimView elements drawn directly to canvas
      return rasterizeAnimViewToPng(animView);
    },
    async rasterizeSvg(svgContent: string): Promise<Buffer> {
      // REQ-RENDER-006: SVG conversion at render time
      // Per design.md Section 3.8: SVG parsed and rendered to canvas
      const dimensions = extractSvgDimensions(svgContent);
      return rasterizeSvgToPng(svgContent, dimensions.width, dimensions.height);
    }
  };
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
    .filter(([_, v]) => v !== undefined)
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
 * Extract dimensions from SVG content
 */
function extractSvgDimensions(svgContent: string): { width: number; height: number } {
  const widthMatch = svgContent.match(/width=["'](\d+)["']/);
  const heightMatch = svgContent.match(/height=["'](\d+)["']/);
  return {
    width: widthMatch ? parseInt(widthMatch[1], 10) : 200,
    height: heightMatch ? parseInt(heightMatch[1], 10) : 100
  };
}

/**
 * Rasterize AnimView directly to PNG using node-canvas
 * @implements REQ-RENDER-005
 * NORMATIVE: design.md Section 3.8
 * AnimView elements are drawn directly to canvas
 * @param animView - Animation view record with elements
 * @returns PNG data as Buffer
 */
async function rasterizeAnimViewToPng(animView: AnimView): Promise<Buffer> {
  const canvas = await getCanvas();
  const cvs = canvas.createCanvas(animView.width, animView.height);
  const ctx = cvs.getContext('2d');

  // Set default background (white)
  ctx.fillStyle = '#ffffff';
  ctx.fillRect(0, 0, animView.width, animView.height);

  // Draw each element directly to canvas
  for (const element of animView.elements) {
    await drawElementToCanvas(ctx, element);
  }

  // Export canvas to PNG buffer per design.md Section 3.8
  return cvs.toBuffer('image/png');
}

/**
 * Draw a single SvgElement to canvas context
 * @implements REQ-RENDER-005
 * NORMATIVE: design.md Section 3.8
 * @param ctx - Canvas 2D rendering context
 * @param element - SVG element to draw
 */
async function drawElementToCanvas(
  ctx: import('@napi-rs/canvas').SKRSContext2D,
  element: SvgElement
): Promise<void> {
  const { shape } = element;

  // Get fill and stroke from element
  const fill = element.fill as string | undefined;
  const stroke = element.stroke as string | undefined;
  const strokeWidth = (element['stroke-width'] as number) || 1;

  // Set styles
  if (fill && fill !== 'none') {
    ctx.fillStyle = fill;
  }
  if (stroke && stroke !== 'none') {
    ctx.strokeStyle = stroke;
    ctx.lineWidth = strokeWidth;
  }

  switch (shape) {
    case 'rect':
      drawRectToCanvas(ctx, element, fill, stroke);
      break;
    case 'circle':
      drawCircleToCanvas(ctx, element, fill, stroke);
      break;
    case 'line':
      drawLineToCanvas(ctx, element, stroke);
      break;
    case 'text':
      drawTextToCanvas(ctx, element, fill);
      break;
    case 'path':
      await drawPathToCanvas(ctx, element, fill, stroke);
      break;
    case 'g':
      // Group element - no direct drawing, children would be processed separately
      break;
  }
}

/**
 * Draw rectangle to canvas
 */
function drawRectToCanvas(
  ctx: import('@napi-rs/canvas').SKRSContext2D,
  element: SvgElement,
  fill: string | undefined,
  stroke: string | undefined
): void {
  const x = (element.x as number) || 0;
  const y = (element.y as number) || 0;
  const width = (element.width as number) || 0;
  const height = (element.height as number) || 0;
  const rx = (element.rx as number) || 0;
  const ry = (element.ry as number) || rx;

  if (rx > 0 || ry > 0) {
    // Rounded rectangle
    ctx.beginPath();
    ctx.roundRect(x, y, width, height, [rx, ry]);
    if (fill && fill !== 'none') ctx.fill();
    if (stroke && stroke !== 'none') ctx.stroke();
  } else {
    // Regular rectangle
    if (fill && fill !== 'none') ctx.fillRect(x, y, width, height);
    if (stroke && stroke !== 'none') ctx.strokeRect(x, y, width, height);
  }
}

/**
 * Draw circle to canvas
 */
function drawCircleToCanvas(
  ctx: import('@napi-rs/canvas').SKRSContext2D,
  element: SvgElement,
  fill: string | undefined,
  stroke: string | undefined
): void {
  const cx = (element.cx as number) || 0;
  const cy = (element.cy as number) || 0;
  const r = (element.r as number) || 0;

  ctx.beginPath();
  ctx.arc(cx, cy, r, 0, 2 * Math.PI);
  if (fill && fill !== 'none') ctx.fill();
  if (stroke && stroke !== 'none') ctx.stroke();
}

/**
 * Draw line to canvas
 */
function drawLineToCanvas(
  ctx: import('@napi-rs/canvas').SKRSContext2D,
  element: SvgElement,
  stroke: string | undefined
): void {
  const x1 = (element.x1 as number) || 0;
  const y1 = (element.y1 as number) || 0;
  const x2 = (element.x2 as number) || 0;
  const y2 = (element.y2 as number) || 0;

  if (stroke && stroke !== 'none') {
    ctx.beginPath();
    ctx.moveTo(x1, y1);
    ctx.lineTo(x2, y2);
    ctx.stroke();
  }
}

/**
 * Draw text to canvas
 */
function drawTextToCanvas(
  ctx: import('@napi-rs/canvas').SKRSContext2D,
  element: SvgElement,
  fill: string | undefined
): void {
  const x = (element.x as number) || 0;
  const y = (element.y as number) || 0;
  const text = (element.text as string) || '';
  const fontSize = (element['font-size'] as number) || 12;
  const fontFamily = (element['font-family'] as string) || 'sans-serif';
  const fontWeight = (element['font-weight'] as string) || 'normal';
  const textAnchor = (element['text-anchor'] as string) || 'start';

  ctx.font = `${fontWeight} ${fontSize}px ${fontFamily}`;

  // Handle text-anchor alignment
  if (textAnchor === 'middle') {
    ctx.textAlign = 'center';
  } else if (textAnchor === 'end') {
    ctx.textAlign = 'right';
  } else {
    ctx.textAlign = 'left';
  }

  if (fill && fill !== 'none') {
    ctx.fillText(text, x, y);
  }
}

/**
 * Draw path to canvas (basic SVG path support)
 */
async function drawPathToCanvas(
  ctx: import('@napi-rs/canvas').SKRSContext2D,
  element: SvgElement,
  fill: string | undefined,
  stroke: string | undefined
): Promise<void> {
  const d = (element.d as string) || '';
  if (!d) return;

  // Use Path2D for SVG path data from @napi-rs/canvas
  const canvas = await getCanvas();
  const path = new canvas.Path2D(d);

  if (fill && fill !== 'none') ctx.fill(path);
  if (stroke && stroke !== 'none') ctx.stroke(path);
}

/**
 * Rasterize SVG content to PNG buffer using node-canvas
 * @implements REQ-RENDER-006
 * NORMATIVE: design.md Section 3.8
 * SVG parsed and rendered to canvas
 * @param svgContent - SVG content string
 * @param width - Canvas width
 * @param height - Canvas height
 * @returns PNG data as Buffer
 */
async function rasterizeSvgToPng(
  svgContent: string,
  width: number,
  height: number
): Promise<Buffer> {
  const canvas = await getCanvas();
  const cvs = canvas.createCanvas(width, height);
  const ctx = cvs.getContext('2d');

  // Set default background (white)
  ctx.fillStyle = '#ffffff';
  ctx.fillRect(0, 0, width, height);

  // Convert SVG to data URL and load as image
  // node-canvas supports loading SVG via loadImage
  const svgBuffer = Buffer.from(svgContent, 'utf-8');

  try {
    const img = await canvas.loadImage(svgBuffer);
    ctx.drawImage(img, 0, 0, width, height);
  } catch {
    // If SVG loading fails, parse and render elements manually
    const animView = svgToAnimView(svgContent, width, height);
    for (const element of animView.elements) {
      await drawElementToCanvas(ctx, element);
    }
  }

  // Export canvas to PNG buffer per design.md Section 3.8
  return cvs.toBuffer('image/png');
}

/**
 * Parse SVG content to AnimView structure for manual rendering
 * Used as fallback when direct SVG loading fails
 */
function svgToAnimView(svgContent: string, width: number, height: number): AnimView {
  const elements: SvgElement[] = [];

  // Parse rect elements
  const rectRegex = /<rect([^>]*)\/?>|<rect([^>]*)>[^<]*<\/rect>/g;
  let match;
  while ((match = rectRegex.exec(svgContent)) !== null) {
    const attrs = match[1] || match[2];
    elements.push(parseElementAttrsInternal('rect', attrs));
  }

  // Parse circle elements
  const circleRegex = /<circle([^>]*)\/?>|<circle([^>]*)>[^<]*<\/circle>/g;
  while ((match = circleRegex.exec(svgContent)) !== null) {
    const attrs = match[1] || match[2];
    elements.push(parseElementAttrsInternal('circle', attrs));
  }

  // Parse text elements
  const textRegex = /<text([^>]*)>([^<]*)<\/text>/g;
  while ((match = textRegex.exec(svgContent)) !== null) {
    const attrs = match[1];
    const text = match[2];
    const element = parseElementAttrsInternal('text', attrs);
    element.text = text;
    elements.push(element);
  }

  // Parse line elements
  const lineRegex = /<line([^>]*)\/?>|<line([^>]*)>[^<]*<\/line>/g;
  while ((match = lineRegex.exec(svgContent)) !== null) {
    const attrs = match[1] || match[2];
    elements.push(parseElementAttrsInternal('line', attrs));
  }

  // Parse path elements
  const pathRegex = /<path([^>]*)\/?>|<path([^>]*)>[^<]*<\/path>/g;
  while ((match = pathRegex.exec(svgContent)) !== null) {
    const attrs = match[1] || match[2];
    elements.push(parseElementAttrsInternal('path', attrs));
  }

  return {
    frame: '0',
    title: 'SVG Frame',
    width,
    height,
    elements
  };
}

/**
 * Parse SVG element attributes from string (internal helper)
 */
function parseElementAttrsInternal(shape: string, attrsStr: string): SvgElement {
  const element: SvgElement = { shape: shape as SvgElement['shape'] };
  const attrRegex = /([a-zA-Z][a-zA-Z0-9-]*)=["']([^"']*)["']/g;
  let match;
  while ((match = attrRegex.exec(attrsStr)) !== null) {
    const [, name, value] = match;
    // Convert numeric attributes
    if (['x', 'y', 'width', 'height', 'cx', 'cy', 'r', 'x1', 'y1', 'x2', 'y2', 'rx', 'ry', 'font-size', 'stroke-width'].includes(name)) {
      element[name] = parseFloat(value);
    } else {
      element[name] = value;
    }
  }
  return element;
}

/**
 * Render Kitty graphics escape sequence
 * @implements REQ-RENDER-002
 * NORMATIVE: SC-ANIM-005
 * Format: \x1b_Ga=T,f=100,m=0;<base64data>\x1b\\
 */
function renderKitty(pngData: Buffer): string {
  const base64 = pngData.toString('base64');
  return `\x1b_Ga=T,f=100,m=0;${base64}\x1b\\`;
}

/**
 * Render iTerm2 inline image escape sequence
 * @implements REQ-RENDER-002
 * NORMATIVE: SC-ANIM-005
 * Format: \x1b]1337;File=inline=1;size=<bytes>:<base64data>\x07
 */
function renderIterm2(pngData: Buffer): string {
  const base64 = pngData.toString('base64');
  const size = pngData.length;
  return `\x1b]1337;File=inline=1;size=${size}:${base64}\x07`;
}

/**
 * Render ASCII art from AnimView
 * @implements REQ-FALLBACK-003, REQ-FALLBACK-004, REQ-FALLBACK-005
 * NORMATIVE: SC-ANIM-009, SC-ANIM-019, SC-ANIM-020
 */
function renderAscii(animView: AnimView, config: AsciiConfig): AsciiRenderResult {
  // Apply constraints per SC-ANIM-019
  const cols = Math.max(
    ASCII_CONSTRAINTS.MIN_COLUMNS,
    Math.min(ASCII_CONSTRAINTS.MAX_COLUMNS, config.columns ?? ASCII_CONSTRAINTS.DEFAULT_COLUMNS)
  );
  const rows = Math.max(
    ASCII_CONSTRAINTS.MIN_ROWS,
    Math.min(ASCII_CONSTRAINTS.MAX_ROWS, config.rows ?? ASCII_CONSTRAINTS.DEFAULT_ROWS)
  );
  const colorEnabled = config.colorEnabled ?? true;

  // Create ASCII canvas
  const canvas: string[][] = Array(rows).fill(null).map(() => Array(cols).fill(' '));

  // Scale factors
  const scaleX = cols / animView.width;
  const scaleY = rows / animView.height;

  // Render each element
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
 * NORMATIVE: SC-ANIM-009
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

  // Top-left corner
  if (y >= 0 && y < maxRow && x >= 0 && x < maxCol) {
    canvas[y][x] = ansiColor + BOX_CHARS.TOP_LEFT + resetColor;
  }
  // Top-right corner
  if (y >= 0 && y < maxRow && x + w - 1 >= 0 && x + w - 1 < maxCol) {
    canvas[y][x + w - 1] = ansiColor + BOX_CHARS.TOP_RIGHT + resetColor;
  }
  // Bottom-left corner
  if (y + h - 1 >= 0 && y + h - 1 < maxRow && x >= 0 && x < maxCol) {
    canvas[y + h - 1][x] = ansiColor + BOX_CHARS.BOTTOM_LEFT + resetColor;
  }
  // Bottom-right corner
  if (y + h - 1 >= 0 && y + h - 1 < maxRow && x + w - 1 >= 0 && x + w - 1 < maxCol) {
    canvas[y + h - 1][x + w - 1] = ansiColor + BOX_CHARS.BOTTOM_RIGHT + resetColor;
  }

  // Top and bottom horizontal lines
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

  // Left and right vertical lines
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
 * NORMATIVE: SC-ANIM-009
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
    const circleChar = filled ? BOX_CHARS.FILLED_CIRCLE : BOX_CHARS.OUTLINE_CIRCLE;
    if (cy >= 0 && cy < maxRow && cx >= 0 && cx < maxCol) {
      canvas[cy][cx] = ansiColor + circleChar + resetColor;
    }
  }
}

/**
 * Render line in ASCII
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
    'blue': 21, // Brighter blue (256-color)
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
    '#3498db': 39, // Common blue
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
 * Validate RenderInput - ensures exactly one source is provided
 * @implements REQ-RENDER-004
 * @invariant INV-INPUT-001 (exactly one source)
 * NORMATIVE: SC-ANIM-016, SC-ANIM-017, SC-ANIM-018
 */
function validateRenderInput(input: RenderInput): AnimationError | null {
  const sources = [input.animView, input.svgContent, input.svgFilePath].filter(Boolean);

  if (sources.length === 0) {
    return createAnimationError('INVALID_ANIMVIEW', {
      field: 'source (animView, svgContent, or svgFilePath)'
    });
  }

  if (sources.length > 1) {
    return createAnimationError('INVALID_ANIMVIEW', {
      specificError: 'Exactly one of animView, svgContent, or svgFilePath must be provided'
    });
  }

  // Validate AnimView if provided
  if (input.animView) {
    const validationError = validateAnimView(input.animView);
    if (validationError) {
      return validationError;
    }
  }

  return null;
}

/**
 * Validate AnimView structure
 * @implements REQ-RENDER-004
 * NORMATIVE: SC-ANIM-016
 */
function validateAnimView(animView: AnimView): AnimationError | null {
  if (typeof animView.frame !== 'string') {
    return createAnimationError('INVALID_ANIMVIEW', { field: 'frame' });
  }
  if (typeof animView.title !== 'string') {
    return createAnimationError('INVALID_ANIMVIEW', { field: 'title' });
  }
  if (typeof animView.width !== 'number' || animView.width <= 0) {
    return createAnimationError('INVALID_ANIMVIEW', { field: 'width' });
  }
  if (typeof animView.height !== 'number' || animView.height <= 0) {
    return createAnimationError('INVALID_ANIMVIEW', { field: 'height' });
  }
  if (!Array.isArray(animView.elements)) {
    return createAnimationError('INVALID_ANIMVIEW', { field: 'elements' });
  }
  return null;
}

/**
 * RenderService for animation frame rendering
 * @implements REQ-RENDER-001, REQ-RENDER-002, REQ-RENDER-003, REQ-RENDER-004, REQ-RENDER-005, REQ-RENDER-006
 */
export class RenderService {
  private rasterizer: RasterizerService;
  private fileSystem: FileSystemService;
  private errors: ErrorService;

  /**
   * Create render service with dependency injection
   * @param options - Render service options for testability
   */
  constructor(options: RenderServiceOptions = {}) {
    this.rasterizer = options.rasterizer ?? createDefaultRasterizer();
    this.fileSystem = options.fileSystem ?? createDefaultFileSystem();
    this.errors = errorService;
  }

  /**
   * Render single frame
   * @implements REQ-RENDER-001, REQ-RENDER-002, REQ-RENDER-003, REQ-RENDER-004, REQ-RENDER-005, REQ-RENDER-006
   * @invariant INV-RENDER-001 (frame size never exceeds 1MB)
   * @param input - Render input with protocol and frame source
   * @returns Render result or error
   */
  async render(input: RenderInput): Promise<RenderResult | AnimationError> {
    // Step 1: Validate exactly one input source (INV-INPUT-001)
    const validationError = validateRenderInput(input);
    if (validationError) {
      return validationError;
    }

    // Handle special case: fallbackPreference is 'none' - return error
    // This is for when user explicitly declines all fallbacks
    if (input.fallbackPreference === 'none' && input.protocol !== 'kitty' && input.protocol !== 'iterm2') {
      return this.errors.noFallbackAvailable();
    }

    // Step 2 & 3: Route to appropriate renderer based on protocol
    try {
      switch (input.protocol) {
        case 'kitty':
        case 'iterm2':
          return await this.renderTerminalGraphics(input);
        case 'ascii':
          return await this.renderAscii(input);
        case 'browser':
          return await this.renderBrowser(input);
        default:
          return this.errors.renderFailed(`Unknown protocol: ${input.protocol}`);
      }
    } catch (error) {
      const message = error instanceof Error ? error.message : String(error);
      return this.errors.renderFailed(message);
    }
  }

  /**
   * Render to terminal graphics (Kitty or iTerm2)
   * @implements REQ-RENDER-002, REQ-RENDER-005, REQ-RENDER-006
   * NORMATIVE: SC-ANIM-005
   */
  private async renderTerminalGraphics(input: RenderInput): Promise<TerminalRenderResult | AnimationError> {
    // Obtain PNG data
    const pngResult = await this.obtainPngData(input);
    if (isAnimationError(pngResult)) {
      return pngResult;
    }
    const pngData = pngResult;

    // Step 4: Check frame size limit (INV-RENDER-001, SC-ANIM-024)
    if (pngData.length > FRAME_SIZE_LIMIT) {
      const dimensions = this.getInputDimensions(input);
      return this.errors.frameTooLarge(pngData.length, dimensions.width, dimensions.height);
    }

    // Step 5: Encode for protocol
    const output = input.protocol === 'kitty'
      ? renderKitty(pngData)
      : renderIterm2(pngData);

    return {
      output,
      protocol: input.protocol as 'kitty' | 'iterm2',
      frameIndex: input.frameIndex
    };
  }

  /**
   * Render to ASCII art
   * @implements REQ-FALLBACK-003, REQ-FALLBACK-004, REQ-FALLBACK-005
   * NORMATIVE: SC-ANIM-009, SC-ANIM-019, SC-ANIM-020
   */
  private async renderAscii(input: RenderInput): Promise<AsciiRenderResult | AnimationError> {
    // For ASCII rendering, we need the AnimView structure
    // If svgContent or svgFilePath is provided, we need to convert
    let animView: AnimView;

    if (input.animView) {
      animView = input.animView;
    } else if (input.svgContent) {
      animView = this.svgContentToAnimView(input.svgContent);
    } else if (input.svgFilePath) {
      const exists = await this.fileSystem.exists(input.svgFilePath);
      if (!exists) {
        return this.errors.fileNotFound(input.svgFilePath);
      }
      const content = await this.fileSystem.readFile(input.svgFilePath);
      animView = this.svgContentToAnimView(content.toString('utf-8'));
    } else {
      return this.errors.invalidAnimView('source');
    }

    const config = input.asciiConfig ?? {};
    const result = renderAscii(animView, config);
    result.frameIndex = input.frameIndex;

    return result;
  }

  /**
   * Render to browser fallback (save file)
   * @implements REQ-FALLBACK-001, REQ-FALLBACK-002
   */
  private async renderBrowser(input: RenderInput): Promise<BrowserRenderResult | AnimationError> {
    let svgContent: string;

    if (input.animView) {
      svgContent = animViewToSvg(input.animView);
    } else if (input.svgContent) {
      svgContent = input.svgContent;
    } else if (input.svgFilePath) {
      const exists = await this.fileSystem.exists(input.svgFilePath);
      if (!exists) {
        return this.errors.fileNotFound(input.svgFilePath);
      }
      const content = await this.fileSystem.readFile(input.svgFilePath);
      svgContent = content.toString('utf-8');
    } else {
      return this.errors.invalidAnimView('source');
    }

    // Create HTML wrapper
    const htmlContent = `<!DOCTYPE html>
<html>
<head>
  <meta charset="utf-8">
  <title>TLA+ Animation Frame ${input.frameIndex}</title>
  <style>
    body { margin: 0; display: flex; justify-content: center; align-items: center; min-height: 100vh; background: #1a1a1a; }
    svg { max-width: 100%; max-height: 100vh; }
  </style>
</head>
<body>
${svgContent}
</body>
</html>`;

    // Save to temp directory
    const tempDir = os.tmpdir();
    const fileName = `tlaplus_anim_frame_${input.frameIndex}.html`;
    const filePath = path.join(tempDir, fileName);

    await this.fileSystem.writeFile(filePath, htmlContent);

    return {
      filePath,
      protocol: 'browser',
      frameIndex: input.frameIndex
    };
  }

  /**
   * Obtain PNG data from input source
   * @implements REQ-RENDER-005, REQ-RENDER-006
   */
  private async obtainPngData(input: RenderInput): Promise<Buffer | AnimationError> {
    if (input.animView) {
      // REQ-RENDER-005: AnimView direct rasterization
      return this.rasterizer.rasterizeAnimView(input.animView);
    }

    if (input.svgContent) {
      // REQ-RENDER-006: SVG conversion at render time
      return this.rasterizer.rasterizeSvg(input.svgContent);
    }

    if (input.svgFilePath) {
      // REQ-RENDER-006: SVG file conversion at render time
      const exists = await this.fileSystem.exists(input.svgFilePath);
      if (!exists) {
        return this.errors.fileNotFound(input.svgFilePath);
      }

      try {
        const content = await this.fileSystem.readFile(input.svgFilePath);
        return this.rasterizer.rasterizeSvg(content.toString('utf-8'));
      } catch (error) {
        const message = error instanceof Error ? error.message : String(error);
        return this.errors.invalidSvg(message);
      }
    }

    return this.errors.invalidAnimView('source');
  }

  /**
   * Get dimensions from input
   */
  private getInputDimensions(input: RenderInput): { width: number; height: number } {
    if (input.animView) {
      return { width: input.animView.width, height: input.animView.height };
    }
    if (input.svgContent) {
      return extractSvgDimensions(input.svgContent);
    }
    // Default dimensions for file-based inputs
    return { width: 200, height: 100 };
  }

  /**
   * Convert SVG content to AnimView structure
   * This is a simplified conversion for ASCII rendering
   */
  private svgContentToAnimView(svgContent: string): AnimView {
    const dimensions = extractSvgDimensions(svgContent);

    // Extract title if present
    const titleMatch = svgContent.match(/<title>([^<]*)<\/title>/);
    const title = titleMatch ? titleMatch[1] : 'Frame';

    // Parse basic SVG elements
    const elements: SvgElement[] = [];

    // Parse rect elements
    const rectRegex = /<rect([^>]*)\/?>|<rect([^>]*)>[^<]*<\/rect>/g;
    let match;
    while ((match = rectRegex.exec(svgContent)) !== null) {
      const attrs = match[1] || match[2];
      elements.push(parseElementAttrs('rect', attrs));
    }

    // Parse circle elements
    const circleRegex = /<circle([^>]*)\/?>|<circle([^>]*)>[^<]*<\/circle>/g;
    while ((match = circleRegex.exec(svgContent)) !== null) {
      const attrs = match[1] || match[2];
      elements.push(parseElementAttrs('circle', attrs));
    }

    // Parse text elements
    const textRegex = /<text([^>]*)>([^<]*)<\/text>/g;
    while ((match = textRegex.exec(svgContent)) !== null) {
      const attrs = match[1];
      const text = match[2];
      const element = parseElementAttrs('text', attrs);
      element.text = text;
      elements.push(element);
    }

    // Parse line elements
    const lineRegex = /<line([^>]*)\/?>|<line([^>]*)>[^<]*<\/line>/g;
    while ((match = lineRegex.exec(svgContent)) !== null) {
      const attrs = match[1] || match[2];
      elements.push(parseElementAttrs('line', attrs));
    }

    return {
      frame: '0',
      title,
      width: dimensions.width,
      height: dimensions.height,
      elements
    };
  }

  /**
   * Get frame count for trace directory
   * @implements REQ-ARCH-008
   * NORMATIVE: SC-ANIM-026
   * @param traceDirectory - Directory containing trace files
   * @param filePattern - Glob pattern (default: "*_anim_*.svg")
   * @returns Frame count and file list
   */
  async getFrameCount(
    traceDirectory: string,
    filePattern?: string
  ): Promise<FrameCountResult | AnimationError> {
    // Check if directory exists
    const exists = await this.fileSystem.exists(traceDirectory);
    if (!exists) {
      return this.errors.fileNotFound(traceDirectory);
    }

    const pattern = filePattern ?? DEFAULT_FILE_PATTERN;

    try {
      const files = await this.fileSystem.glob(pattern, traceDirectory);

      // Sort files by frame number extracted from filename
      const sortedFiles = files.sort((a, b) => {
        const numA = extractFrameNumber(a);
        const numB = extractFrameNumber(b);
        return numA - numB;
      });

      return {
        count: sortedFiles.length,
        files: sortedFiles
      };
    } catch (error) {
      const message = error instanceof Error ? error.message : String(error);
      return this.errors.renderFailed(`Failed to enumerate files: ${message}`);
    }
  }
}

/**
 * Parse SVG element attributes from string
 */
function parseElementAttrs(shape: string, attrsStr: string): SvgElement {
  const element: SvgElement = { shape: shape as SvgElement['shape'] };
  const attrRegex = /(\w+)=["']([^"']*)["']/g;
  let match;
  while ((match = attrRegex.exec(attrsStr)) !== null) {
    const [, name, value] = match;
    // Convert numeric attributes
    if (['x', 'y', 'width', 'height', 'cx', 'cy', 'r', 'x1', 'y1', 'x2', 'y2'].includes(name)) {
      element[name] = parseFloat(value);
    } else {
      element[name] = value;
    }
  }
  return element;
}

/**
 * Extract frame number from filename
 */
function extractFrameNumber(filePath: string): number {
  const filename = path.basename(filePath);
  const match = filename.match(/_(\d+)\./);
  return match ? parseInt(match[1], 10) : 0;
}

/**
 * Factory function for creating render service with dependency injection
 * @param rasterizer - Service to convert AnimView/SVG to PNG (for testing)
 * @param fileSystem - File system abstraction (for testing)
 * @returns RenderService instance
 */
export function createRenderService(
  rasterizer?: RasterizerService,
  fileSystem?: FileSystemService
): RenderService {
  return new RenderService({
    rasterizer,
    fileSystem
  });
}
