/**
 * White-box tests for RenderService
 *
 * Tests rendering logic for different protocols: Kitty, iTerm2, ASCII, browser.
 * Uses dependency injection for mocking rasterizer and file system.
 *
 * @module animation/__tests__/RenderService.test
 */

import { createRenderService } from '../RenderService';
import {
  RenderInput,
  TerminalRenderResult,
  AsciiRenderResult,
  BrowserRenderResult,
  AnimView,
  AnimationError,
  RasterizerService,
  FileSystemService,
  isAnimationError,
  isRenderResult
} from '../types';

// Test fixtures
const createValidAnimView = (): AnimView => ({
  frame: '0',
  title: 'Test Frame',
  width: 200,
  height: 100,
  elements: [
    { shape: 'rect', x: 10, y: 10, width: 80, height: 40, fill: '#3498db' },
    { shape: 'text', x: 50, y: 35, text: 'count: 5', fill: 'white' }
  ]
});

const createValidSvgContent = (): string => `
<svg xmlns="http://www.w3.org/2000/svg" width="200" height="100">
  <rect x="10" y="10" width="80" height="40" fill="#3498db"/>
  <text x="50" y="35" fill="white">count: 5</text>
</svg>`;

const createMockPngBuffer = (size = 1000): Buffer => {
  return Buffer.alloc(size, 0x89); // PNG magic byte pattern
};

const createMockRasterizer = (pngBuffer?: Buffer): RasterizerService => ({
  rasterizeAnimView: jest.fn().mockResolvedValue(pngBuffer ?? createMockPngBuffer()),
  rasterizeSvg: jest.fn().mockResolvedValue(pngBuffer ?? createMockPngBuffer())
});

const createMockFileSystem = (files: Map<string, Buffer | string> = new Map()): FileSystemService => ({
  readFile: jest.fn().mockImplementation(async (path: string) => {
    if (files.has(path)) {
      const content = files.get(path)!;
      return typeof content === 'string' ? Buffer.from(content) : content;
    }
    throw new Error(`File not found: ${path}`);
  }),
  writeFile: jest.fn().mockResolvedValue(undefined),
  exists: jest.fn().mockImplementation(async (path: string) => files.has(path)),
  glob: jest.fn().mockResolvedValue([])
});

describe('RenderService', () => {
  describe('Input Validation', () => {
    // @tests REQ-RENDER-004, SCN-ERROR-003
    // @tests-invariant INV-INPUT-001
    it('returns error when no source is provided', async () => {
      const service = createRenderService(createMockRasterizer());

      const input: RenderInput = {
        operation: 'render',
        protocol: 'kitty',
        useCase: 'live',
        frameIndex: 0
        // No animView, svgContent, or svgFilePath
      };

      const result = await service.render(input);

      expect(isAnimationError(result)).toBe(true);
      const error = result as AnimationError;
      expect(error.error).toBe('INVALID_ANIMVIEW');
      expect(error.message).toContain('source');
    });

    // @tests REQ-RENDER-004
    // @tests-invariant INV-INPUT-001
    it('returns error when multiple sources are provided', async () => {
      const service = createRenderService(createMockRasterizer());

      const input: RenderInput = {
        operation: 'render',
        protocol: 'kitty',
        useCase: 'live',
        frameIndex: 0,
        animView: createValidAnimView(),
        svgContent: createValidSvgContent()
      };

      const result = await service.render(input);

      expect(isAnimationError(result)).toBe(true);
      const error = result as AnimationError;
      expect(error.error).toBe('INVALID_ANIMVIEW');
      expect(error.message).toContain('Exactly one');
    });

    // @tests REQ-RENDER-004
    it('returns error when AnimView is missing required field: frame', async () => {
      const service = createRenderService(createMockRasterizer());

      const invalidAnimView = {
        title: 'Test',
        width: 200,
        height: 100,
        elements: []
      };

      const input: RenderInput = {
        operation: 'render',
        protocol: 'kitty',
        useCase: 'live',
        frameIndex: 0,
        animView: invalidAnimView as unknown as AnimView
      };

      const result = await service.render(input);

      expect(isAnimationError(result)).toBe(true);
      const error = result as AnimationError;
      expect(error.error).toBe('INVALID_ANIMVIEW');
      expect(error.message).toContain('frame');
    });

    // @tests REQ-RENDER-004
    it('returns error when AnimView has invalid width (zero)', async () => {
      const service = createRenderService(createMockRasterizer());

      const invalidAnimView: AnimView = {
        frame: '0',
        title: 'Test',
        width: 0,
        height: 100,
        elements: []
      };

      const input: RenderInput = {
        operation: 'render',
        protocol: 'kitty',
        useCase: 'live',
        frameIndex: 0,
        animView: invalidAnimView
      };

      const result = await service.render(input);

      expect(isAnimationError(result)).toBe(true);
      const error = result as AnimationError;
      expect(error.error).toBe('INVALID_ANIMVIEW');
      expect(error.message).toContain('width');
    });

    // @tests REQ-RENDER-004
    it('returns error when AnimView has invalid height (negative)', async () => {
      const service = createRenderService(createMockRasterizer());

      const invalidAnimView: AnimView = {
        frame: '0',
        title: 'Test',
        width: 200,
        height: -100,
        elements: []
      };

      const input: RenderInput = {
        operation: 'render',
        protocol: 'kitty',
        useCase: 'live',
        frameIndex: 0,
        animView: invalidAnimView
      };

      const result = await service.render(input);

      expect(isAnimationError(result)).toBe(true);
      const error = result as AnimationError;
      expect(error.error).toBe('INVALID_ANIMVIEW');
      expect(error.message).toContain('height');
    });
  });

  describe('Kitty Protocol Rendering', () => {
    // @tests REQ-RENDER-001, REQ-RENDER-002, REQ-RENDER-005, SCN-RENDER-001
    it('renders AnimView to Kitty escape sequence', async () => {
      const mockRasterizer = createMockRasterizer();
      const service = createRenderService(mockRasterizer);

      const input: RenderInput = {
        operation: 'render',
        protocol: 'kitty',
        useCase: 'live',
        frameIndex: 0,
        animView: createValidAnimView()
      };

      const result = await service.render(input);

      expect(isAnimationError(result)).toBe(false);
      const renderResult = result as TerminalRenderResult;
      expect(renderResult.protocol).toBe('kitty');
      expect(renderResult.frameIndex).toBe(0);

      // Verify Kitty escape sequence format: \x1b_Ga=T,f=100,m=0;<base64>\x1b\\
      expect(renderResult.output).toMatch(/^\x1b_Ga=T,f=100,m=0;[A-Za-z0-9+/=]+\x1b\\$/);
      expect(mockRasterizer.rasterizeAnimView).toHaveBeenCalledWith(input.animView);
    });

    // @tests REQ-RENDER-002, REQ-ARCH-005, SCN-ARCH-005
    it('does not re-detect protocol - uses explicit protocol parameter', async () => {
      const mockRasterizer = createMockRasterizer();
      const service = createRenderService(mockRasterizer);

      // Even if we're in an iTerm2 environment, render should use the explicit protocol
      const input: RenderInput = {
        operation: 'render',
        protocol: 'kitty', // Explicit kitty, not detected
        useCase: 'live',
        frameIndex: 0,
        animView: createValidAnimView()
      };

      const result = await service.render(input);

      expect(isAnimationError(result)).toBe(false);
      const renderResult = result as TerminalRenderResult;
      expect(renderResult.protocol).toBe('kitty');
      // Kitty format, not iTerm2
      expect(renderResult.output).toContain('\x1b_G');
    });
  });

  describe('iTerm2 Protocol Rendering', () => {
    // @tests REQ-RENDER-002, SCN-RENDER-002
    it('renders AnimView to iTerm2 escape sequence', async () => {
      const mockRasterizer = createMockRasterizer();
      const service = createRenderService(mockRasterizer);

      const input: RenderInput = {
        operation: 'render',
        protocol: 'iterm2',
        useCase: 'static',
        frameIndex: 5,
        animView: createValidAnimView()
      };

      const result = await service.render(input);

      expect(isAnimationError(result)).toBe(false);
      const renderResult = result as TerminalRenderResult;
      expect(renderResult.protocol).toBe('iterm2');
      expect(renderResult.frameIndex).toBe(5);

      // Verify iTerm2 escape sequence format: \x1b]1337;File=inline=1;size=<bytes>:<base64>\x07
      expect(renderResult.output).toMatch(/^\x1b\]1337;File=inline=1;size=\d+:[A-Za-z0-9+/=]+\x07$/);
    });
  });

  describe('SVG Content Rendering', () => {
    // @tests REQ-RENDER-006
    it('renders svgContent to terminal graphics', async () => {
      const mockRasterizer = createMockRasterizer();
      const service = createRenderService(mockRasterizer);

      const input: RenderInput = {
        operation: 'render',
        protocol: 'kitty',
        useCase: 'static',
        frameIndex: 0,
        svgContent: createValidSvgContent()
      };

      const result = await service.render(input);

      expect(isAnimationError(result)).toBe(false);
      const renderResult = result as TerminalRenderResult;
      expect(renderResult.protocol).toBe('kitty');
      expect(mockRasterizer.rasterizeSvg).toHaveBeenCalledWith(input.svgContent);
    });
  });

  describe('SVG File Rendering', () => {
    // @tests REQ-RENDER-006, SCN-RENDER-002
    it('renders svgFilePath to terminal graphics', async () => {
      const svgContent = createValidSvgContent();
      const files = new Map([['/tmp/test.svg', svgContent]]);
      const mockFileSystem = createMockFileSystem(files);
      const mockRasterizer = createMockRasterizer();
      const service = createRenderService(mockRasterizer, mockFileSystem);

      const input: RenderInput = {
        operation: 'render',
        protocol: 'kitty',
        useCase: 'static',
        frameIndex: 0,
        svgFilePath: '/tmp/test.svg'
      };

      const result = await service.render(input);

      expect(isAnimationError(result)).toBe(false);
      const renderResult = result as TerminalRenderResult;
      expect(renderResult.protocol).toBe('kitty');
      expect(mockFileSystem.exists).toHaveBeenCalledWith('/tmp/test.svg');
      expect(mockFileSystem.readFile).toHaveBeenCalledWith('/tmp/test.svg');
    });

    // @tests REQ-ERROR-001
    it('returns FILE_NOT_FOUND when svgFilePath does not exist', async () => {
      const mockFileSystem = createMockFileSystem(); // Empty file system
      const service = createRenderService(createMockRasterizer(), mockFileSystem);

      const input: RenderInput = {
        operation: 'render',
        protocol: 'kitty',
        useCase: 'static',
        frameIndex: 0,
        svgFilePath: '/nonexistent/file.svg'
      };

      const result = await service.render(input);

      expect(isAnimationError(result)).toBe(true);
      const error = result as AnimationError;
      expect(error.error).toBe('FILE_NOT_FOUND');
      expect(error.message).toContain('/nonexistent/file.svg');
      expect(error.remediation.length).toBeGreaterThan(0);
    });
  });

  describe('Frame Size Limit', () => {
    // @tests REQ-ARCH-006, SCN-ERROR-002
    // @tests-invariant INV-RENDER-001
    it('returns FRAME_TOO_LARGE when PNG exceeds 1MB', async () => {
      const oversizedBuffer = Buffer.alloc(1024 * 1024 + 1); // 1MB + 1 byte
      const mockRasterizer = createMockRasterizer(oversizedBuffer);
      const service = createRenderService(mockRasterizer);

      const input: RenderInput = {
        operation: 'render',
        protocol: 'kitty',
        useCase: 'live',
        frameIndex: 0,
        animView: createValidAnimView()
      };

      const result = await service.render(input);

      expect(isAnimationError(result)).toBe(true);
      const error = result as AnimationError;
      expect(error.error).toBe('FRAME_TOO_LARGE');
      expect(error.message).toContain('1MB');
      expect(error.remediation.length).toBeGreaterThan(0);
    });

    // @tests REQ-ARCH-006
    // @tests-invariant INV-RENDER-001
    it('succeeds when PNG is exactly 1MB', async () => {
      const exactBuffer = Buffer.alloc(1024 * 1024); // Exactly 1MB
      const mockRasterizer = createMockRasterizer(exactBuffer);
      const service = createRenderService(mockRasterizer);

      const input: RenderInput = {
        operation: 'render',
        protocol: 'kitty',
        useCase: 'live',
        frameIndex: 0,
        animView: createValidAnimView()
      };

      const result = await service.render(input);

      expect(isAnimationError(result)).toBe(false);
      const renderResult = result as TerminalRenderResult;
      expect(renderResult.protocol).toBe('kitty');
    });
  });

  describe('ASCII Rendering', () => {
    // @tests REQ-FALLBACK-003, SCN-FALLBACK-001
    it('renders AnimView to ASCII art', async () => {
      const service = createRenderService(createMockRasterizer());

      const input: RenderInput = {
        operation: 'render',
        protocol: 'ascii',
        useCase: 'live',
        frameIndex: 0,
        animView: createValidAnimView(),
        asciiConfig: { columns: 80, rows: 24, colorEnabled: false }
      };

      const result = await service.render(input);

      expect(isAnimationError(result)).toBe(false);
      const renderResult = result as AsciiRenderResult;
      expect(renderResult.protocol).toBe('ascii');
      expect(renderResult.frameIndex).toBe(0);
      expect(renderResult.dimensions.cols).toBe(80);
      expect(renderResult.dimensions.rows).toBe(24);
      expect(typeof renderResult.output).toBe('string');
    });

    // @tests REQ-FALLBACK-004
    it('enforces minimum ASCII canvas size (40x20)', async () => {
      const service = createRenderService(createMockRasterizer());

      const input: RenderInput = {
        operation: 'render',
        protocol: 'ascii',
        useCase: 'live',
        frameIndex: 0,
        animView: createValidAnimView(),
        asciiConfig: { columns: 10, rows: 5 } // Below minimum
      };

      const result = await service.render(input);

      expect(isAnimationError(result)).toBe(false);
      const renderResult = result as AsciiRenderResult;
      expect(renderResult.dimensions.cols).toBe(40); // Clamped to min
      expect(renderResult.dimensions.rows).toBe(20); // Clamped to min
    });

    // @tests REQ-FALLBACK-004
    it('enforces maximum ASCII canvas size (200x60)', async () => {
      const service = createRenderService(createMockRasterizer());

      const input: RenderInput = {
        operation: 'render',
        protocol: 'ascii',
        useCase: 'live',
        frameIndex: 0,
        animView: createValidAnimView(),
        asciiConfig: { columns: 300, rows: 100 } // Above maximum
      };

      const result = await service.render(input);

      expect(isAnimationError(result)).toBe(false);
      const renderResult = result as AsciiRenderResult;
      expect(renderResult.dimensions.cols).toBe(200); // Clamped to max
      expect(renderResult.dimensions.rows).toBe(60); // Clamped to max
    });

    // @tests REQ-FALLBACK-004
    it('uses default ASCII canvas size (80x24) when not specified', async () => {
      const service = createRenderService(createMockRasterizer());

      const input: RenderInput = {
        operation: 'render',
        protocol: 'ascii',
        useCase: 'live',
        frameIndex: 0,
        animView: createValidAnimView()
        // No asciiConfig
      };

      const result = await service.render(input);

      expect(isAnimationError(result)).toBe(false);
      const renderResult = result as AsciiRenderResult;
      expect(renderResult.dimensions.cols).toBe(80);
      expect(renderResult.dimensions.rows).toBe(24);
    });

    // @tests REQ-FALLBACK-003
    it('renders rectangle with box-drawing characters', async () => {
      const service = createRenderService(createMockRasterizer());

      const animView: AnimView = {
        frame: '0',
        title: 'Rect Test',
        width: 80,
        height: 24,
        elements: [
          { shape: 'rect', x: 0, y: 0, width: 10, height: 5, fill: 'blue' }
        ]
      };

      const input: RenderInput = {
        operation: 'render',
        protocol: 'ascii',
        useCase: 'live',
        frameIndex: 0,
        animView,
        asciiConfig: { columns: 80, rows: 24, colorEnabled: false }
      };

      const result = await service.render(input);

      expect(isAnimationError(result)).toBe(false);
      const renderResult = result as AsciiRenderResult;

      // Verify box-drawing characters are present
      expect(renderResult.output).toContain('\u250C'); // Top-left corner
      expect(renderResult.output).toContain('\u2510'); // Top-right corner
      expect(renderResult.output).toContain('\u2514'); // Bottom-left corner
      expect(renderResult.output).toContain('\u2518'); // Bottom-right corner
    });
  });

  describe('Browser Fallback', () => {
    // @tests REQ-FALLBACK-001, REQ-FALLBACK-002, SCN-FALLBACK-002
    it('saves AnimView to HTML file for browser viewing', async () => {
      const mockFileSystem = createMockFileSystem();
      const service = createRenderService(createMockRasterizer(), mockFileSystem);

      const input: RenderInput = {
        operation: 'render',
        protocol: 'browser',
        useCase: 'static',
        frameIndex: 2,
        animView: createValidAnimView()
      };

      const result = await service.render(input);

      expect(isAnimationError(result)).toBe(false);
      const renderResult = result as BrowserRenderResult;
      expect(renderResult.protocol).toBe('browser');
      expect(renderResult.frameIndex).toBe(2);
      expect(renderResult.filePath).toContain('tlaplus_anim_frame_2.html');
      expect(mockFileSystem.writeFile).toHaveBeenCalled();
    });
  });

  describe('No Fallback Error', () => {
    // @tests REQ-FALLBACK-006, SCN-ERROR-005
    it('returns NO_FALLBACK_AVAILABLE when fallbackPreference is none', async () => {
      const service = createRenderService(createMockRasterizer());

      const input: RenderInput = {
        operation: 'render',
        protocol: 'ascii', // Not a graphics protocol
        useCase: 'live',
        frameIndex: 0,
        animView: createValidAnimView(),
        fallbackPreference: 'none'
      };

      const result = await service.render(input);

      expect(isAnimationError(result)).toBe(true);
      const error = result as AnimationError;
      expect(error.error).toBe('NO_FALLBACK_AVAILABLE');
      expect(error.remediation.length).toBeGreaterThan(0);
      expect(error.remediation.some(r => r.includes('ascii'))).toBe(true);
      expect(error.remediation.some(r => r.includes('browser'))).toBe(true);
    });
  });

  describe('Use Cases', () => {
    // @tests REQ-ARCH-003, SCN-RENDER-001
    it('supports live exploration use case', async () => {
      const service = createRenderService(createMockRasterizer());

      const input: RenderInput = {
        operation: 'render',
        protocol: 'kitty',
        useCase: 'live',
        frameIndex: 0,
        animView: createValidAnimView()
      };

      const result = await service.render(input);

      expect(isAnimationError(result)).toBe(false);
      expect(isRenderResult(result)).toBe(true);
    });

    // @tests REQ-ARCH-003, SCN-RENDER-002
    it('supports static frame use case', async () => {
      const files = new Map([['/tmp/frame.svg', createValidSvgContent()]]);
      const mockFileSystem = createMockFileSystem(files);
      const service = createRenderService(createMockRasterizer(), mockFileSystem);

      const input: RenderInput = {
        operation: 'render',
        protocol: 'iterm2',
        useCase: 'static',
        frameIndex: 5,
        svgFilePath: '/tmp/frame.svg'
      };

      const result = await service.render(input);

      expect(isAnimationError(result)).toBe(false);
      const renderResult = result as TerminalRenderResult;
      expect(renderResult.frameIndex).toBe(5);
    });

    // @tests REQ-ARCH-003, SCN-RENDER-003, SCN-TRACE-001
    it('supports trace visualization use case', async () => {
      const files = new Map([['/tmp/trace/MySpec_anim_3.svg', createValidSvgContent()]]);
      const mockFileSystem = createMockFileSystem(files);
      const service = createRenderService(createMockRasterizer(), mockFileSystem);

      const input: RenderInput = {
        operation: 'render',
        protocol: 'kitty',
        useCase: 'trace',
        frameIndex: 3,
        svgFilePath: '/tmp/trace/MySpec_anim_3.svg',
        traceDirectory: '/tmp/trace/', // Metadata only
        filePattern: 'MySpec_anim_*.svg' // Metadata only
      };

      const result = await service.render(input);

      expect(isAnimationError(result)).toBe(false);
      const renderResult = result as TerminalRenderResult;
      expect(renderResult.frameIndex).toBe(3);
    });
  });

  describe('Frame Navigation', () => {
    // @tests REQ-RENDER-003
    it('preserves frameIndex in render result', async () => {
      const service = createRenderService(createMockRasterizer());

      const testCases = [0, 1, 5, 99, 999];

      for (const frameIndex of testCases) {
        const input: RenderInput = {
          operation: 'render',
          protocol: 'kitty',
          useCase: 'live',
          frameIndex,
          animView: createValidAnimView()
        };

        const result = await service.render(input);

        expect(isAnimationError(result)).toBe(false);
        const renderResult = result as TerminalRenderResult;
        expect(renderResult.frameIndex).toBe(frameIndex);
      }
    });
  });

  describe('Frame Count', () => {
    // @tests REQ-ARCH-008
    it('enumerates frames in trace directory', async () => {
      const files = new Map([
        ['/tmp/trace/MySpec_anim_0.svg', createValidSvgContent()],
        ['/tmp/trace/MySpec_anim_1.svg', createValidSvgContent()],
        ['/tmp/trace/MySpec_anim_2.svg', createValidSvgContent()]
      ]);
      const mockFileSystem: FileSystemService = {
        ...createMockFileSystem(files),
        exists: jest.fn().mockResolvedValue(true),
        glob: jest.fn().mockResolvedValue([
          '/tmp/trace/MySpec_anim_0.svg',
          '/tmp/trace/MySpec_anim_1.svg',
          '/tmp/trace/MySpec_anim_2.svg'
        ])
      };
      const service = createRenderService(createMockRasterizer(), mockFileSystem);

      const result = await service.getFrameCount('/tmp/trace/', 'MySpec_anim_*.svg');

      expect(isAnimationError(result)).toBe(false);
      expect(result).toHaveProperty('count', 3);
      expect(result).toHaveProperty('files');
      expect((result as { files: string[] }).files.length).toBe(3);
    });

    // @tests REQ-ARCH-008
    it('returns FILE_NOT_FOUND for non-existent trace directory', async () => {
      const mockFileSystem = createMockFileSystem();
      const service = createRenderService(createMockRasterizer(), mockFileSystem);

      const result = await service.getFrameCount('/nonexistent/');

      expect(isAnimationError(result)).toBe(true);
      const error = result as AnimationError;
      expect(error.error).toBe('FILE_NOT_FOUND');
    });

    // @tests REQ-ARCH-008
    it('sorts frames by frame number', async () => {
      const mockFileSystem: FileSystemService = {
        ...createMockFileSystem(),
        exists: jest.fn().mockResolvedValue(true),
        glob: jest.fn().mockResolvedValue([
          '/tmp/trace/MySpec_anim_2.svg',
          '/tmp/trace/MySpec_anim_0.svg',
          '/tmp/trace/MySpec_anim_1.svg'
        ])
      };
      const service = createRenderService(createMockRasterizer(), mockFileSystem);

      const result = await service.getFrameCount('/tmp/trace/');

      expect(isAnimationError(result)).toBe(false);
      const frameResult = result as { count: number; files: string[] };
      expect(frameResult.files[0]).toContain('_0.svg');
      expect(frameResult.files[1]).toContain('_1.svg');
      expect(frameResult.files[2]).toContain('_2.svg');
    });
  });

  describe('Sequential Call Safety', () => {
    // @tests REQ-ARCH-007, SCN-ARCH-006
    // @tests-invariant INV-SEQUENTIAL-001
    it('multiple render calls work independently', async () => {
      const service = createRenderService(createMockRasterizer());

      const input1: RenderInput = {
        operation: 'render',
        protocol: 'kitty',
        useCase: 'live',
        frameIndex: 0,
        animView: createValidAnimView()
      };

      const input2: RenderInput = {
        operation: 'render',
        protocol: 'iterm2',
        useCase: 'static',
        frameIndex: 5,
        animView: { ...createValidAnimView(), frame: '5' }
      };

      const result1 = await service.render(input1);
      const result2 = await service.render(input2);

      expect(isAnimationError(result1)).toBe(false);
      expect(isAnimationError(result2)).toBe(false);

      const r1 = result1 as TerminalRenderResult;
      const r2 = result2 as TerminalRenderResult;

      expect(r1.protocol).toBe('kitty');
      expect(r2.protocol).toBe('iterm2');
      expect(r1.frameIndex).toBe(0);
      expect(r2.frameIndex).toBe(5);
    });
  });
});
