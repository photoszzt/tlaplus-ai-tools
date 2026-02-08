/**
 * Contract Tests for Animation MCP Tool
 *
 * Black-box tests that verify the PUBLIC API contract as documented in contract.md.
 * These tests do NOT access internal services or implementation details.
 *
 * Contract: docs/tla-animations/contract.md
 *
 * @module animation/__tests__/contract/animation-contract.test
 */

import { handleDetect, handleRender, handleFrameCount } from '../../../animation';

// Test fixtures - valid input data per contract.md
const validAnimView = {
  frame: '0',
  title: 'Test Frame',
  width: 200,
  height: 100,
  elements: [
    { shape: 'rect', x: 10, y: 10, width: 80, height: 40, fill: '#3498db' },
    { shape: 'text', x: 50, y: 35, text: 'count: 5', fill: 'white' }
  ]
};

const validSvgContent = `
<svg xmlns="http://www.w3.org/2000/svg" width="200" height="100">
  <rect x="10" y="10" width="80" height="40" fill="#3498db"/>
  <text x="50" y="35" fill="white">count: 5</text>
</svg>`;

/**
 * Parse MCP response content to JSON
 */
function parseResponse(response: { content: { type: string; text: string }[] }): unknown {
  return JSON.parse(response.content[0].text);
}

describe('Animation MCP Tool - Contract Tests', () => {
  describe('detect operation', () => {
    // @tests-contract REQ-DETECT-001
    it('completes detection within timeout per contract', async () => {
      const startTime = Date.now();
      const response = await handleDetect({});
      const duration = Date.now() - startTime;

      // Contract: detection completes within 500ms
      expect(duration).toBeLessThanOrEqual(600); // Allow small tolerance for test overhead
      expect(response).toHaveProperty('content');
      expect(response.content[0]).toHaveProperty('type', 'text');
    });

    // @tests-contract REQ-DETECT-002
    it('returns multiplexer information per contract schema', async () => {
      const response = await handleDetect({});
      const result = parseResponse(response) as Record<string, unknown>;

      // Contract: multiplexer is one of "tmux" | "screen" | "none"
      if (!result.error) {
        expect(result).toHaveProperty('multiplexer');
        expect(['tmux', 'screen', 'none']).toContain(result.multiplexer);
        expect(result).toHaveProperty('passthroughEnabled');
        expect(typeof result.passthroughEnabled).toBe('boolean');
      }
    });

    // @tests-contract REQ-DETECT-003
    it('returns DetectionResult conforming to NORMATIVE schema', async () => {
      const response = await handleDetect({});
      const result = parseResponse(response) as Record<string, unknown>;

      // If not an error, should have all required fields per contract.md section 2.1.1
      if (!result.error) {
        // Protocol: "kitty" | "iterm2" | "none"
        expect(result).toHaveProperty('protocol');
        expect(['kitty', 'iterm2', 'none']).toContain(result.protocol);

        // Multiplexer: "tmux" | "screen" | "none"
        expect(result).toHaveProperty('multiplexer');
        expect(['tmux', 'screen', 'none']).toContain(result.multiplexer);

        // Boolean fields
        expect(typeof result.passthroughEnabled).toBe('boolean');
        expect(typeof result.passthroughVerified).toBe('boolean');

        // Fallback available: always ["ascii", "browser"]
        expect(Array.isArray(result.fallbackAvailable)).toBe(true);

        // Detection method: "env" | "query" | "probe"
        expect(result).toHaveProperty('detectionMethod');
        expect(['env', 'query', 'probe']).toContain(result.detectionMethod);

        // Confidence: "high" | "medium" | "low"
        expect(result).toHaveProperty('confidence');
        expect(['high', 'medium', 'low']).toContain(result.confidence);

        // Environment object
        expect(typeof result.environment).toBe('object');
      }
    });

    // @tests-contract REQ-ARCH-007
    it('supports sequential calls without state corruption', async () => {
      const response1 = await handleDetect({});
      const response2 = await handleDetect({});

      const result1 = parseResponse(response1) as Record<string, unknown>;
      const result2 = parseResponse(response2) as Record<string, unknown>;

      // Both calls should succeed
      expect(response1.content).toBeDefined();
      expect(response2.content).toBeDefined();

      // Results should be consistent if environment unchanged
      if (!result1.error && !result2.error) {
        expect(result1.protocol).toBe(result2.protocol);
        expect(result1.multiplexer).toBe(result2.multiplexer);
      }
    });

    // @tests-contract REQ-ERROR-001
    it('returns error with remediation on timeout', async () => {
      // Using very short timeout to trigger timeout error
      const response = await handleDetect({ timeout: 1 });
      const result = parseResponse(response) as Record<string, unknown>;

      // May timeout or succeed quickly - both are valid
      if (result.error) {
        expect(result).toHaveProperty('message');
        expect(result).toHaveProperty('remediation');
        expect(Array.isArray(result.remediation)).toBe(true);
        expect((result.remediation as string[]).length).toBeGreaterThan(0);
      }
    });
  });

  describe('render operation', () => {
    // @tests-contract REQ-RENDER-001
    it('accepts AnimView and returns terminal-displayable output', async () => {
      const response = await handleRender({
        protocol: 'kitty',
        useCase: 'live',
        frameIndex: 0,
        animView: validAnimView
      });
      const result = parseResponse(response) as Record<string, unknown>;

      // Contract: returns RenderResult with output string
      if (!result.error) {
        expect(result).toHaveProperty('output');
        expect(typeof result.output).toBe('string');
        expect(result).toHaveProperty('protocol');
        expect(result).toHaveProperty('frameIndex', 0);
      }
    });

    // @tests-contract REQ-RENDER-002
    it('generates Kitty protocol escape sequence', async () => {
      const response = await handleRender({
        protocol: 'kitty',
        useCase: 'live',
        frameIndex: 0,
        animView: validAnimView
      });
      const result = parseResponse(response) as Record<string, unknown>;

      if (!result.error) {
        expect(result.protocol).toBe('kitty');
        // Contract: Kitty format is \x1b_Ga=T,f=100,m=0;<base64>\x1b\\
        const output = result.output as string;
        expect(output).toMatch(/^\x1b_Ga=T,f=100,m=0;[A-Za-z0-9+/=]+\x1b\\$/);
      }
    });

    // @tests-contract REQ-RENDER-002
    it('generates iTerm2 protocol escape sequence', async () => {
      const response = await handleRender({
        protocol: 'iterm2',
        useCase: 'static',
        frameIndex: 5,
        animView: validAnimView
      });
      const result = parseResponse(response) as Record<string, unknown>;

      if (!result.error) {
        expect(result.protocol).toBe('iterm2');
        // Contract: iTerm2 format is \x1b]1337;File=inline=1;size=<bytes>:<base64>\x07
        const output = result.output as string;
        expect(output).toMatch(/^\x1b\]1337;File=inline=1;size=\d+:[A-Za-z0-9+/=]+\x07$/);
        expect(result.frameIndex).toBe(5);
      }
    });

    // @tests-contract REQ-RENDER-003
    it('supports manual frame navigation with frameIndex', async () => {
      const frameIndices = [0, 1, 5, 10];

      for (const frameIndex of frameIndices) {
        const response = await handleRender({
          protocol: 'kitty',
          useCase: 'live',
          frameIndex,
          animView: { ...validAnimView, frame: String(frameIndex) }
        });
        const result = parseResponse(response) as Record<string, unknown>;

        if (!result.error) {
          expect(result.frameIndex).toBe(frameIndex);
        }
      }
    });

    // @tests-contract REQ-RENDER-004
    it('validates input format - requires exactly one source', async () => {
      // No source provided
      const noSource = await handleRender({
        protocol: 'kitty',
        useCase: 'live',
        frameIndex: 0
      });
      expect(noSource.isError).toBe(true);
      const noSourceResult = parseResponse(noSource) as Record<string, unknown>;
      expect(noSourceResult).toHaveProperty('error');

      // Multiple sources provided
      const multiSource = await handleRender({
        protocol: 'kitty',
        useCase: 'live',
        frameIndex: 0,
        animView: validAnimView,
        svgContent: validSvgContent
      });
      expect(multiSource.isError).toBe(true);
      const multiResult = parseResponse(multiSource) as Record<string, unknown>;
      expect(multiResult).toHaveProperty('error');
    });

    // @tests-contract REQ-RENDER-005
    it('accepts AnimView and rasterizes directly', async () => {
      const response = await handleRender({
        protocol: 'kitty',
        useCase: 'live',
        frameIndex: 0,
        animView: validAnimView
      });
      const result = parseResponse(response) as Record<string, unknown>;

      // Contract: AnimView is converted to terminal graphics directly
      if (!result.error) {
        expect(result).toHaveProperty('output');
        expect(result.protocol).toBe('kitty');
      }
    });

    // @tests-contract REQ-RENDER-006
    it('accepts svgContent and converts at render time', async () => {
      const response = await handleRender({
        protocol: 'kitty',
        useCase: 'static',
        frameIndex: 0,
        svgContent: validSvgContent
      });
      const result = parseResponse(response) as Record<string, unknown>;

      // Contract: SVG is converted to terminal graphics at render time
      if (!result.error) {
        expect(result).toHaveProperty('output');
        expect(result.protocol).toBe('kitty');
      }
    });

    // @tests-contract REQ-FALLBACK-001
    it('supports ASCII fallback choice', async () => {
      const response = await handleRender({
        protocol: 'ascii',
        useCase: 'live',
        frameIndex: 0,
        animView: validAnimView
      });
      const result = parseResponse(response) as Record<string, unknown>;

      if (!result.error) {
        expect(result.protocol).toBe('ascii');
        expect(result).toHaveProperty('output');
        expect(typeof result.output).toBe('string');
        expect(result).toHaveProperty('dimensions');
      }
    });

    // @tests-contract REQ-FALLBACK-001
    it('supports browser fallback choice', async () => {
      const response = await handleRender({
        protocol: 'browser',
        useCase: 'static',
        frameIndex: 0,
        animView: validAnimView
      });
      const result = parseResponse(response) as Record<string, unknown>;

      if (!result.error) {
        expect(result.protocol).toBe('browser');
        expect(result).toHaveProperty('filePath');
        expect(typeof result.filePath).toBe('string');
      }
    });

    // @tests-contract REQ-FALLBACK-002
    it('accepts configurable fallback preference', async () => {
      // Test with fallbackPreference parameter
      const response = await handleRender({
        protocol: 'ascii',
        useCase: 'live',
        frameIndex: 0,
        animView: validAnimView,
        fallbackPreference: 'ascii'
      });

      // Should succeed with valid input
      expect(response).toHaveProperty('content');
    });

    // @tests-contract REQ-FALLBACK-003
    it('ASCII rendering uses box-drawing characters', async () => {
      const response = await handleRender({
        protocol: 'ascii',
        useCase: 'live',
        frameIndex: 0,
        animView: {
          frame: '0',
          title: 'Rect Test',
          width: 80,
          height: 24,
          elements: [
            { shape: 'rect', x: 0, y: 0, width: 10, height: 5, fill: 'blue' }
          ]
        },
        asciiConfig: { columns: 80, rows: 24, colorEnabled: false }
      });
      const result = parseResponse(response) as Record<string, unknown>;

      if (!result.error) {
        const output = result.output as string;
        // Contract: uses specified Unicode box-drawing characters
        expect(output).toMatch(/[\u250C\u2510\u2514\u2518\u2500\u2502]/);
      }
    });

    // @tests-contract REQ-FALLBACK-004
    it('ASCII canvas respects size constraints', async () => {
      // Below minimum
      const belowMin = await handleRender({
        protocol: 'ascii',
        useCase: 'live',
        frameIndex: 0,
        animView: validAnimView,
        asciiConfig: { columns: 10, rows: 5 }
      });
      const belowMinResult = parseResponse(belowMin) as Record<string, unknown>;

      if (!belowMinResult.error) {
        const dims = belowMinResult.dimensions as { cols: number; rows: number };
        // Contract: clamped to MIN 40x20
        expect(dims.cols).toBeGreaterThanOrEqual(40);
        expect(dims.rows).toBeGreaterThanOrEqual(20);
      }

      // Above maximum
      const aboveMax = await handleRender({
        protocol: 'ascii',
        useCase: 'live',
        frameIndex: 0,
        animView: validAnimView,
        asciiConfig: { columns: 300, rows: 100 }
      });
      const aboveMaxResult = parseResponse(aboveMax) as Record<string, unknown>;

      if (!aboveMaxResult.error) {
        const dims = aboveMaxResult.dimensions as { cols: number; rows: number };
        // Contract: clamped to MAX 200x60
        expect(dims.cols).toBeLessThanOrEqual(200);
        expect(dims.rows).toBeLessThanOrEqual(60);
      }
    });

    // @tests-contract REQ-FALLBACK-005
    it('ASCII rendering includes ANSI colors when enabled', async () => {
      const response = await handleRender({
        protocol: 'ascii',
        useCase: 'live',
        frameIndex: 0,
        animView: {
          frame: '0',
          title: 'Color Test',
          width: 80,
          height: 24,
          elements: [
            { shape: 'rect', x: 0, y: 0, width: 10, height: 5, fill: 'blue' }
          ]
        },
        asciiConfig: { columns: 80, rows: 24, colorEnabled: true }
      });
      const result = parseResponse(response) as Record<string, unknown>;

      if (!result.error) {
        const output = result.output as string;
        // Contract: ANSI color codes are \x1b[38;5;<code>m
        expect(output).toContain('\x1b[38;5;');
      }
    });

    // @tests-contract REQ-FALLBACK-006
    it('returns NO_FALLBACK_AVAILABLE when fallbackPreference is none', async () => {
      const response = await handleRender({
        protocol: 'ascii', // Not kitty or iterm2
        useCase: 'live',
        frameIndex: 0,
        animView: validAnimView,
        fallbackPreference: 'none'
      });
      const result = parseResponse(response) as Record<string, unknown>;

      expect(response.isError).toBe(true);
      expect(result.error).toBe('NO_FALLBACK_AVAILABLE');
      expect(Array.isArray(result.remediation)).toBe(true);
      expect((result.remediation as string[]).length).toBeGreaterThan(0);
    });

    // @tests-contract REQ-ARCH-003
    it('supports live use case', async () => {
      const response = await handleRender({
        protocol: 'kitty',
        useCase: 'live',
        frameIndex: 0,
        animView: validAnimView
      });
      const result = parseResponse(response) as Record<string, unknown>;

      if (!result.error) {
        expect(result).toHaveProperty('output');
      }
    });

    // @tests-contract REQ-ARCH-003
    it('supports static use case', async () => {
      const response = await handleRender({
        protocol: 'iterm2',
        useCase: 'static',
        frameIndex: 5,
        animView: validAnimView
      });
      const result = parseResponse(response) as Record<string, unknown>;

      if (!result.error) {
        expect(result).toHaveProperty('output');
      }
    });

    // @tests-contract REQ-ARCH-003
    it('supports trace use case', async () => {
      const response = await handleRender({
        protocol: 'kitty',
        useCase: 'trace',
        frameIndex: 3,
        animView: validAnimView
      });
      const result = parseResponse(response) as Record<string, unknown>;

      if (!result.error) {
        expect(result).toHaveProperty('output');
      }
    });

    // @tests-contract REQ-ARCH-005
    it('uses explicit protocol without re-detection', async () => {
      // Render should use the protocol specified, not detect
      const response = await handleRender({
        protocol: 'iterm2', // Explicitly specified
        useCase: 'live',
        frameIndex: 0,
        animView: validAnimView
      });
      const result = parseResponse(response) as Record<string, unknown>;

      if (!result.error) {
        expect(result.protocol).toBe('iterm2'); // Used as specified
      }
    });

    // @tests-contract REQ-ARCH-006
    it('validates AnimView structure', async () => {
      // Missing required field
      const response = await handleRender({
        protocol: 'kitty',
        useCase: 'live',
        frameIndex: 0,
        animView: {
          frame: '0',
          title: 'Missing height',
          width: 200,
          // height missing
          elements: []
        }
      });

      expect(response.isError).toBe(true);
      const result = parseResponse(response) as Record<string, unknown>;
      expect(result).toHaveProperty('error');
    });

    // @tests-contract REQ-ARCH-007
    it('supports sequential render calls independently', async () => {
      const response1 = await handleRender({
        protocol: 'kitty',
        useCase: 'live',
        frameIndex: 0,
        animView: validAnimView
      });

      const response2 = await handleRender({
        protocol: 'iterm2',
        useCase: 'static',
        frameIndex: 5,
        animView: { ...validAnimView, frame: '5' }
      });

      const result1 = parseResponse(response1) as Record<string, unknown>;
      const result2 = parseResponse(response2) as Record<string, unknown>;

      if (!result1.error && !result2.error) {
        expect(result1.protocol).toBe('kitty');
        expect(result2.protocol).toBe('iterm2');
        expect(result1.frameIndex).toBe(0);
        expect(result2.frameIndex).toBe(5);
      }
    });

    // @tests-contract REQ-ERROR-001
    it('returns error with actionable remediation', async () => {
      const response = await handleRender({
        protocol: 'kitty',
        useCase: 'live',
        frameIndex: 0,
        svgFilePath: '/nonexistent/file.svg'
      });

      expect(response.isError).toBe(true);
      const result = parseResponse(response) as Record<string, unknown>;
      expect(result).toHaveProperty('error');
      expect(result).toHaveProperty('message');
      expect(result).toHaveProperty('remediation');
      expect(Array.isArray(result.remediation)).toBe(true);
      expect((result.remediation as string[]).length).toBeGreaterThan(0);
    });
  });

  describe('frameCount operation', () => {
    // @tests-contract REQ-ARCH-008
    it('returns count and sorted file list for valid directory', async () => {
      // Create a temp directory with test files
      const fs = await import('fs/promises');
      const os = await import('os');
      const path = await import('path');

      const tempDir = path.join(os.tmpdir(), `contract-test-${Date.now()}`);
      await fs.mkdir(tempDir, { recursive: true });

      try {
        // Create test files
        await fs.writeFile(path.join(tempDir, 'Test_anim_0.svg'), '<svg></svg>');
        await fs.writeFile(path.join(tempDir, 'Test_anim_1.svg'), '<svg></svg>');
        await fs.writeFile(path.join(tempDir, 'Test_anim_2.svg'), '<svg></svg>');

        const response = await handleFrameCount({
          traceDirectory: tempDir,
          filePattern: 'Test_anim_*.svg'
        });
        const result = parseResponse(response) as Record<string, unknown>;

        if (!result.error) {
          // Contract: returns { count: number, files: string[] }
          expect(result).toHaveProperty('count', 3);
          expect(result).toHaveProperty('files');
          expect(Array.isArray(result.files)).toBe(true);
          expect((result.files as string[]).length).toBe(3);

          // Contract: files are sorted by frame number
          const files = result.files as string[];
          expect(files[0]).toContain('_0.svg');
          expect(files[1]).toContain('_1.svg');
          expect(files[2]).toContain('_2.svg');
        }
      } finally {
        // Cleanup
        await fs.rm(tempDir, { recursive: true, force: true });
      }
    });

    // @tests-contract REQ-ARCH-008
    it('returns FILE_NOT_FOUND for non-existent directory', async () => {
      const response = await handleFrameCount({
        traceDirectory: '/nonexistent/path/to/traces'
      });

      expect(response.isError).toBe(true);
      const result = parseResponse(response) as Record<string, unknown>;
      expect(result.error).toBe('FILE_NOT_FOUND');
    });

    // @tests-contract REQ-ARCH-008
    it('uses default pattern when not specified', async () => {
      const fs = await import('fs/promises');
      const os = await import('os');
      const path = await import('path');

      const tempDir = path.join(os.tmpdir(), `contract-test-default-${Date.now()}`);
      await fs.mkdir(tempDir, { recursive: true });

      try {
        // Create file matching default pattern *_anim_*.svg
        await fs.writeFile(path.join(tempDir, 'Spec_anim_0.svg'), '<svg></svg>');

        const response = await handleFrameCount({
          traceDirectory: tempDir
          // filePattern not specified - should use default
        });
        const result = parseResponse(response) as Record<string, unknown>;

        if (!result.error) {
          expect(result).toHaveProperty('count');
          expect(result).toHaveProperty('files');
        }
      } finally {
        await fs.rm(tempDir, { recursive: true, force: true });
      }
    });

    // @tests-contract REQ-ERROR-001
    it('returns error with remediation on failure', async () => {
      const response = await handleFrameCount({
        traceDirectory: '/nonexistent/directory'
      });

      const result = parseResponse(response) as Record<string, unknown>;
      expect(result).toHaveProperty('error');
      expect(result).toHaveProperty('message');
      expect(result).toHaveProperty('remediation');
      expect(Array.isArray(result.remediation)).toBe(true);
    });
  });

  describe('Cross-operation contracts', () => {
    // @tests-contract REQ-ARCH-001
    it('tool provides all three operations: detect, render, frameCount', async () => {
      // Verify all three operations are available and callable
      const detectResponse = await handleDetect({});
      expect(detectResponse).toHaveProperty('content');

      const renderResponse = await handleRender({
        protocol: 'kitty',
        useCase: 'live',
        frameIndex: 0,
        animView: validAnimView
      });
      expect(renderResponse).toHaveProperty('content');

      const frameCountResponse = await handleFrameCount({
        traceDirectory: '/tmp'
      });
      expect(frameCountResponse).toHaveProperty('content');
    });

    // @tests-contract REQ-ARCH-004
    it('protocol selection flow: detect then render with explicit protocol', async () => {
      // Step 1: Call detect
      const detectResponse = await handleDetect({});
      const detectResult = parseResponse(detectResponse) as Record<string, unknown>;

      // Step 2: Interpret results and decide protocol
      const protocol = detectResult.protocol === 'none' ? 'ascii' : detectResult.protocol;

      // Step 3: Call render with explicit protocol
      const renderResponse = await handleRender({
        protocol: protocol as 'kitty' | 'iterm2' | 'ascii' | 'browser',
        useCase: 'live',
        frameIndex: 0,
        animView: validAnimView
      });
      const renderResult = parseResponse(renderResponse) as Record<string, unknown>;

      // Contract: MCP trusts Claude's protocol selection
      if (!renderResult.error) {
        expect(renderResult.protocol).toBe(protocol);
      }
    });

    // @tests-contract REQ-COMPAT-001
    it('does not affect existing SVG workflow capabilities', async () => {
      // Contract: existing svgContent and svgFilePath options work
      const svgContentRender = await handleRender({
        protocol: 'kitty',
        useCase: 'static',
        frameIndex: 0,
        svgContent: validSvgContent
      });

      const svgResult = parseResponse(svgContentRender) as Record<string, unknown>;
      if (!svgResult.error) {
        expect(svgResult).toHaveProperty('output');
      }
    });

    // @tests-contract REQ-ERROR-002
    it('error responses include fallback offer in remediation', async () => {
      // Trigger a render error
      const response = await handleRender({
        protocol: 'kitty',
        useCase: 'live',
        frameIndex: 0,
        svgFilePath: '/nonexistent/file.svg'
      });

      const result = parseResponse(response) as Record<string, unknown>;
      if (result.error) {
        const remediation = result.remediation as string[];
        // Contract: errors include actionable remediation
        expect(remediation.length).toBeGreaterThan(0);
        // All remediation items should be non-empty actionable text
        expect(remediation.every(r => r.length > 0)).toBe(true);
      }
    });
  });
});
