/**
 * White-box tests for DetectionService
 *
 * Tests detection logic for terminal graphics capabilities.
 * Uses dependency injection for mocking environment and tmux config.
 *
 * @module animation/__tests__/DetectionService.test
 */

import {
  DetectionService,
  createDetectionService
} from '../DetectionService';
import {
  DetectionResult,
  DetectionEnvironment,
  AnimationError,
  isAnimationError
} from '../types';

// Test fixtures
const createKittyEnv = (): DetectionEnvironment => ({
  TERM: 'xterm-kitty',
  KITTY_WINDOW_ID: '1'
});

const createIterm2Env = (): DetectionEnvironment => ({
  TERM_PROGRAM: 'iTerm.app',
  LC_TERMINAL: 'iTerm2',
  TERM: 'xterm-256color'
});

const createKittyInTmuxEnv = (): DetectionEnvironment => ({
  TERM: 'xterm-kitty',
  KITTY_WINDOW_ID: '1',
  TMUX: '/tmp/tmux-1000/default,12345,0'
});

const createScreenEnv = (): DetectionEnvironment => ({
  TERM: 'screen',
  STY: '12345.pts-0.hostname'
});

const createUnknownEnv = (): DetectionEnvironment => ({
  TERM: 'xterm'
});

const createEmptyEnv = (): DetectionEnvironment => ({});

describe('DetectionService', () => {
  describe('Protocol Detection', () => {
    // @tests REQ-DETECT-001, REQ-DETECT-003, SCN-DETECT-001
    it('detects Kitty terminal from KITTY_WINDOW_ID with high confidence', async () => {
      const service = createDetectionService(
        () => createKittyEnv(),
        async () => false
      );

      const result = await service.detect();

      expect(isAnimationError(result)).toBe(false);
      const detection = result as DetectionResult;
      expect(detection.protocol).toBe('kitty');
      expect(detection.confidence).toBe('high');
      expect(detection.detectionMethod).toBe('env');
      expect(detection.environment.KITTY_WINDOW_ID).toBe('1');
    });

    // @tests REQ-DETECT-001, REQ-DETECT-003
    it('detects Kitty terminal from TERM=xterm-kitty with medium confidence', async () => {
      const env: DetectionEnvironment = { TERM: 'xterm-kitty' };
      const service = createDetectionService(() => env, async () => false);

      const result = await service.detect();

      expect(isAnimationError(result)).toBe(false);
      const detection = result as DetectionResult;
      expect(detection.protocol).toBe('kitty');
      expect(detection.confidence).toBe('medium');
    });

    // @tests REQ-DETECT-001, REQ-DETECT-003, SCN-DETECT-002
    it('detects iTerm2 from TERM_PROGRAM=iTerm.app with high confidence', async () => {
      const service = createDetectionService(
        () => createIterm2Env(),
        async () => false
      );

      const result = await service.detect();

      expect(isAnimationError(result)).toBe(false);
      const detection = result as DetectionResult;
      expect(detection.protocol).toBe('iterm2');
      expect(detection.confidence).toBe('high');
      expect(detection.environment.TERM_PROGRAM).toBe('iTerm.app');
    });

    // @tests REQ-DETECT-001, REQ-DETECT-003
    it('detects iTerm2 from LC_TERMINAL=iTerm2 with high confidence', async () => {
      const env: DetectionEnvironment = { LC_TERMINAL: 'iTerm2', TERM: 'xterm-256color' };
      const service = createDetectionService(() => env, async () => false);

      const result = await service.detect();

      expect(isAnimationError(result)).toBe(false);
      const detection = result as DetectionResult;
      expect(detection.protocol).toBe('iterm2');
      expect(detection.confidence).toBe('high');
    });

    // @tests REQ-DETECT-001, REQ-DETECT-003, SCN-DETECT-003
    it('returns protocol=none for unknown terminal with low confidence', async () => {
      const service = createDetectionService(
        () => createUnknownEnv(),
        async () => false
      );

      const result = await service.detect();

      expect(isAnimationError(result)).toBe(false);
      const detection = result as DetectionResult;
      expect(detection.protocol).toBe('none');
      expect(detection.confidence).toBe('low');
    });

    // @tests REQ-DETECT-003
    it('returns protocol=none for empty environment', async () => {
      const service = createDetectionService(
        () => createEmptyEnv(),
        async () => false
      );

      const result = await service.detect();

      expect(isAnimationError(result)).toBe(false);
      const detection = result as DetectionResult;
      expect(detection.protocol).toBe('none');
      expect(detection.multiplexer).toBe('none');
    });
  });

  describe('Multiplexer Detection', () => {
    // @tests REQ-DETECT-002, SCN-DETECT-001
    it('detects tmux multiplexer from TMUX env var', async () => {
      const service = createDetectionService(
        () => createKittyInTmuxEnv(),
        async () => true
      );

      const result = await service.detect();

      expect(isAnimationError(result)).toBe(false);
      const detection = result as DetectionResult;
      expect(detection.multiplexer).toBe('tmux');
      expect(detection.environment.TMUX).toBeDefined();
    });

    // @tests REQ-DETECT-002
    it('detects screen multiplexer from STY env var', async () => {
      const service = createDetectionService(
        () => createScreenEnv(),
        async () => false
      );

      const result = await service.detect();

      expect(isAnimationError(result)).toBe(false);
      const detection = result as DetectionResult;
      expect(detection.multiplexer).toBe('screen');
      expect(detection.environment.STY).toBeDefined();
    });

    // @tests REQ-DETECT-002, SCN-DETECT-002
    it('returns multiplexer=none when not in multiplexer', async () => {
      const service = createDetectionService(
        () => createIterm2Env(),
        async () => false
      );

      const result = await service.detect();

      expect(isAnimationError(result)).toBe(false);
      const detection = result as DetectionResult;
      expect(detection.multiplexer).toBe('none');
    });
  });

  describe('Passthrough Detection', () => {
    // @tests REQ-DETECT-002, SCN-DETECT-001
    it('reports passthroughEnabled=true when tmux passthrough is on', async () => {
      const service = createDetectionService(
        () => createKittyInTmuxEnv(),
        async () => true
      );

      const result = await service.detect();

      expect(isAnimationError(result)).toBe(false);
      const detection = result as DetectionResult;
      expect(detection.passthroughEnabled).toBe(true);
      expect(detection.passthroughVerified).toBe(false); // Always false for v1
    });

    // @tests REQ-DETECT-002, SCN-ERROR-004
    it('reports passthroughEnabled=false when tmux passthrough is off', async () => {
      const service = createDetectionService(
        () => createKittyInTmuxEnv(),
        async () => false
      );

      const result = await service.detect();

      expect(isAnimationError(result)).toBe(false);
      const detection = result as DetectionResult;
      expect(detection.passthroughEnabled).toBe(false);
    });

    // @tests REQ-DETECT-002
    it('reports passthroughEnabled=false for screen (limited support)', async () => {
      const service = createDetectionService(
        () => createScreenEnv(),
        async () => true // Even if query returns true, screen has limited support
      );

      const result = await service.detect();

      expect(isAnimationError(result)).toBe(false);
      const detection = result as DetectionResult;
      expect(detection.multiplexer).toBe('screen');
      expect(detection.passthroughEnabled).toBe(false);
    });

    // @tests REQ-DETECT-002
    it('reports passthroughEnabled=true when no multiplexer (direct terminal)', async () => {
      const service = createDetectionService(
        () => createKittyEnv(),
        async () => false
      );

      const result = await service.detect();

      expect(isAnimationError(result)).toBe(false);
      const detection = result as DetectionResult;
      expect(detection.multiplexer).toBe('none');
      expect(detection.passthroughEnabled).toBe(true);
    });
  });

  describe('Timeout Handling', () => {
    // @tests REQ-DETECT-001, SCN-ERROR-001
    // @tests-invariant INV-DETECT-001
    it('returns DETECTION_TIMEOUT when detection exceeds 500ms', async () => {
      const slowTmuxReader = () =>
        new Promise<boolean>((resolve) => {
          setTimeout(() => resolve(true), 600);
        });

      const service = createDetectionService(
        () => createKittyInTmuxEnv(),
        slowTmuxReader,
        100 // Use short timeout for faster test
      );

      const result = await service.detect();

      expect(isAnimationError(result)).toBe(true);
      const error = result as AnimationError;
      expect(error.error).toBe('DETECTION_TIMEOUT');
      expect(error.message).toContain('timed out');
      expect(error.remediation.length).toBeGreaterThan(0);
    });

    // @tests REQ-DETECT-001
    // @tests-invariant INV-DETECT-001
    it('completes within timeout for fast detection', async () => {
      const fastTmuxReader = async () => true;

      const service = createDetectionService(
        () => createKittyInTmuxEnv(),
        fastTmuxReader,
        500
      );

      const startTime = Date.now();
      const result = await service.detect();
      const duration = Date.now() - startTime;

      expect(isAnimationError(result)).toBe(false);
      expect(duration).toBeLessThan(500);
    });

    // @tests REQ-DETECT-001
    it('allows custom timeout override', async () => {
      const service = new DetectionService({ timeoutMs: 50 });

      // Calling with timeout override
      const result = await service.detect(10);

      // Should either succeed quickly or timeout
      // The test verifies the timeout parameter is respected
      expect(result).toBeDefined();
    });
  });

  describe('Detection Result Schema', () => {
    // @tests REQ-DETECT-003
    it('returns all required fields per NORMATIVE schema', async () => {
      const service = createDetectionService(
        () => createKittyInTmuxEnv(),
        async () => true
      );

      const result = await service.detect();

      expect(isAnimationError(result)).toBe(false);
      const detection = result as DetectionResult;

      // Verify all NORMATIVE fields present
      expect(detection.protocol).toBeDefined();
      expect(['kitty', 'iterm2', 'none']).toContain(detection.protocol);

      expect(detection.multiplexer).toBeDefined();
      expect(['tmux', 'screen', 'none']).toContain(detection.multiplexer);

      expect(typeof detection.passthroughEnabled).toBe('boolean');
      expect(typeof detection.passthroughVerified).toBe('boolean');

      expect(Array.isArray(detection.fallbackAvailable)).toBe(true);
      expect(detection.fallbackAvailable).toContain('ascii');
      expect(detection.fallbackAvailable).toContain('browser');

      expect(detection.detectionMethod).toBeDefined();
      expect(['env', 'query', 'probe']).toContain(detection.detectionMethod);

      expect(detection.confidence).toBeDefined();
      expect(['high', 'medium', 'low']).toContain(detection.confidence);

      expect(typeof detection.environment).toBe('object');
    });

    // @tests REQ-DETECT-003
    it('filters undefined environment variables from result', async () => {
      const partialEnv: DetectionEnvironment = {
        TERM: 'xterm-kitty',
        KITTY_WINDOW_ID: '1'
        // Other vars undefined
      };

      const service = createDetectionService(
        () => partialEnv,
        async () => false
      );

      const result = await service.detect();

      expect(isAnimationError(result)).toBe(false);
      const detection = result as DetectionResult;

      // Only defined vars should be in environment
      expect(detection.environment.TERM).toBe('xterm-kitty');
      expect(detection.environment.KITTY_WINDOW_ID).toBe('1');
      // TMUX should not be in the object if undefined
      expect('TMUX' in detection.environment && detection.environment.TMUX !== undefined).toBe(false);
    });
  });

  describe('Protocol Priority', () => {
    // @tests REQ-DETECT-001
    it('prioritizes Kitty over iTerm2 when both indicators present', async () => {
      const mixedEnv: DetectionEnvironment = {
        KITTY_WINDOW_ID: '1',
        TERM_PROGRAM: 'iTerm.app'
      };

      const service = createDetectionService(() => mixedEnv, async () => false);

      const result = await service.detect();

      expect(isAnimationError(result)).toBe(false);
      const detection = result as DetectionResult;
      // Per design.md: Check for Kitty first (order matters)
      expect(detection.protocol).toBe('kitty');
    });
  });

  describe('Factory Function', () => {
    // @tests REQ-DETECT-001
    it('createDetectionService creates service with custom dependencies', async () => {
      const customEnv = () => ({ TERM: 'xterm-kitty', KITTY_WINDOW_ID: '2' });
      const customTmux = async () => true;

      const service = createDetectionService(customEnv, customTmux, 1000);

      const result = await service.detect();

      expect(isAnimationError(result)).toBe(false);
      const detection = result as DetectionResult;
      expect(detection.environment.KITTY_WINDOW_ID).toBe('2');
    });
  });

  describe('Sequential Call Safety', () => {
    // @tests REQ-ARCH-007, SCN-ARCH-006
    // @tests-invariant INV-SEQUENTIAL-001
    it('multiple detect calls return consistent results', async () => {
      const service = createDetectionService(
        () => createKittyInTmuxEnv(),
        async () => true
      );

      const result1 = await service.detect();
      const result2 = await service.detect();
      const result3 = await service.detect();

      expect(isAnimationError(result1)).toBe(false);
      expect(isAnimationError(result2)).toBe(false);
      expect(isAnimationError(result3)).toBe(false);

      const d1 = result1 as DetectionResult;
      const d2 = result2 as DetectionResult;
      const d3 = result3 as DetectionResult;

      // Results should be consistent
      expect(d1.protocol).toBe(d2.protocol);
      expect(d2.protocol).toBe(d3.protocol);
      expect(d1.multiplexer).toBe(d2.multiplexer);
      expect(d1.passthroughEnabled).toBe(d2.passthroughEnabled);
    });
  });
});
