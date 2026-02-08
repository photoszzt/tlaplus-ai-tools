/**
 * Detection service for terminal graphics capabilities.
 *
 * Spec: docs/tla-animations/spec.md
 * Contract: docs/tla-animations/contract.md
 *
 * @module animation/DetectionService
 */

import { spawn } from 'child_process';
import {
  DetectionResult,
  DetectionEnvironment,
  DetectionServiceOptions,
  GraphicsProtocol,
  Multiplexer,
  ConfidenceLevel,
  FallbackOption,
  AnimationError
} from './types';
import { createAnimationError } from './errors';

/**
 * Default timeout for detection in milliseconds
 * @invariant INV-DETECT-001 (detection timeout guarantee)
 */
const DEFAULT_TIMEOUT_MS = 500;

/**
 * Timeout for tmux config query in milliseconds
 */
const TMUX_QUERY_TIMEOUT_MS = 200;

/**
 * Default environment reader that reads from process.env
 */
function defaultEnvReader(): DetectionEnvironment {
  return {
    TERM: process.env.TERM,
    TERM_PROGRAM: process.env.TERM_PROGRAM,
    KITTY_WINDOW_ID: process.env.KITTY_WINDOW_ID,
    TMUX: process.env.TMUX,
    STY: process.env.STY,
    LC_TERMINAL: process.env.LC_TERMINAL
  };
}

/**
 * Default tmux config reader that spawns tmux to check passthrough
 */
async function defaultTmuxConfigReader(): Promise<boolean> {
  return new Promise((resolve) => {
    const timeout = setTimeout(() => {
      resolve(false);
    }, TMUX_QUERY_TIMEOUT_MS);

    try {
      const proc = spawn('tmux', ['show', '-g', 'allow-passthrough'], {
        stdio: ['ignore', 'pipe', 'pipe']
      });

      let output = '';

      proc.stdout.on('data', (data) => {
        output += data.toString();
      });

      proc.on('close', (code) => {
        clearTimeout(timeout);
        if (code === 0) {
          // Output format: "allow-passthrough on" or "allow-passthrough off"
          const enabled = output.toLowerCase().includes('on');
          resolve(enabled);
        } else {
          resolve(false);
        }
      });

      proc.on('error', () => {
        clearTimeout(timeout);
        resolve(false);
      });
    } catch {
      clearTimeout(timeout);
      resolve(false);
    }
  });
}

/**
 * Detect terminal multiplexer from environment
 * @implements REQ-DETECT-002
 * @param env - Detection environment variables
 * @returns Detected multiplexer
 */
function detectMultiplexer(env: DetectionEnvironment): Multiplexer {
  if (env.TMUX) {
    return 'tmux';
  }
  if (env.STY) {
    return 'screen';
  }
  return 'none';
}

/**
 * Detect graphics protocol from environment
 * @implements REQ-DETECT-001, REQ-DETECT-003
 * @param env - Detection environment variables
 * @returns Detected protocol
 */
function detectProtocol(env: DetectionEnvironment): GraphicsProtocol {
  // Check for Kitty (order matters per design.md)
  if (env.KITTY_WINDOW_ID || env.TERM === 'xterm-kitty') {
    return 'kitty';
  }

  // Check for iTerm2
  if (env.TERM_PROGRAM === 'iTerm.app' || env.LC_TERMINAL === 'iTerm2') {
    return 'iterm2';
  }

  return 'none';
}

/**
 * Determine confidence level based on detection method
 * @implements REQ-DETECT-003
 * @param protocol - Detected protocol
 * @param env - Detection environment variables
 * @returns Confidence level
 */
function determineConfidence(
  protocol: GraphicsProtocol,
  env: DetectionEnvironment
): ConfidenceLevel {
  if (protocol === 'kitty') {
    // High confidence if direct env var match
    if (env.KITTY_WINDOW_ID) {
      return 'high';
    }
    // Medium if inferred from TERM
    if (env.TERM === 'xterm-kitty') {
      return 'medium';
    }
  }

  if (protocol === 'iterm2') {
    // High confidence if direct TERM_PROGRAM match
    if (env.TERM_PROGRAM === 'iTerm.app') {
      return 'high';
    }
    // High confidence for LC_TERMINAL
    if (env.LC_TERMINAL === 'iTerm2') {
      return 'high';
    }
  }

  // Low confidence for fallback/no detection
  return 'low';
}

/**
 * Filter environment to only include set values
 * @param env - Full detection environment
 * @returns Environment with only defined values
 */
function filterEnvironment(env: DetectionEnvironment): DetectionEnvironment {
  const filtered: DetectionEnvironment = {};
  if (env.TERM !== undefined) filtered.TERM = env.TERM;
  if (env.TERM_PROGRAM !== undefined) filtered.TERM_PROGRAM = env.TERM_PROGRAM;
  if (env.KITTY_WINDOW_ID !== undefined) filtered.KITTY_WINDOW_ID = env.KITTY_WINDOW_ID;
  if (env.TMUX !== undefined) filtered.TMUX = env.TMUX;
  if (env.STY !== undefined) filtered.STY = env.STY;
  if (env.LC_TERMINAL !== undefined) filtered.LC_TERMINAL = env.LC_TERMINAL;
  return filtered;
}

/**
 * Detection service for terminal graphics capabilities
 * @implements REQ-DETECT-001, REQ-DETECT-002, REQ-DETECT-003
 */
export class DetectionService {
  private envReader: () => DetectionEnvironment;
  private tmuxConfigReader: () => Promise<boolean>;
  private timeoutMs: number;

  /**
   * Create detection service with dependency injection
   * @param options - Detection service options for testability
   */
  constructor(options: DetectionServiceOptions = {}) {
    this.envReader = options.envReader ?? defaultEnvReader;
    this.tmuxConfigReader = options.tmuxConfigReader ?? defaultTmuxConfigReader;
    this.timeoutMs = options.timeoutMs ?? DEFAULT_TIMEOUT_MS;
  }

  /**
   * Detect terminal graphics capabilities
   * @implements REQ-DETECT-001, REQ-DETECT-002, REQ-DETECT-003
   * @invariant INV-DETECT-001 (detection MUST complete within 500ms)
   * @param timeout - Optional timeout override in milliseconds
   * @returns Detection result or timeout error
   */
  async detect(timeout?: number): Promise<DetectionResult | AnimationError> {
    const effectiveTimeout = timeout ?? this.timeoutMs;

    // Create timeout promise for INV-DETECT-001 enforcement
    const timeoutPromise = new Promise<AnimationError>((resolve) => {
      setTimeout(() => {
        resolve(createAnimationError('DETECTION_TIMEOUT'));
      }, effectiveTimeout);
    });

    // Create detection promise
    const detectionPromise = this.performDetection();

    // Race detection against timeout (INV-DETECT-001)
    return Promise.race([detectionPromise, timeoutPromise]);
  }

  /**
   * Perform the actual detection logic
   * @returns Detection result
   */
  private async performDetection(): Promise<DetectionResult> {
    // Step 1: Read environment variables (per design.md 4.1)
    const env = this.envReader();

    // Step 2: Detect multiplexer (per design.md 4.1)
    const multiplexer = detectMultiplexer(env);

    // Step 3: Detect protocol (per design.md 4.1)
    const protocol = detectProtocol(env);

    // Step 4: Check passthrough (per design.md 4.1)
    let passthroughEnabled = true; // Default true when no multiplexer
    const passthroughVerified = false; // Always false for v1 per spec

    if (multiplexer === 'tmux') {
      passthroughEnabled = await this.tmuxConfigReader();
    } else if (multiplexer === 'screen') {
      // Screen has limited graphics support per design.md
      passthroughEnabled = false;
    }

    // If no multiplexer, passthrough is not applicable but set to true
    // to indicate graphics can work directly
    if (multiplexer === 'none') {
      passthroughEnabled = true;
    }

    // Step 5: Determine confidence (per design.md 4.1)
    const confidence = determineConfidence(protocol, env);

    // Step 6: Build and return result (per design.md 4.1)
    const fallbackAvailable: FallbackOption[] = ['ascii', 'browser'];

    return {
      protocol,
      multiplexer,
      passthroughEnabled,
      passthroughVerified,
      fallbackAvailable,
      detectionMethod: 'env',
      confidence,
      environment: filterEnvironment(env)
    };
  }
}

/**
 * Factory function for creating detection service with dependency injection
 * @implements REQ-DETECT-001, REQ-DETECT-002
 * @param envReader - Function to read environment variables (for testing)
 * @param tmuxConfigReader - Function to read tmux config (for testing)
 * @param timeoutMs - Detection timeout in milliseconds (default: 500)
 * @returns DetectionService instance
 */
export function createDetectionService(
  envReader?: () => DetectionEnvironment,
  tmuxConfigReader?: () => Promise<boolean>,
  timeoutMs?: number
): DetectionService {
  return new DetectionService({
    envReader,
    tmuxConfigReader,
    timeoutMs
  });
}
