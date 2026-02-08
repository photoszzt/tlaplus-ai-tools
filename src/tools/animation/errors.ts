/**
 * Error handling service for animation module.
 *
 * Spec: docs/tla-animations/spec.md
 * Contract: docs/tla-animations/contract.md
 *
 * @module animation/errors
 */

import { AnimationError, AnimationErrorCode } from './types';

/**
 * Error remediation mapping
 * @implements REQ-ERROR-001
 * NORMATIVE: SC-ANIM-014
 */
const ERROR_REMEDIATION: Record<AnimationErrorCode, { message: string; remediation: string[] }> = {
  DETECTION_TIMEOUT: {
    message: 'Terminal graphics detection timed out after 500ms',
    remediation: [
      'Try again or use ASCII fallback. If in tmux, ensure allow-passthrough is enabled.'
    ]
  },
  UNKNOWN_TERMINAL: {
    message: 'Could not detect terminal type from environment',
    remediation: [
      'Set TERM_PROGRAM or use --protocol to specify: kitty, iterm2, ascii'
    ]
  },
  PASSTHROUGH_NOT_ENABLED: {
    message: 'tmux detected but allow-passthrough is not enabled',
    remediation: [
      'Run: tmux set -g allow-passthrough on'
    ]
  },
  RENDER_FAILED: {
    message: 'Failed to render frame',
    remediation: [
      'Check error message for details',
      'Try using ASCII or browser fallback'
    ]
  },
  FRAME_TOO_LARGE: {
    message: 'Frame exceeds 1MB limit',
    remediation: [
      'Reduce animation complexity or canvas size'
    ]
  },
  INVALID_ANIMVIEW: {
    message: 'AnimView record missing required field',
    remediation: [
      'Ensure AnimView has: frame, title, width, height, elements'
    ]
  },
  NO_FALLBACK_AVAILABLE: {
    message: 'Terminal does not support graphics and no fallback was accepted. Options: set fallbackPreference to \'ascii\' or \'browser\', or use a graphics-capable terminal (Kitty, iTerm2).',
    remediation: [
      'Set TLAPLUS_ANIMATION_FALLBACK=ascii for ASCII art output',
      'Set TLAPLUS_ANIMATION_FALLBACK=browser to open in browser',
      'Use a terminal with graphics support (Kitty, iTerm2)'
    ]
  },
  FILE_NOT_FOUND: {
    message: 'File not found',
    remediation: [
      'Verify file path is correct',
      'Check file permissions'
    ]
  },
  INVALID_SVG: {
    message: 'Invalid SVG content',
    remediation: [
      'Ensure SVG is well-formed XML',
      'Check SVG syntax'
    ]
  }
};

/**
 * Create animation error response
 * @implements REQ-ERROR-001
 * @invariant INV-ERROR-001 (remediation array must be non-empty)
 * NORMATIVE: SC-ANIM-014
 * @param code - Error code
 * @param details - Additional details to include in message
 * @returns AnimationError object
 */
export function createAnimationError(
  code: AnimationErrorCode,
  details?: Record<string, unknown>
): AnimationError {
  const template = ERROR_REMEDIATION[code];
  let message = template.message;
  const remediation = [...template.remediation];

  // Add details to message if provided
  if (details) {
    if (details.specificError && typeof details.specificError === 'string') {
      message = `${template.message}: ${details.specificError}`;
    }
    if (details.path && typeof details.path === 'string') {
      message = `${template.message}: ${details.path}`;
    }
    if (details.actualSize && typeof details.actualSize === 'number') {
      message = `${template.message} (${formatBytes(details.actualSize)})`;
    }
    if (details.field && typeof details.field === 'string') {
      message = `${template.message}: ${details.field}`;
    }
    if (details.width && details.height) {
      remediation[0] = `${remediation[0]}. Current: ${details.width}x${details.height}`;
    }
  }

  // INV-ERROR-001: Validate remediation is non-empty
  if (remediation.length === 0) {
    throw new Error(`Implementation error: remediation for ${code} must be non-empty`);
  }

  return {
    error: code,
    message,
    remediation
  };
}

/**
 * Format bytes to human-readable string
 */
function formatBytes(bytes: number): string {
  if (bytes < 1024) {
    return `${bytes} bytes`;
  }
  if (bytes < 1024 * 1024) {
    return `${(bytes / 1024).toFixed(1)} KB`;
  }
  return `${(bytes / (1024 * 1024)).toFixed(2)} MB`;
}

/**
 * ErrorService class for animation errors
 * @implements REQ-ERROR-001, REQ-ERROR-002
 */
export class ErrorService {
  /**
   * Create a DETECTION_TIMEOUT error
   * @implements REQ-DETECT-001
   */
  detectionTimeout(): AnimationError {
    return createAnimationError('DETECTION_TIMEOUT');
  }

  /**
   * Create an UNKNOWN_TERMINAL error
   * @implements REQ-ERROR-001
   */
  unknownTerminal(): AnimationError {
    return createAnimationError('UNKNOWN_TERMINAL');
  }

  /**
   * Create a PASSTHROUGH_NOT_ENABLED error
   * @implements REQ-DETECT-002
   */
  passthroughNotEnabled(): AnimationError {
    return createAnimationError('PASSTHROUGH_NOT_ENABLED');
  }

  /**
   * Create a RENDER_FAILED error
   * @implements REQ-ERROR-001
   * @param specificError - The specific error message
   */
  renderFailed(specificError: string): AnimationError {
    return createAnimationError('RENDER_FAILED', { specificError });
  }

  /**
   * Create a FRAME_TOO_LARGE error
   * @implements REQ-ARCH-006
   * @invariant INV-RENDER-001 (frame size limit enforcement)
   * @param actualSize - Actual frame size in bytes
   * @param width - Canvas width
   * @param height - Canvas height
   */
  frameTooLarge(actualSize: number, width: number, height: number): AnimationError {
    return createAnimationError('FRAME_TOO_LARGE', { actualSize, width, height });
  }

  /**
   * Create an INVALID_ANIMVIEW error
   * @implements REQ-RENDER-004
   * @param field - The missing field name
   */
  invalidAnimView(field: string): AnimationError {
    return createAnimationError('INVALID_ANIMVIEW', { field });
  }

  /**
   * Create a NO_FALLBACK_AVAILABLE error
   * @implements REQ-FALLBACK-006
   */
  noFallbackAvailable(): AnimationError {
    return createAnimationError('NO_FALLBACK_AVAILABLE');
  }

  /**
   * Create a FILE_NOT_FOUND error
   * @implements REQ-ERROR-001
   * @param path - The file path that was not found
   */
  fileNotFound(path: string): AnimationError {
    return createAnimationError('FILE_NOT_FOUND', { path });
  }

  /**
   * Create an INVALID_SVG error
   * @implements REQ-ERROR-001
   * @param specificError - The specific parse error
   */
  invalidSvg(specificError: string): AnimationError {
    return createAnimationError('INVALID_SVG', { specificError });
  }
}

/**
 * Singleton error service instance
 */
export const errorService = new ErrorService();
