/**
 * Frame count service for trace navigation.
 *
 * Spec: docs/tla-animations/spec.md
 * Contract: docs/tla-animations/contract.md
 *
 * @module animation/FrameCountService
 */

import * as fs from 'fs/promises';
import * as path from 'path';

import {
  FrameCountResult,
  AnimationError,
  FileSystemService
} from './types';
import { createAnimationError } from './errors';

/**
 * Default file pattern for trace files
 * NORMATIVE: SC-ANIM-026
 */
const DEFAULT_FILE_PATTERN = '*_anim_*.svg';

/**
 * Convert simple glob pattern to regex
 * @param pattern - Glob pattern with * and ? wildcards
 * @returns RegExp for matching filenames
 */
function globToRegex(pattern: string): RegExp {
  const escaped = pattern
    .replace(/[.+^${}()|[\]\\]/g, '\\$&')
    .replace(/\*/g, '.*')
    .replace(/\?/g, '.');
  return new RegExp(`^${escaped}$`);
}

/**
 * Extract frame number from filename
 * @param filePath - Full path to file
 * @returns Frame number extracted from filename, or 0 if not found
 */
function extractFrameNumber(filePath: string): number {
  const filename = path.basename(filePath);
  // Match patterns like: _0.svg, _1.svg, _anim_5.svg, etc.
  const match = filename.match(/_(\d+)\./);
  return match ? parseInt(match[1], 10) : 0;
}

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
 * Check if path is a directory
 * @param dirPath - Path to check
 * @returns true if path is a directory
 */
async function isDirectory(dirPath: string): Promise<boolean> {
  try {
    const stat = await fs.stat(dirPath);
    return stat.isDirectory();
  } catch {
    return false;
  }
}

/**
 * Options for FrameCountService
 */
export interface FrameCountServiceOptions {
  /** File system service (for testing) */
  fileSystem?: FileSystemService;
}

/**
 * FrameCountService provides frame enumeration for trace navigation.
 * @implements REQ-ARCH-008
 * NORMATIVE: SC-ANIM-026
 *
 * This service is responsible for:
 * - Validating trace directory existence
 * - Finding files matching the specified pattern
 * - Sorting files by frame number
 * - Returning count and sorted file list for navigation
 */
export class FrameCountService {
  private fileSystem: FileSystemService;

  /**
   * Create frame count service with dependency injection
   * @param options - Frame count service options for testability
   */
  constructor(options: FrameCountServiceOptions = {}) {
    this.fileSystem = options.fileSystem ?? createDefaultFileSystem();
  }

  /**
   * Get count and list of animation frames in trace directory
   * @implements REQ-ARCH-008
   * NORMATIVE: SC-ANIM-026
   *
   * Per contract.md section 2.1.3:
   * - Directory is scanned for files matching pattern
   * - Files are sorted by frame number extracted from filename
   * - Returns count and sorted file list
   *
   * @param traceDirectory - Directory containing SVG animation files
   * @param filePattern - Glob pattern (default: "*_anim_*.svg")
   * @returns { count: number, files: string[] } - sorted by frame number
   * @throws AnimationError with FILE_NOT_FOUND if directory doesn't exist
   */
  async frameCount(
    traceDirectory: string,
    filePattern: string = DEFAULT_FILE_PATTERN
  ): Promise<FrameCountResult | AnimationError> {
    // Step 1: Validate traceDirectory exists
    // Per SC-ANIM-014: FILE_NOT_FOUND error if directory doesn't exist
    const exists = await this.fileSystem.exists(traceDirectory);
    if (!exists) {
      return createAnimationError('FILE_NOT_FOUND', { path: traceDirectory });
    }

    // Additional validation: ensure it's a directory, not a file
    const isDir = await isDirectory(traceDirectory);
    if (!isDir) {
      return createAnimationError('FILE_NOT_FOUND', {
        path: traceDirectory,
        specificError: 'Path exists but is not a directory'
      });
    }

    // Step 2: Find files matching pattern (use glob)
    try {
      const files = await this.fileSystem.glob(filePattern, traceDirectory);

      // Step 3: Sort files by frame number
      const sortedFiles = files.sort((a, b) => {
        const numA = extractFrameNumber(a);
        const numB = extractFrameNumber(b);
        return numA - numB;
      });

      // Step 4: Return { count, files }
      return {
        count: sortedFiles.length,
        files: sortedFiles
      };
    } catch (error) {
      // Handle any errors during file enumeration
      const message = error instanceof Error ? error.message : String(error);
      return createAnimationError('RENDER_FAILED', {
        specificError: `Failed to enumerate files: ${message}`
      });
    }
  }
}

/**
 * Factory function for creating frame count service with dependency injection
 * @implements REQ-ARCH-008
 * @param fileSystem - File system abstraction (for testing)
 * @returns FrameCountService instance
 */
export function createFrameCountService(
  fileSystem?: FileSystemService
): FrameCountService {
  return new FrameCountService({ fileSystem });
}
