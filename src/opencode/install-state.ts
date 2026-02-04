import * as fs from 'fs';
import * as path from 'path';

/**
 * Install State Management
 *
 * This module manages the installation state marker file for the TLA+ OpenCode plugin.
 * The marker file prevents repeated installation prompts and tracks installation status.
 *
 * MARKER FILE LOCATION:
 * - Global: {globalDir}/.tlaplus-install-state.json
 *
 * MARKER FILE SCHEMA:
 * {
 *   "state": "installed" | "declined" | "error",
 *   "version": "2.0.0",
 *   "timestamp": "2026-02-02T19:30:00.000Z"
 * }
 */

/**
 * Installation state values
 */
export type InstallState = 'installed' | 'declined' | 'error';

/**
 * Install state marker file structure
 */
export interface InstallStateMarker {
  state: InstallState;
  version: string;
  timestamp: string;
}

/**
 * Marker file name
 */
const MARKER_FILENAME = '.tlaplus-install-state.json';

/**
 * Current plugin version (should match package.json)
 */
const PLUGIN_VERSION = '2.0.0';

/**
 * Get the path to the marker file.
 *
 * @param globalDir - Global OpenCode directory
 * @returns Absolute path to marker file
 */
export function getMarkerPath(globalDir: string): string {
  return path.join(globalDir, MARKER_FILENAME);
}

/**
 * Read the install state marker file.
 *
 * @param markerPath - Path to marker file
 * @returns Parsed marker object, or null if file doesn't exist or is invalid
 */
export function readInstallState(markerPath: string): InstallStateMarker | null {
  try {
    if (!fs.existsSync(markerPath)) {
      return null;
    }

    const content = fs.readFileSync(markerPath, 'utf-8');
    const marker = JSON.parse(content) as InstallStateMarker;

    // Validate marker structure
    if (
      !marker.state ||
      !marker.version ||
      !marker.timestamp ||
      !['installed', 'declined', 'error'].includes(marker.state)
    ) {
      return null;
    }

    return marker;
  } catch (error) {
    // Invalid JSON or read error - treat as missing
    return null;
  }
}

/**
 * Write the install state marker file atomically.
 *
 * Uses atomic write pattern: write to temp file, then rename.
 * Creates parent directory if missing.
 *
 * @param markerPath - Path to marker file
 * @param state - Installation state
 * @throws Error if write fails
 */
export function writeInstallState(
  markerPath: string,
  state: InstallState
): void {
  const marker: InstallStateMarker = {
    state,
    version: PLUGIN_VERSION,
    timestamp: new Date().toISOString(),
  };

  const content = JSON.stringify(marker, null, 2) + '\n';
  const tempPath = `${markerPath}.tmp`;

  // Ensure parent directory exists
  const dir = path.dirname(markerPath);
  if (!fs.existsSync(dir)) {
    fs.mkdirSync(dir, { recursive: true });
  }

  // Atomic write: temp file + rename
  fs.writeFileSync(tempPath, content, 'utf-8');
  fs.renameSync(tempPath, markerPath);
}

/**
 * Check if installation prompt should be shown.
 *
 * Returns true only if no marker file exists (any state).
 * If marker exists with any state (installed, declined, error), returns false.
 *
 * @param markerPath - Path to marker file
 * @returns True if prompt should be shown, false otherwise
 */
export function shouldPromptInstall(markerPath: string): boolean {
  const marker = readInstallState(markerPath);
  return marker === null;
}
