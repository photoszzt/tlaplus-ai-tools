import * as fs from 'fs';
import * as path from 'path';
import { parseConfigFile } from './paths';

/**
 * OpenCode Configuration Patcher
 *
 * Safely patches OpenCode configuration files to enable the TLA+ MCP server.
 *
 * KEY FEATURES:
 * - Tolerant parsing: Handles JSON and JSONC (comments, trailing commas)
 * - Surgical patching: Only modifies `mcp.tlaplus`, preserves all other keys
 * - Atomic writes: Uses temp file + rename to prevent corruption
 * - Backup creation: Creates .bak file once (never overwrites existing backups)
 * - Idempotent: Running twice produces identical output
 *
 * GLOBAL INSTALLATION:
 * - Command: ['tlaplus-ai-tools'] (uses npm global bin)
 * - Requires: Package installed globally via npm
 * - Use case: End-user installation
 *
 * ERROR HANDLING:
 * - Invalid JSON → parse error with line/column info
 * - Write failures → atomic operation prevents corruption
 */

/**
 * MCP server configuration
 */
export interface McpServerConfig {
  type: 'local';
  command: string[];
  enabled: boolean;
}

/**
 * OpenCode configuration structure (partial)
 */
export interface OpenCodeConfig {
  mcp?: {
    [serverName: string]: McpServerConfig;
  };
  [key: string]: unknown;
}

/**
 * Result of patching operation
 */
export interface PatchResult {
  success: boolean;
  configPath: string;
  backupPath?: string;
  created: boolean;
  modified: boolean;
  error?: string;
}

/**
 * Patch OpenCode configuration to enable TLA+ MCP server globally.
 *
 * This function:
 * 1. Reads existing config (or creates new one)
 * 2. Patches only the `mcp.tlaplus` section
 * 3. Preserves all other configuration keys
 * 4. Writes atomically (temp file + rename)
 * 5. Creates backup of original (once)
 *
 * @param configPath - Path to OpenCode config file
 * @param pluginRoot - Plugin root directory (for validation)
 * @returns Result of patching operation
 *
 * @example
 * const result = await patchOpenCodeConfig(
 *   '~/.config/opencode/opencode.json',
 *   '/path/to/plugin'
 * );
 */
export async function patchOpenCodeConfig(
  configPath: string,
  pluginRoot: string
): Promise<PatchResult> {
  try {
    // Read or create config
    let config: OpenCodeConfig;
    let created = false;
    let originalContent: string | null = null;

    if (fs.existsSync(configPath)) {
      // Parse existing config
      try {
        config = parseConfigFile(configPath) as OpenCodeConfig;
        originalContent = fs.readFileSync(configPath, 'utf-8');
      } catch (parseError) {
        return {
          success: false,
          configPath,
          created: false,
          modified: false,
          error: `Failed to parse config: ${parseError instanceof Error ? parseError.message : String(parseError)}`,
        };
      }
    } else {
      // Create new config
      config = {};
      created = true;
    }

    // Patch MCP configuration
    const { patched, modified } = patchMcpConfig(config);

    // Skip write if no changes needed
    if (!created && !modified) {
      return {
        success: true,
        configPath,
        created: false,
        modified: false,
      };
    }

    // Create backup of original (once)
    let backupPath: string | undefined;
    if (originalContent && !created) {
      backupPath = await createBackup(configPath, originalContent);
    }

    // Write atomically
    await writeConfigAtomic(configPath, patched);

    return {
      success: true,
      configPath,
      backupPath,
      created,
      modified,
    };
  } catch (error) {
    return {
      success: false,
      configPath,
      created: false,
      modified: false,
      error: error instanceof Error ? error.message : String(error),
    };
  }
}

/**
 * Patch MCP configuration section.
 * 
 * Only modifies `mcp.tlaplus`, preserves all other keys.
 * 
 * @param config - OpenCode configuration object
 * @param mode - Installation mode
 * @returns Patched config and whether it was modified
 */
function patchMcpConfig(
  config: OpenCodeConfig
): { patched: OpenCodeConfig; modified: boolean } {
  // Ensure mcp section exists
  if (!config.mcp) {
    config.mcp = {};
  }

  // Get desired MCP config (global mode)
  const desiredConfig = getMcpServerConfig();

  // Check if already configured correctly
  const existing = config.mcp.tlaplus;
  const alreadyCorrect =
    existing &&
    existing.type === desiredConfig.type &&
    existing.enabled === desiredConfig.enabled &&
    arraysEqual(existing.command, desiredConfig.command);

  if (alreadyCorrect) {
    return { patched: config, modified: false };
  }

  // Patch tlaplus MCP server config
  config.mcp.tlaplus = desiredConfig;

  return { patched: config, modified: true };
}

/**
 * Get MCP server configuration for global installation.
 *
 * @returns MCP server configuration
 */
function getMcpServerConfig(): McpServerConfig {
  return {
    type: 'local',
    command: ['tlaplus-ai-tools'],
    enabled: true,
  };
}

/**
 * Compare two arrays for equality.
 * 
 * @param a - First array
 * @param b - Second array
 * @returns True if arrays are equal
 */
function arraysEqual(a: string[], b: string[]): boolean {
  if (a.length !== b.length) return false;
  return a.every((val, idx) => val === b[idx]);
}

/**
 * Create backup of original config file.
 * 
 * Creates a .bak file once. Never overwrites existing backups.
 * 
 * @param configPath - Path to config file
 * @param content - Original content
 * @returns Path to backup file, or undefined if backup already exists
 */
async function createBackup(configPath: string, content: string): Promise<string | undefined> {
  const backupPath = `${configPath}.bak`;

  // Don't overwrite existing backup
  if (fs.existsSync(backupPath)) {
    return undefined;
  }

  // Write backup
  fs.writeFileSync(backupPath, content, 'utf-8');
  return backupPath;
}

/**
 * Write configuration file atomically.
 * 
 * Uses temp file + rename to prevent corruption.
 * 
 * @param configPath - Path to config file
 * @param config - Configuration object
 */
async function writeConfigAtomic(configPath: string, config: OpenCodeConfig): Promise<void> {
  // Ensure directory exists
  const dir = path.dirname(configPath);
  if (!fs.existsSync(dir)) {
    fs.mkdirSync(dir, { recursive: true });
  }

  // Write to temp file
  const tempPath = `${configPath}.tmp`;
  const content = JSON.stringify(config, null, 2) + '\n';
  fs.writeFileSync(tempPath, content, 'utf-8');

  // Atomic rename
  fs.renameSync(tempPath, configPath);
}

/**
 * Check if config is already correctly patched for global installation.
 *
 * Useful for idempotency checks and avoiding unnecessary writes.
 *
 * @param configPath - Path to config file
 * @returns True if config is already correctly patched
 */
export function isConfigPatched(configPath: string): boolean {
  if (!fs.existsSync(configPath)) {
    return false;
  }

  try {
    const config = parseConfigFile(configPath) as OpenCodeConfig;
    const desiredConfig = getMcpServerConfig();
    const existing = config.mcp?.tlaplus;

    return (
      existing !== undefined &&
      existing.type === desiredConfig.type &&
      existing.enabled === desiredConfig.enabled &&
      arraysEqual(existing.command, desiredConfig.command)
    );
  } catch {
    return false;
  }
}
