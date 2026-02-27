import * as fs from 'fs';
import * as path from 'path';
import * as os from 'os';

/**
 * OpenCode Path Resolution
 * 
 * This module defines canonical paths for OpenCode plugin directories and configuration files.
 * It handles backwards compatibility between singular/plural directory names and supports
 * both per-project and global configurations across Linux, macOS, and Windows.
 * 
 * PATH RESOLUTION MATRIX:
 * 
 * 1. Per-Project Directories (relative to project root):
 *    - Plugin directory: `.opencode/plugin/` OR `.opencode/plugins/` (prefer plural if both exist)
 *    - Commands directory: `.opencode/commands/` OR `.opencode/command/` (prefer plural if both exist)
 *    - Skills directory: `.opencode/skills/` OR `.opencode/skill/` (prefer plural if both exist)
 *    - Config file: `.opencode/opencode.json` OR `.opencode/opencode.jsonc`
 * 
 * 2. Global Directories (platform-specific):
 *    Linux:   ~/.config/opencode/
 *    macOS:   ~/.config/opencode/
 *    Windows: %APPDATA%\opencode\
 * 
 * 3. Global Subdirectories:
 *    - Plugins: {global}/plugins/ OR {global}/plugin/ (prefer plural)
 *    - Commands: {global}/commands/ OR {global}/command/ (prefer plural)
 *    - Skills: {global}/skills/ OR {global}/skill/ (prefer plural)
 *    - Config: {global}/opencode.json OR {global}/opencode.jsonc
 * 
 * PRECEDENCE RULES:
 * - When both singular and plural exist, prefer plural
 * - Per-project paths take precedence over global paths
 * - .json takes precedence over .jsonc when both exist
 * 
 * CONFIG FILE PARSING:
 * - Support both .json (strict JSON) and .jsonc (JSON with comments/trailing commas)
 * - Use tolerant parsing for .jsonc files
 */

/**
 * OpenCode directory types (singular and plural forms)
 */
export type OpenCodeDirType = 'plugin' | 'plugins' | 'command' | 'commands' | 'skill' | 'skills';

/**
 * Canonical OpenCode directory names (plural form preferred)
 */
export const CANONICAL_DIRS = {
  PLUGIN: 'plugins',
  COMMAND: 'commands',
  SKILL: 'skills',
} as const;

/**
 * OpenCode configuration file names
 */
export const CONFIG_FILENAMES = ['opencode.json', 'opencode.jsonc'] as const;

/**
 * Get the global OpenCode configuration directory for the current platform.
 * 
 * Platform-specific paths:
 * - Linux: ~/.config/opencode/
 * - macOS: ~/.config/opencode/
 * - Windows: %APPDATA%\opencode\
 * 
 * @returns Absolute path to global OpenCode config directory
 */
export function getGlobalOpenCodeDir(): string {
  const platform = os.platform();
  const homeDir = os.homedir();

  switch (platform) {
    case 'win32':
      // Windows: %APPDATA%\opencode\
      const appData = process.env.APPDATA;
      if (!appData) {
        throw new Error('APPDATA environment variable not set on Windows');
      }
      return path.join(appData, 'opencode');

    case 'darwin':
    case 'linux':
    default:
      // macOS and Linux: ~/.config/opencode/
      return path.join(homeDir, '.config', 'opencode');
  }
}

/**
 * Find an existing directory, preferring plural form over singular.
 * 
 * Checks for both singular and plural forms of a directory name.
 * If both exist, returns the plural form.
 * If only one exists, returns that one.
 * If neither exists, returns null.
 * 
 * @param baseDir - Base directory to search in
 * @param singularName - Singular form of directory name (e.g., 'plugin')
 * @param pluralName - Plural form of directory name (e.g., 'plugins')
 * @returns Absolute path to existing directory, or null if neither exists
 * 
 * @example
 * // If both .opencode/plugin/ and .opencode/plugins/ exist, returns .opencode/plugins/
 * findExistingDir('/project', 'plugin', 'plugins')
 * 
 * // If only .opencode/plugin/ exists, returns .opencode/plugin/
 * findExistingDir('/project', 'plugin', 'plugins')
 */
export function findExistingDir(
  baseDir: string,
  singularName: string,
  pluralName: string
): string | null {
  const pluralPath = path.join(baseDir, pluralName);
  const singularPath = path.join(baseDir, singularName);

  const pluralExists = fs.existsSync(pluralPath) && fs.statSync(pluralPath).isDirectory();
  const singularExists = fs.existsSync(singularPath) && fs.statSync(singularPath).isDirectory();

  // Prefer plural if both exist
  if (pluralExists) {
    return pluralPath;
  }

  // Fall back to singular
  if (singularExists) {
    return singularPath;
  }

  return null;
}

/**
 * Find OpenCode plugin directory in project or global location.
 * 
 * Search order:
 * 1. {projectRoot}/.opencode/plugins/ OR {projectRoot}/.opencode/plugin/
 * 2. {global}/plugins/ OR {global}/plugin/
 * 
 * @param projectRoot - Project root directory (optional)
 * @returns Absolute path to plugin directory, or null if not found
 */
export function findPluginDir(projectRoot?: string): string | null {
  // Check per-project location
  if (projectRoot) {
    const opencodeDir = path.join(projectRoot, '.opencode');
    const pluginDir = findExistingDir(opencodeDir, 'plugin', 'plugins');
    if (pluginDir) {
      return pluginDir;
    }
  }

  // Check global location
  const globalDir = getGlobalOpenCodeDir();
  return findExistingDir(globalDir, 'plugin', 'plugins');
}

/**
 * Find OpenCode commands directory in project or global location.
 * 
 * Search order:
 * 1. {projectRoot}/.opencode/commands/ OR {projectRoot}/.opencode/command/
 * 2. {global}/commands/ OR {global}/command/
 * 
 * @param projectRoot - Project root directory (optional)
 * @returns Absolute path to commands directory, or null if not found
 */
export function findCommandsDir(projectRoot?: string): string | null {
  // Check per-project location
  if (projectRoot) {
    const opencodeDir = path.join(projectRoot, '.opencode');
    const commandsDir = findExistingDir(opencodeDir, 'command', 'commands');
    if (commandsDir) {
      return commandsDir;
    }
  }

  // Check global location
  const globalDir = getGlobalOpenCodeDir();
  return findExistingDir(globalDir, 'command', 'commands');
}

/**
 * Find OpenCode skills directory in project or global location.
 * 
 * Search order:
 * 1. {projectRoot}/.opencode/skills/ OR {projectRoot}/.opencode/skill/
 * 2. {global}/skills/ OR {global}/skill/
 * 
 * @param projectRoot - Project root directory (optional)
 * @returns Absolute path to skills directory, or null if not found
 */
export function findSkillsDir(projectRoot?: string): string | null {
  // Check per-project location
  if (projectRoot) {
    const opencodeDir = path.join(projectRoot, '.opencode');
    const skillsDir = findExistingDir(opencodeDir, 'skill', 'skills');
    if (skillsDir) {
      return skillsDir;
    }
  }

  // Check global location
  const globalDir = getGlobalOpenCodeDir();
  return findExistingDir(globalDir, 'skill', 'skills');
}

/**
 * Find OpenCode configuration file.
 * 
 * Checks for both .json and .jsonc extensions.
 * Prefers .json over .jsonc when both exist.
 * 
 * Search order:
 * 1. {projectRoot}/.opencode/opencode.json
 * 2. {projectRoot}/.opencode/opencode.jsonc
 * 3. {global}/opencode.json
 * 4. {global}/opencode.jsonc
 * 
 * @param projectRoot - Project root directory (optional)
 * @returns Absolute path to config file, or null if not found
 */
export function findConfigFile(projectRoot?: string): string | null {
  const searchDirs: string[] = [];

  // Add per-project location
  if (projectRoot) {
    searchDirs.push(path.join(projectRoot, '.opencode'));
  }

  // Add global location
  searchDirs.push(getGlobalOpenCodeDir());

  // Search each directory for config files
  for (const dir of searchDirs) {
    for (const filename of CONFIG_FILENAMES) {
      const configPath = path.join(dir, filename);
      if (fs.existsSync(configPath) && fs.statSync(configPath).isFile()) {
        return configPath;
      }
    }
  }

  return null;
}

/**
 * Parse OpenCode configuration file with tolerant JSON parsing.
 * 
 * Supports both strict JSON (.json) and JSON with comments/trailing commas (.jsonc).
 * Uses a simple comment-stripping approach for .jsonc files.
 * 
 * @param configPath - Path to configuration file
 * @returns Parsed configuration object
 * @throws Error if file cannot be read or parsed
 */
export function parseConfigFile(configPath: string): unknown {
  const content = fs.readFileSync(configPath, 'utf-8');
  const ext = path.extname(configPath);

  if (ext === '.jsonc') {
    // Strip comments and trailing commas for JSONC
    const stripped = stripJsonComments(content);
    return JSON.parse(stripped);
  }

  // Standard JSON parsing
  return JSON.parse(content);
}

/**
 * Strip comments and trailing commas from JSON content.
 * 
 * This is a simple implementation that handles:
 * - Single-line comments: // comment
 * - Multi-line comments: /* comment *\/
 * - Trailing commas before } or ]
 * 
 * Note: This is not a full JSONC parser and may not handle all edge cases.
 * For production use, consider using a dedicated JSONC parsing library.
 * 
 * @param content - JSON content with comments
 * @returns JSON content with comments stripped
 */
// @implements REQ-CODEX-007, SCN-CODEX-007-01, SCN-CODEX-007-02, SCN-CODEX-007-03, SCN-CODEX-007-04
// @implements REQ-CODEX-008, SCN-CODEX-008-01, SCN-CODEX-008-02, SCN-CODEX-008-03
function stripJsonComments(content: string): string {
  let result = '';
  let i = 0;
  let inString = false;

  while (i < content.length) {
    const ch = content[i];

    if (inString) {
      // Inside a JSON string literal
      if (ch === '\\') {
        // Escaped character -- copy both the backslash and the next char
        result += ch;
        i++;
        if (i < content.length) {
          result += content[i];
          i++;
        }
        continue;
      }
      if (ch === '"') {
        // End of string
        inString = false;
        result += ch;
        i++;
        continue;
      }
      // Any other character inside string -- copy as-is
      result += ch;
      i++;
      continue;
    }

    // Outside string literal
    if (ch === '"') {
      // Start of string
      inString = true;
      result += ch;
      i++;
      continue;
    }

    if (ch === '/' && i + 1 < content.length) {
      const next = content[i + 1];
      if (next === '/') {
        // Single-line comment: skip to end of line
        i += 2;
        while (i < content.length && content[i] !== '\n') {
          i++;
        }
        // Keep the newline (preserves line structure)
        continue;
      }
      if (next === '*') {
        // Multi-line comment: skip to closing */
        i += 2;
        while (i + 1 < content.length && !(content[i] === '*' && content[i + 1] === '/')) {
          i++;
        }
        if (i + 1 < content.length) {
          i += 2; // skip the closing */
        }
        continue;
      }
    }

    // Regular character outside string
    result += ch;
    i++;
  }

  // Remove trailing commas before } or ]
  result = result.replace(/,(\s*[}\]])/g, '$1');

  return result;
}

/**
 * Get all OpenCode paths for a project.
 * 
 * Returns an object containing all resolved OpenCode paths:
 * - pluginDir: Plugin directory (per-project or global)
 * - commandsDir: Commands directory (per-project or global)
 * - skillsDir: Skills directory (per-project or global)
 * - configFile: Configuration file (per-project or global)
 * - globalDir: Global OpenCode directory
 * 
 * @param projectRoot - Project root directory (optional)
 * @returns Object containing all resolved paths (null for paths not found)
 */
export function getOpenCodePaths(projectRoot?: string): {
  pluginDir: string | null;
  commandsDir: string | null;
  skillsDir: string | null;
  configFile: string | null;
  globalDir: string;
} {
  return {
    pluginDir: findPluginDir(projectRoot),
    commandsDir: findCommandsDir(projectRoot),
    skillsDir: findSkillsDir(projectRoot),
    configFile: findConfigFile(projectRoot),
    globalDir: getGlobalOpenCodeDir(),
  };
}

/**
 * Ensure a directory exists, creating it if necessary.
 * 
 * Creates the directory and any necessary parent directories.
 * 
 * @param dirPath - Path to directory
 * @throws Error if directory cannot be created
 */
export function ensureDir(dirPath: string): void {
  if (!fs.existsSync(dirPath)) {
    fs.mkdirSync(dirPath, { recursive: true });
  }
}

/**
 * Get the canonical (preferred) path for an OpenCode directory.
 * 
 * Returns the plural form path, creating it if createIfMissing is true.
 * 
 * @param baseDir - Base directory (e.g., .opencode/ or global dir)
 * @param dirType - Type of directory ('plugin', 'command', or 'skill')
 * @param createIfMissing - Create directory if it doesn't exist (default: false)
 * @returns Absolute path to canonical directory
 */
export function getCanonicalDir(
  baseDir: string,
  dirType: 'plugin' | 'command' | 'skill',
  createIfMissing = false
): string {
  const pluralName = dirType === 'plugin' ? 'plugins' : dirType === 'command' ? 'commands' : 'skills';
  const canonicalPath = path.join(baseDir, pluralName);

  if (createIfMissing) {
    ensureDir(canonicalPath);
  }

  return canonicalPath;
}
