import * as fs from 'fs';
import * as path from 'path';
import * as paths from './paths';

/**
 * OpenCode Commands Installer
 *
 * Installs TLA+ AI Tools commands into OpenCode by creating symlinks (or copying on Windows).
 *
 * INSTALLATION:
 * - Target: ~/.config/opencode/commands/{command-name}.md (Linux/macOS)
 *           %APPDATA%\opencode\commands\{command-name}.md (Windows)
 * - Source: {pluginRoot}/commands/{command-name}.md
 * - Use case: Globally installed package
 *
 * SYMLINK-FIRST STRATEGY:
 * - Try to create symlink first (fast, no duplication)
 * - If symlink fails (Windows without admin, unsupported filesystem), fall back to copy
 * - Symlink individual command files (.md)
 *
 * IDEMPOTENCY:
 * - If symlink/copy already exists and points to correct source, do nothing
 * - If target exists but is incorrect, report error (don't overwrite)
 * - Safe to run multiple times
 */

/**
 * Result of installing a single command
 */
export interface CommandInstallResult {
  /** Command name (without .md extension) */
  commandName: string;
  /** Target path where command was installed */
  targetPath: string;
  /** Source path of command */
  sourcePath: string;
  /** Whether command was newly installed */
  installed: boolean;
  /** Whether symlink was used (true) or copy (false) */
  symlinked: boolean;
  /** Error message if installation failed */
  error?: string;
}

/**
 * Result of installing all commands
 */
export interface InstallCommandsResult {
  /** Target directory where commands were installed */
  targetDir: string;
  /** Source directory containing commands */
  sourceDir: string;
  /** Results for each command */
  commands: CommandInstallResult[];
  /** Overall success (all commands installed) */
  success: boolean;
  /** Number of commands installed */
  installedCount: number;
  /** Number of commands that were already installed */
  alreadyInstalledCount: number;
  /** Number of commands that failed to install */
  failedCount: number;
}

/**
 * Enumerate all command files in the source directory.
 * 
 * A valid command file is a .md file in the commands directory.
 * 
 * @param sourceDir - Source directory containing commands (e.g., {repo}/commands/)
 * @returns Array of command names (filenames without .md extension)
 */
export function enumerateCommands(sourceDir: string): string[] {
  if (!fs.existsSync(sourceDir)) {
    return [];
  }

  const entries = fs.readdirSync(sourceDir, { withFileTypes: true });
  const commands: string[] = [];

  for (const entry of entries) {
    if (!entry.isFile()) {
      continue;
    }

    // Check if file has .md extension
    if (entry.name.endsWith('.md')) {
      // Remove .md extension to get command name
      const commandName = entry.name.slice(0, -3);
      commands.push(commandName);
    }
  }

  return commands.sort();
}

/**
 * Check if a target path is already correctly installed.
 * 
 * Returns true if:
 * - Target is a symlink pointing to sourcePath
 * - Target is a file with same content as sourcePath
 * 
 * @param targetPath - Target installation path
 * @param sourcePath - Source command file
 * @returns True if already correctly installed
 */
function isAlreadyInstalled(targetPath: string, sourcePath: string): boolean {
  if (!fs.existsSync(targetPath)) {
    return false;
  }

  const targetStat = fs.lstatSync(targetPath);

  // Check if it's a symlink pointing to the correct source
  if (targetStat.isSymbolicLink()) {
    const linkTarget = fs.readlinkSync(targetPath);
    // Resolve both paths to absolute for comparison
    const resolvedLink = path.resolve(path.dirname(targetPath), linkTarget);
    const resolvedSource = path.resolve(sourcePath);
    return resolvedLink === resolvedSource;
  }

  // If it's a file, we consider it already installed
  // (We don't verify content equality - too expensive)
  if (targetStat.isFile()) {
    return true;
  }

  return false;
}

/**
 * Install a single command by creating a symlink or copying.
 * 
 * Strategy:
 * 1. Check if already installed (idempotency)
 * 2. Try to create symlink
 * 3. If symlink fails, fall back to copy
 * 
 * @param commandName - Name of command to install (without .md extension)
 * @param sourcePath - Source command file
 * @param targetPath - Target installation path
 * @returns Installation result
 */
function installCommand(
  commandName: string,
  sourcePath: string,
  targetPath: string
): CommandInstallResult {
  // Check if source exists
  if (!fs.existsSync(sourcePath)) {
    return {
      commandName,
      sourcePath,
      targetPath,
      installed: false,
      symlinked: false,
      error: `Source file not found: ${sourcePath}`,
    };
  }

  // Check if already installed
  if (isAlreadyInstalled(targetPath, sourcePath)) {
    const isSymlink = fs.lstatSync(targetPath).isSymbolicLink();
    return {
      commandName,
      sourcePath,
      targetPath,
      installed: false,
      symlinked: isSymlink,
    };
  }

  // If target exists but is not correctly installed, report error
  if (fs.existsSync(targetPath)) {
    return {
      commandName,
      sourcePath,
      targetPath,
      installed: false,
      symlinked: false,
      error: `Target already exists but is not correctly installed: ${targetPath}`,
    };
  }

  // Try to create symlink first
  try {
    fs.symlinkSync(sourcePath, targetPath, 'file');
    return {
      commandName,
      sourcePath,
      targetPath,
      installed: true,
      symlinked: true,
    };
  } catch (symlinkError) {
    // Symlink failed, fall back to copy
    try {
      fs.copyFileSync(sourcePath, targetPath);
      return {
        commandName,
        sourcePath,
        targetPath,
        installed: true,
        symlinked: false,
      };
    } catch (copyError) {
      return {
        commandName,
        sourcePath,
        targetPath,
        installed: false,
        symlinked: false,
        error: `Failed to install: ${copyError instanceof Error ? copyError.message : String(copyError)}`,
      };
    }
  }
}

/**
 * Install all commands into OpenCode globally.
 *
 * - Source: {pluginRoot}/commands/
 * - Target: ~/.config/opencode/commands/ (or platform equivalent)
 *
 * @param pluginRoot - Plugin root directory (optional, auto-detected if not provided)
 * @returns Installation result
 */
export function installCommands(
  pluginRoot?: string
): InstallCommandsResult {
  // Auto-detect plugin root if not provided
  if (!pluginRoot) {
    pluginRoot = path.resolve(__dirname, '..', '..');
  }

  // Source and target directories
  const sourceDir = path.join(pluginRoot, 'commands');
  const { getGlobalOpenCodeDir } = require('./paths');
  const targetBaseDir = getGlobalOpenCodeDir();

  // Get canonical commands directory (creates if missing)
  const targetDir = paths.getCanonicalDir(targetBaseDir, 'command', true);

  // Enumerate commands
  const commandNames = enumerateCommands(sourceDir);

  // Install each command
  const commandResults: CommandInstallResult[] = [];
  for (const commandName of commandNames) {
    const sourcePath = path.join(sourceDir, `${commandName}.md`);
    const targetPath = path.join(targetDir, `${commandName}.md`);
    const result = installCommand(commandName, sourcePath, targetPath);
    commandResults.push(result);
  }

  // Calculate summary statistics
  const installedCount = commandResults.filter((r) => r.installed).length;
  const alreadyInstalledCount = commandResults.filter((r) => !r.installed && !r.error).length;
  const failedCount = commandResults.filter((r) => r.error).length;
  const success = failedCount === 0;

  return {
    targetDir,
    sourceDir,
    commands: commandResults,
    success,
    installedCount,
    alreadyInstalledCount,
    failedCount,
  };
}

/**
 * Uninstall a single command.
 * 
 * Removes the command file from the target location.
 * Safe to call even if command is not installed.
 * 
 * @param commandName - Name of command to uninstall (without .md extension)
 * @param targetDir - Target directory containing commands
 * @returns True if command was uninstalled, false if it wasn't installed
 */
export function uninstallCommand(commandName: string, targetDir: string): boolean {
  const targetPath = path.join(targetDir, `${commandName}.md`);

  if (!fs.existsSync(targetPath)) {
    return false;
  }

  // Remove file
  fs.rmSync(targetPath, { force: true });
  return true;
}

/**
 * Uninstall all commands from OpenCode globally.
 *
 * @returns Number of commands uninstalled
 */
export function uninstallAllCommands(): number {
  // Get global OpenCode directory
  const { getGlobalOpenCodeDir } = require('./paths');
  const targetBaseDir = getGlobalOpenCodeDir();

  // Get commands directory (don't create if missing)
  const targetDir = paths.getCanonicalDir(targetBaseDir, 'command', false);

  if (!fs.existsSync(targetDir)) {
    return 0;
  }

  // Enumerate installed commands
  const entries = fs.readdirSync(targetDir, { withFileTypes: true });
  let uninstalledCount = 0;

  for (const entry of entries) {
    if (entry.isFile() && entry.name.endsWith('.md')) {
      const commandPath = path.join(targetDir, entry.name);
      fs.rmSync(commandPath, { force: true });
      uninstalledCount++;
    }
  }

  return uninstalledCount;
}
