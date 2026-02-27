import * as fs from 'fs';
import * as path from 'path';
import * as paths from './paths';

/**
 * OpenCode Skills Installer
 *
 * Installs TLA+ AI Tools skills into OpenCode by creating symlinks (or copying on Windows).
 *
 * INSTALLATION:
 * - Target: ~/.config/opencode/skills/{skill-name}/ (Linux/macOS)
 *           %APPDATA%\opencode\skills\{skill-name}\ (Windows)
 * - Source: {pluginRoot}/skills/{skill-name}/
 * - Use case: Globally installed package
 *
 * SYMLINK-FIRST STRATEGY:
 * - Try to create symlink first (fast, no duplication)
 * - If symlink fails (Windows without admin, unsupported filesystem), fall back to copy
 * - Symlink entire skill directory, not just SKILL.md
 *
 * IDEMPOTENCY:
 * - If symlink/copy already exists and points to correct source, do nothing
 * - If target exists but is incorrect, report error (don't overwrite)
 * - Safe to run multiple times
 */

/**
 * Result of installing a single skill
 */
export interface SkillInstallResult {
  /** Skill name */
  skillName: string;
  /** Target path where skill was installed */
  targetPath: string;
  /** Source path of skill */
  sourcePath: string;
  /** Whether skill was newly installed */
  installed: boolean;
  /** Whether symlink was used (true) or copy (false) */
  symlinked: boolean;
  /** Error message if installation failed */
  error?: string;
}

/**
 * Result of installing all skills
 */
export interface InstallSkillsResult {
  /** Target directory where skills were installed */
  targetDir: string;
  /** Source directory containing skills */
  sourceDir: string;
  /** Results for each skill */
  skills: SkillInstallResult[];
  /** Overall success (all skills installed) */
  success: boolean;
  /** Number of skills installed */
  installedCount: number;
  /** Number of skills that were already installed */
  alreadyInstalledCount: number;
  /** Number of skills that failed to install */
  failedCount: number;
}

/**
 * Enumerate all skill directories in the source directory.
 * 
 * A valid skill directory contains a SKILL.md file.
 * 
 * @param sourceDir - Source directory containing skills (e.g., {repo}/skills/)
 * @returns Array of skill names (directory names)
 */
export function enumerateSkills(sourceDir: string): string[] {
  if (!fs.existsSync(sourceDir)) {
    return [];
  }

  const entries = fs.readdirSync(sourceDir, { withFileTypes: true });
  const skills: string[] = [];

  for (const entry of entries) {
    if (!entry.isDirectory()) {
      continue;
    }

    // Check if directory contains SKILL.md
    const skillMdPath = path.join(sourceDir, entry.name, 'SKILL.md');
    if (fs.existsSync(skillMdPath)) {
      skills.push(entry.name);
    }
  }

  return skills.sort();
}

/**
 * Check if a target path is already correctly installed.
 * 
 * Returns true if:
 * - Target is a symlink pointing to sourcePath
 * - Target is a directory with same content as sourcePath
 * 
 * @param targetPath - Target installation path
 * @param sourcePath - Source skill directory
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

  // @implements REQ-CODEX-010, SCN-CODEX-010-01, SCN-CODEX-010-02, SCN-CODEX-010-03
  if (targetStat.isDirectory()) {
    try {
      const targetSkillMd = path.join(targetPath, 'SKILL.md');
      const sourceSkillMd = path.join(sourcePath, 'SKILL.md');
      const targetContent = fs.readFileSync(targetSkillMd, 'utf-8');
      const sourceContent = fs.readFileSync(sourceSkillMd, 'utf-8');
      return targetContent === sourceContent;
    } catch {
      // If SKILL.md is missing or unreadable in either location, not installed
      return false;
    }
  }

  return false;
}

/**
 * Install a single skill by creating a symlink or copying.
 * 
 * Strategy:
 * 1. Check if already installed (idempotency)
 * 2. Try to create symlink
 * 3. If symlink fails, fall back to copy
 * 
 * @param skillName - Name of skill to install
 * @param sourcePath - Source skill directory
 * @param targetPath - Target installation path
 * @returns Installation result
 */
function installSkill(
  skillName: string,
  sourcePath: string,
  targetPath: string
): SkillInstallResult {
  // Check if source exists
  if (!fs.existsSync(sourcePath)) {
    return {
      skillName,
      sourcePath,
      targetPath,
      installed: false,
      symlinked: false,
      error: `Source directory not found: ${sourcePath}`,
    };
  }

  // Check if already installed
  if (isAlreadyInstalled(targetPath, sourcePath)) {
    const isSymlink = fs.lstatSync(targetPath).isSymbolicLink();
    return {
      skillName,
      sourcePath,
      targetPath,
      installed: false,
      symlinked: isSymlink,
    };
  }

  // @implements REQ-CODEX-011, SCN-CODEX-011-02, SCN-CODEX-011-03
  // If target exists but is stale, remove before reinstalling
  if (fs.existsSync(targetPath)) {
    try {
      fs.rmSync(targetPath, { recursive: true, force: true });
    } catch (rmError) {
      return {
        skillName,
        sourcePath,
        targetPath,
        installed: false,
        symlinked: false,
        error: `Failed to remove stale target: ${rmError instanceof Error ? rmError.message : String(rmError)}`,
      };
    }
  }

  // Try to create symlink first
  try {
    fs.symlinkSync(sourcePath, targetPath, 'dir');
    return {
      skillName,
      sourcePath,
      targetPath,
      installed: true,
      symlinked: true,
    };
  } catch (symlinkError) {
    // Symlink failed, fall back to copy
    try {
      copyDirectory(sourcePath, targetPath);
      return {
        skillName,
        sourcePath,
        targetPath,
        installed: true,
        symlinked: false,
      };
    } catch (copyError) {
      return {
        skillName,
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
 * Recursively copy a directory.
 * 
 * @param src - Source directory
 * @param dest - Destination directory
 */
function copyDirectory(src: string, dest: string): void {
  // Create destination directory
  fs.mkdirSync(dest, { recursive: true });

  // Read source directory
  const entries = fs.readdirSync(src, { withFileTypes: true });

  for (const entry of entries) {
    const srcPath = path.join(src, entry.name);
    const destPath = path.join(dest, entry.name);

    if (entry.isDirectory()) {
      // Recursively copy subdirectory
      copyDirectory(srcPath, destPath);
    } else if (entry.isFile() || entry.isSymbolicLink()) {
      // Copy file (preserving symlinks)
      fs.copyFileSync(srcPath, destPath);
    }
  }
}

/**
 * Install all skills into OpenCode globally.
 *
 * - Source: {pluginRoot}/skills/
 * - Target: ~/.config/opencode/skills/ (or platform equivalent)
 *
 * @param pluginRoot - Plugin root directory (optional, auto-detected if not provided)
 * @returns Installation result
 */
export function installSkills(
  pluginRoot?: string
): InstallSkillsResult {
  // Auto-detect plugin root if not provided
  if (!pluginRoot) {
    pluginRoot = path.resolve(__dirname, '..', '..');
  }

  // Source and target directories
  const sourceDir = path.join(pluginRoot, 'skills');
  const { getGlobalOpenCodeDir } = require('./paths');
  const targetBaseDir = getGlobalOpenCodeDir();

  // Get canonical skills directory (creates if missing)
  const targetDir = paths.getCanonicalDir(targetBaseDir, 'skill', true);

  // Enumerate skills
  const skillNames = enumerateSkills(sourceDir);

  // Install each skill
  const skillResults: SkillInstallResult[] = [];
  for (const skillName of skillNames) {
    const sourcePath = path.join(sourceDir, skillName);
    const targetPath = path.join(targetDir, skillName);
    const result = installSkill(skillName, sourcePath, targetPath);
    skillResults.push(result);
  }

  // Calculate summary statistics
  const installedCount = skillResults.filter((r) => r.installed).length;
  const alreadyInstalledCount = skillResults.filter((r) => !r.installed && !r.error).length;
  const failedCount = skillResults.filter((r) => r.error).length;
  const success = failedCount === 0;

  return {
    targetDir,
    sourceDir,
    skills: skillResults,
    success,
    installedCount,
    alreadyInstalledCount,
    failedCount,
  };
}

/**
 * Uninstall a single skill.
 * 
 * Removes the skill directory from the target location.
 * Safe to call even if skill is not installed.
 * 
 * @param skillName - Name of skill to uninstall
 * @param targetDir - Target directory containing skills
 * @returns True if skill was uninstalled, false if it wasn't installed
 */
export function uninstallSkill(skillName: string, targetDir: string): boolean {
  const targetPath = path.join(targetDir, skillName);

  if (!fs.existsSync(targetPath)) {
    return false;
  }

  // Remove directory (recursively)
  fs.rmSync(targetPath, { recursive: true, force: true });
  return true;
}

/**
 * Uninstall all skills from OpenCode globally.
 *
 * @returns Number of skills uninstalled
 */
export function uninstallAllSkills(): number {
  // Get global OpenCode directory
  const { getGlobalOpenCodeDir } = require('./paths');
  const targetBaseDir = getGlobalOpenCodeDir();

  // Get skills directory (don't create if missing)
  const targetDir = paths.getCanonicalDir(targetBaseDir, 'skill', false);

  if (!fs.existsSync(targetDir)) {
    return 0;
  }

  // Enumerate installed skills
  const entries = fs.readdirSync(targetDir, { withFileTypes: true });
  let uninstalledCount = 0;

  for (const entry of entries) {
    if (entry.isDirectory() || entry.isSymbolicLink()) {
      const skillPath = path.join(targetDir, entry.name);
      fs.rmSync(skillPath, { recursive: true, force: true });
      uninstalledCount++;
    }
  }

  return uninstalledCount;
}
