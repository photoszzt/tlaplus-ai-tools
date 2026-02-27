import { execSync } from 'child_process';
import * as fs from 'fs';
import * as path from 'path';

/**
 * Resolve a file path and optionally validate its containment within the working directory.
 *
 * @implements REQ-CODEX-003, SCN-CODEX-003-01, SCN-CODEX-003-02, SCN-CODEX-003-03, SCN-CODEX-003-04
 * @implements REQ-CODEX-004, SCN-CODEX-004-01
 *
 * @param filePath - The file path to resolve (absolute or relative)
 * @param workingDir - Optional working directory to restrict access to
 * @returns Absolute path to the file
 * @throws Error if path is outside workingDir (when workingDir is set)
 */
export function resolveAndValidatePath(
  filePath: string,
  workingDir: string | null
): string {
  const absolute = path.isAbsolute(filePath)
    ? filePath
    : path.resolve(workingDir || process.cwd(), filePath);

  if (!workingDir) {
    return absolute;
  }

  // Attempt symlink-aware containment check
  try {
    const realAbsolute = fs.realpathSync(absolute);
    const realWorkingDir = fs.realpathSync(workingDir);
    const relative = path.relative(realWorkingDir, realAbsolute);

    if (relative.startsWith('..') || path.isAbsolute(relative)) {
      throw new Error(
        `Access denied: Path ${filePath} resolves to ${realAbsolute} which is outside the working directory ${realWorkingDir}`
      );
    }

    return absolute;
  } catch (err) {
    // If realpathSync fails because the file doesn't exist yet, fall back to lexical check
    if ((err as NodeJS.ErrnoException).code === 'ENOENT') {
      const relative = path.relative(workingDir, absolute);
      if (relative.startsWith('..') || path.isAbsolute(relative)) {
        throw new Error(
          `Access denied: Path ${filePath} is outside the working directory ${workingDir}`
        );
      }
      return absolute;
    }
    // Re-throw non-ENOENT errors (including our own "Access denied" thrown above)
    throw err;
  }
}

/**
 * Auto-detect the TLA+ tools directory by checking common locations
 * relative to the package installation.
 *
 * @returns Path to tools directory, or null if not found
 */
export async function autoDetectToolsDir(): Promise<string | null> {
  // Get package directory (two levels up from dist/utils/)
  const packageDir = path.join(__dirname, '..', '..');

  // Try relative paths from package directory
  const candidates = [
    path.join(packageDir, 'tools'),               // tools (standalone repo)
    path.join(packageDir, '..', 'tools'),         // ../tools
  ];

  // Add npm global fallback
  try {
    const npmRoot = execSync('npm root -g', { encoding: 'utf8' }).trim();
    candidates.push(
      path.join(npmRoot, 'tlaplus-ai-tools', 'tools')
    );
  } catch {
    // npm not available, skip
  }

  for (const candidate of candidates) {
    try {
      const stat = await fs.promises.stat(candidate);
      if (stat.isDirectory()) {
        // Check if it contains tla2tools.jar
        const tlaToolsJar = path.join(candidate, 'tla2tools.jar');
        try {
          await fs.promises.access(tlaToolsJar);
          return candidate;
        } catch {
          // Directory exists but doesn't contain tla2tools.jar
          continue;
        }
      }
    } catch {
      // Directory doesn't exist
      continue;
    }
  }

  return null;
}

/**
 * Auto-detect the knowledge base directory by checking common locations
 * relative to the package installation.
 *
 * @returns Path to knowledge base directory, or null if not found
 */
export async function autoDetectKbDir(): Promise<string | null> {
  // Get package directory (two levels up from dist/utils/)
  const packageDir = path.join(__dirname, '..', '..');

  // Try relative paths from package directory
  const candidates = [
    path.join(packageDir, 'resources', 'knowledgebase'),               // resources/knowledgebase (standalone repo)
    path.join(packageDir, '..', 'resources', 'knowledgebase'),         // ../resources/knowledgebase
  ];

  // Add npm global fallback
  try {
    const npmRoot = execSync('npm root -g', { encoding: 'utf8' }).trim();
    candidates.push(
      path.join(npmRoot, 'tlaplus-ai-tools', 'resources', 'knowledgebase')
    );
  } catch {
    // npm not available, skip
  }

  for (const candidate of candidates) {
    try {
      const stat = await fs.promises.stat(candidate);
      if (stat.isDirectory()) {
        // Check if it contains any .md files
        const files = await fs.promises.readdir(candidate);
        if (files.some(f => f.endsWith('.md'))) {
          return candidate;
        }
      }
    } catch {
      // Directory doesn't exist
      continue;
    }
  }

  return null;
}

/**
 * Validate that a directory exists.
 *
 * @param dirPath - Path to the directory
 * @param name - Human-readable name for error messages
 * @throws Error if directory doesn't exist or is not a directory
 */
export async function validateDirectory(
  dirPath: string,
  name: string
): Promise<void> {
  try {
    const stat = await fs.promises.stat(dirPath);
    if (!stat.isDirectory()) {
      throw new Error(
        `${name} path exists but is not a directory: ${dirPath}`
      );
    }
  } catch (error) {
    if ((error as NodeJS.ErrnoException).code === 'ENOENT') {
      throw new Error(
        `${name} directory not found: ${dirPath}\n\n` +
        `Please ensure the directory exists or specify a different path.`
      );
    }
    throw error;
  }
}
