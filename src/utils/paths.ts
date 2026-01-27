import { execSync } from 'child_process';
import * as fs from 'fs';
import * as path from 'path';

/**
 * Resolve a file path and optionally validate it's within the working directory.
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
  // Resolve to absolute path
  const absolute = path.isAbsolute(filePath)
    ? filePath
    : path.resolve(workingDir || process.cwd(), filePath);

  // If no workingDir specified, allow any path
  if (!workingDir) {
    return absolute;
  }

  // Validate path is within workingDir
  const relative = path.relative(workingDir, absolute);

  // Check for path traversal attempts
  if (relative.startsWith('..') || path.isAbsolute(relative)) {
    throw new Error(
      `Access denied: Path ${filePath} is outside the working directory ${workingDir}`
    );
  }

  return absolute;
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
    path.join(packageDir, '..', '..', 'tools'),  // ../../tools (monorepo)
    path.join(packageDir, '..', 'tools'),         // ../tools
  ];

  // Add npm global fallback
  try {
    const npmRoot = execSync('npm root -g', { encoding: 'utf8' }).trim();
    candidates.push(
      path.join(npmRoot, '@tlaplus', 'mcp-server', 'tools')
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
    path.join(packageDir, '..', '..', 'resources', 'knowledgebase'),  // ../../resources/knowledgebase
    path.join(packageDir, '..', 'resources', 'knowledgebase'),         // ../resources/knowledgebase
  ];

  // Add npm global fallback
  try {
    const npmRoot = execSync('npm root -g', { encoding: 'utf8' }).trim();
    candidates.push(
      path.join(npmRoot, '@tlaplus', 'mcp-server', 'resources', 'knowledgebase')
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
