import * as fs from 'fs';
import * as path from 'path';

const TLA_TOOLS_LIB_NAME = 'tla2tools.jar';
const TLA_CMODS_LIB_NAME = 'CommunityModules-deps.jar';

/**
 * Get path to tla2tools.jar in the tools directory
 *
 * @param toolsDir Path to tools directory
 * @returns Full path to tla2tools.jar
 * @throws Error if file doesn't exist
 */
export function getTlaToolsJarPath(toolsDir: string): string {
  const jarPath = path.join(toolsDir, TLA_TOOLS_LIB_NAME);

  if (!fs.existsSync(jarPath)) {
    throw new Error(
      `TLA+ tools jar not found: ${jarPath}\n\n` +
      `Please ensure ${TLA_TOOLS_LIB_NAME} exists in the tools directory, or use --tools-dir to specify the correct location.`
    );
  }

  return jarPath;
}

/**
 * Get path to CommunityModules-deps.jar in the tools directory
 *
 * @param toolsDir Path to tools directory
 * @returns Full path to CommunityModules-deps.jar
 * @throws Error if file doesn't exist
 */
export function getCommunityModulesJarPath(toolsDir: string): string {
  const jarPath = path.join(toolsDir, TLA_CMODS_LIB_NAME);

  if (!fs.existsSync(jarPath)) {
    throw new Error(
      `Community modules jar not found: ${jarPath}\n\n` +
      `Please ensure ${TLA_CMODS_LIB_NAME} exists in the tools directory, or use --tools-dir to specify the correct location.`
    );
  }

  return jarPath;
}

/**
 * Get classpath string for both TLA+ jars
 * Includes tla2tools.jar and CommunityModules-deps.jar
 *
 * @param toolsDir Path to tools directory
 * @returns Classpath string with both jars separated by path delimiter
 */
export function getClassPath(toolsDir: string): string {
  const tlaToolsJar = getTlaToolsJarPath(toolsDir);
  const cmodsJar = getCommunityModulesJarPath(toolsDir);

  return [tlaToolsJar, cmodsJar].join(path.delimiter);
}

/**
 * Get module search paths for TLA+ standard modules
 * Returns paths in the jarfile: scheme format for use as module lookup paths
 *
 * @param toolsDir Path to tools directory
 * @returns Array of module search paths
 */
export function getModuleSearchPaths(toolsDir: string): string[] {
  const tlaToolsJar = getTlaToolsJarPath(toolsDir);
  const cmodsJar = getCommunityModulesJarPath(toolsDir);

  const TLA_TOOLS_STANDARD_MODULES = '/tla2sany/StandardModules';

  // Use jarfile: scheme instead of jar:file: for better compatibility
  return [
    `jarfile:${tlaToolsJar}!${TLA_TOOLS_STANDARD_MODULES}`,
    `jarfile:${cmodsJar}!/`
  ];
}
