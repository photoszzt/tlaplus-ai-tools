import * as path from 'path';
import { ProcessInfo, runJavaCommand } from './java';
import { getClassPath, getModuleSearchPaths } from './tla-tools';

const TLC_MAIN_CLASS = 'tlc2.TLC';

/**
 * Run TLC model checker on a TLA+ file with configuration
 *
 * @param tlaFilePath Path to the TLA+ file
 * @param cfgFileName Name of the configuration file (e.g., "Model.cfg")
 * @param tlcOptions TLC-specific options (e.g., -workers, -coverage)
 * @param javaOpts Java options (e.g., -Xmx, -D properties)
 * @param toolsDir Path to tools directory containing tla2tools.jar
 * @param javaHome Optional JAVA_HOME path
 * @returns ProcessInfo with the spawned process
 */
export async function runTlc(
  tlaFilePath: string,
  cfgFileName: string,
  tlcOptions: string[],
  javaOpts: string[],
  toolsDir: string,
  javaHome?: string
): Promise<ProcessInfo> {
  const classPath = getClassPath(toolsDir);
  const moduleSearchPaths = getModuleSearchPaths(toolsDir);

  // Build TLA-Library Java option from module search paths
  // Filter out jarfile: paths for now (TODO: support archive paths)
  const libPaths = moduleSearchPaths
    .filter(p => !p.startsWith('jarfile:'))
    .join(path.delimiter);

  const javaOptions = javaOpts.slice();
  if (libPaths) {
    javaOptions.push(`-DTLA-Library=${libPaths}`);
  }

  // Build TLC arguments: [tlaFileName] -tool -modelcheck [options]
  const tlaFileName = path.basename(tlaFilePath);
  const args = [tlaFileName, '-tool', '-modelcheck'];

  // Add -config option if cfgFileName is provided
  if (cfgFileName) {
    args.push('-config', cfgFileName);
  }

  // Add user-specified TLC options
  args.push(...tlcOptions);

  return await runJavaCommand(
    classPath,
    TLC_MAIN_CLASS,
    args,
    javaOptions,
    javaHome,
    path.dirname(tlaFilePath)
  );
}

/**
 * Map a TLC output line for clean display
 * Removes TLC's internal message markers (@!@!@START/END MSG)
 *
 * @param line Line from TLC output
 * @returns Cleaned line, or undefined if line should be skipped
 */
export function mapTlcOutputLine(line: string): string | undefined {
  if (line === '') {
    return line;
  }

  // Remove TLC message markers
  const cleanLine = line.replace(/@!@!@(START|END)MSG \d+(:\d+)? @!@!@/g, '');

  return cleanLine === '' ? undefined : cleanLine;
}
