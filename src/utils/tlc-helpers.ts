import * as fs from 'fs';
import * as path from 'path';
import { buildJavaOptions, findJavaExecutable } from './java';
import { withRetry } from './errors';
import { runProcess } from './process-runner';
import { getClassPath, getModuleSearchPaths } from './tla-tools';
import { mapTlcOutputLine } from './tlc';

const TLC_MAIN_CLASS = 'tlc2.TLC';

/**
 * Result of running TLC
 */
export interface TlcResult {
  exitCode: number;
  output: string[];
}

/**
 * Progress callback for TLC execution
 */
export type TlcProgressCallback = (progress: {
  progress: number;
  total?: number;
  message?: string;
}) => void;

/**
 * Specification files (TLA and CFG)
 */
export interface SpecFiles {
  tlaFilePath: string;
  cfgFilePath: string;
}

export async function runTlcAndWait(
  tlaFilePath: string,
  cfgFileName: string,
  tlcOptions: string[],
  javaOpts: string[],
  toolsDir: string,
  javaHome?: string,
  timeoutMs?: number,
  signal?: AbortSignal,
  onProgress?: TlcProgressCallback
): Promise<TlcResult> {
  const classPath = getClassPath(toolsDir);
  const moduleSearchPaths = getModuleSearchPaths(toolsDir);

  const libPaths = moduleSearchPaths
    .filter(p => !p.startsWith('jarfile:'))
    .join(path.delimiter);

  const javaOptions = javaOpts.slice();
  if (libPaths) {
    javaOptions.push(`-DTLA-Library=${libPaths}`);
  }

  const tlaFileName = path.basename(tlaFilePath);
  const args = [tlaFileName, '-tool', '-modelcheck'];
  if (cfgFileName) {
    args.push('-config', cfgFileName);
  }
  args.push(...tlcOptions);

  const javaPath = findJavaExecutable(javaHome);
  const fullArgs = buildJavaOptions(javaOptions, classPath)
    .concat([TLC_MAIN_CLASS])
    .concat(args);

  const result = await withRetry(async () => {
    const attemptResult = await runProcess({
      command: javaPath,
      args: fullArgs,
      cwd: path.dirname(tlaFilePath),
      timeoutMs,
      signal
    });

    if (!attemptResult.timedOut && !attemptResult.aborted && attemptResult.exitCode === null) {
      const errorDetails = attemptResult.stderr || attemptResult.combined || 'Unknown error.';
      throw new Error(`Failed to launch Java process using "${javaPath}": ${errorDetails}`);
    }

    return attemptResult;
  });

  let lastProgressTime = Date.now();
  const progressIntervalMs = 10000;

  const output: string[] = [];
  if (result.combined.length > 0) {
    const lines = result.combined.split(/\r?\n/);
    for (let i = 0; i < lines.length; i++) {
      const line = lines[i];
      const cleanedLine = mapTlcOutputLine(line);
      if (cleanedLine !== undefined) {
        output.push(cleanedLine);
      }

      if (onProgress) {
        const now = Date.now();
        if (now - lastProgressTime >= progressIntervalMs) {
          onProgress({
            progress: i + 1,
            total: lines.length,
            message: `Processing TLC output: ${i + 1}/${lines.length} lines`
          });
          lastProgressTime = now;
        }
      }
    }
  }

  if (result.timedOut) {
    output.push(`TLC process timed out after ${timeoutMs ?? 0}ms.`);
  }
  if (result.aborted) {
    output.push('TLC process was aborted.');
  }

  const exitCode = result.exitCode ?? (result.timedOut ? 124 : result.aborted ? 130 : 0);

  return { exitCode, output };
}

/**
 * Find specification files (TLA and CFG) for a given TLA file
 * Looks for matching .cfg file or MC*.tla/MC*.cfg files
 *
 * @param tlaFilePath Path to the TLA+ file
 * @returns SpecFiles if found, null otherwise
 */
export async function getSpecFiles(tlaFilePath: string): Promise<SpecFiles | null> {
  const dir = path.dirname(tlaFilePath);
  const baseName = path.basename(tlaFilePath, '.tla');

  // First, try the simple case: MySpec.tla -> MySpec.cfg
  const simpleCfg = path.join(dir, `${baseName}.cfg`);
  if (fs.existsSync(simpleCfg)) {
    return {
      tlaFilePath,
      cfgFilePath: simpleCfg
    };
  }

  // Second, try the MC prefix pattern: MySpec.tla -> MCMySpec.tla + MCMySpec.cfg
  const mcBaseName = `MC${baseName}`;
  const mcTlaPath = path.join(dir, `${mcBaseName}.tla`);
  const mcCfgPath = path.join(dir, `${mcBaseName}.cfg`);

  if (fs.existsSync(mcTlaPath) && fs.existsSync(mcCfgPath)) {
    return {
      tlaFilePath: mcTlaPath,
      cfgFilePath: mcCfgPath
    };
  }

  // No config file found
  return null;
}
