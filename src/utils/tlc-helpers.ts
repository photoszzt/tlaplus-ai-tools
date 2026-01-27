import * as fs from 'fs';
import * as path from 'path';
import { createInterface } from 'readline';
import { ProcessInfo } from './java';
import { runTlc, mapTlcOutputLine } from './tlc';

/**
 * Result of running TLC
 */
export interface TlcResult {
  exitCode: number;
  output: string[];
}

/**
 * Specification files (TLA and CFG)
 */
export interface SpecFiles {
  tlaFilePath: string;
  cfgFilePath: string;
}

/**
 * Run TLC and wait for completion, collecting all output
 *
 * @param tlaFilePath Path to the TLA+ file
 * @param cfgFileName Name of the configuration file
 * @param tlcOptions TLC-specific options
 * @param javaOpts Java options
 * @param toolsDir Path to tools directory
 * @param javaHome Optional JAVA_HOME path
 * @returns TLC result with exit code and output
 */
export async function runTlcAndWait(
  tlaFilePath: string,
  cfgFileName: string,
  tlcOptions: string[],
  javaOpts: string[],
  toolsDir: string,
  javaHome?: string
): Promise<TlcResult> {
  const procInfo = await runTlc(
    tlaFilePath,
    cfgFileName,
    tlcOptions,
    javaOpts,
    toolsDir,
    javaHome
  );

  // Collect output
  const output: string[] = [];
  const rl = createInterface({
    input: procInfo.mergedOutput,
    crlfDelay: Infinity
  });

  for await (const line of rl) {
    const cleanedLine = mapTlcOutputLine(line);
    if (cleanedLine !== undefined) {
      output.push(cleanedLine);
    }
  }

  // Wait for process to complete
  const exitCode = await new Promise<number>((resolve) => {
    procInfo.process.once('close', (code) => {
      resolve(code || 0);
    });
  });

  return {
    exitCode,
    output
  };
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
