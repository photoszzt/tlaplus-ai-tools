import * as path from 'path';
import { ProcessInfo, runJavaCommand } from './java';
import { getClassPath, getModuleSearchPaths } from './tla-tools';
import { createInterface } from 'readline';

const SANY_MAIN_CLASS = 'tla2sany.SANY';

/**
 * Result of parsing a TLA+ file with SANY
 */
export interface SanyParseResult {
  success: boolean;
  errors: SanyError[];
  warnings: SanyWarning[];
}

/**
 * An error found by SANY
 */
export interface SanyError {
  file: string;
  line: number;
  column: number;
  message: string;
}

/**
 * A warning from SANY
 */
export interface SanyWarning {
  file: string;
  line: number;
  column: number;
  message: string;
}

/**
 * Run SANY parser on a TLA+ file
 *
 * @param tlaFilePath Path to the TLA+ file to parse
 * @param toolsDir Path to tools directory containing tla2tools.jar
 * @param javaHome Optional JAVA_HOME path
 * @returns ProcessInfo with the spawned process
 */
export async function runSanyParse(
  tlaFilePath: string,
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

  const javaOpts = libPaths ? [`-DTLA-Library=${libPaths}`] : [];

  // SANY expects the filename as an argument
  const args = [path.basename(tlaFilePath)];

  return await runJavaCommand(
    classPath,
    SANY_MAIN_CLASS,
    args,
    javaOpts,
    javaHome,
    path.dirname(tlaFilePath)
  );
}

/**
 * Parse SANY output and extract errors and warnings
 *
 * @param procInfo Process info from runSanyParse
 * @returns Parsed result with errors and warnings
 */
export async function parseSanyOutput(procInfo: ProcessInfo): Promise<SanyParseResult> {
  const errors: SanyError[] = [];
  const warnings: SanyWarning[] = [];

  let currentFile: string | undefined;
  let inErrorBlock = false;
  let inWarningBlock = false;
  let currentMessage = '';
  let currentRange: { line: number; column: number } | undefined;

  const rl = createInterface({
    input: procInfo.mergedOutput,
    crlfDelay: Infinity
  });

  for await (const line of rl) {
    // Track current file being parsed
    if (line.startsWith('Parsing file ')) {
      // Normalize to forward slashes internally
      const rawPath = line.substring(13).trim();
      currentFile = rawPath.replace(/\\/g, '/');
      continue;
    }

    // Track semantic processing module
    if (line.startsWith('Semantic processing of module ')) {
      // This tells us which module is being processed
      continue;
    }

    // Detect error blocks
    if (line.startsWith('*** Errors:')) {
      inErrorBlock = true;
      inWarningBlock = false;
      currentMessage = '';
      currentRange = undefined;
      continue;
    }

    // Detect parse error blocks
    if (line.startsWith('***Parse Error***') || line.startsWith('Fatal errors while parsing TLA+ spec')) {
      inErrorBlock = true;
      inWarningBlock = false;
      currentMessage = line.trim();
      currentRange = undefined;
      continue;
    }

    // Detect warning blocks
    if (line.startsWith('*** Warnings:')) {
      inWarningBlock = true;
      inErrorBlock = false;
      currentMessage = '';
      currentRange = undefined;
      continue;
    }

    // Detect abort messages
    if (line.startsWith('*** Abort messages:')) {
      inErrorBlock = true;
      inWarningBlock = false;
      currentMessage = '';
      currentRange = undefined;
      continue;
    }

    // Skip stack traces
    if (line.startsWith('Residual stack trace follows:')) {
      inErrorBlock = false;
      inWarningBlock = false;
      continue;
    }

    // Parse lexical errors (in main output)
    const lexicalMatch = /^\s*Lexical error at line (\d+), column (\d+)\.\s*(.*)$/.exec(line);
    if (lexicalMatch && currentFile) {
      errors.push({
        file: currentFile,
        line: parseInt(lexicalMatch[1]),
        column: parseInt(lexicalMatch[2]),
        message: lexicalMatch[3]
      });
      continue;
    }

    // Parse error/warning ranges
    if (inErrorBlock || inWarningBlock) {
      // Try to parse range: "line 1, col 2 to line 3, col 4 of module ModName"
      const rangeMatch = /^\s*line (\d+), col (\d+) to line \d+, col \d+ of module \w+\s*$/.exec(line);
      if (rangeMatch) {
        currentRange = {
          line: parseInt(rangeMatch[1]),
          column: parseInt(rangeMatch[2])
        };
        continue;
      }

      // Try to parse parse error range: "at line 1, col 2 ..."
      const parseErrorMatch = /\bat line (\d+), col(?:umn)? (\d+)\s+.*$/.exec(line);
      if (parseErrorMatch) {
        currentRange = {
          line: parseInt(parseErrorMatch[1]),
          column: parseInt(parseErrorMatch[2])
        };
        // Continue to also capture the message
      }

      // Accumulate message text
      if (line.trim() && !line.startsWith('***')) {
        if (currentMessage) {
          currentMessage += '\n' + line.trim();
        } else {
          currentMessage = line.trim();
        }
      }

      // If we have a complete message with range, add it
      if (currentMessage && currentRange && currentFile) {
        const item = {
          file: currentFile,
          line: currentRange.line,
          column: currentRange.column,
          message: currentMessage
        };

        if (inWarningBlock) {
          warnings.push(item);
        } else {
          errors.push(item);
        }

        currentMessage = '';
        currentRange = undefined;
      }
    }

    // Success indicator
    if (line === 'SANY finished.') {
      // If we have pending error message without range, add it
      if (currentMessage && currentFile) {
        const item = {
          file: currentFile,
          line: 1,
          column: 1,
          message: currentMessage
        };

        if (inWarningBlock) {
          warnings.push(item);
        } else if (inErrorBlock) {
          errors.push(item);
        }
      }
      break;
    }
  }

  // Wait for process to complete (if not already completed)
  if (procInfo.process.exitCode === null) {
    await new Promise<void>((resolve) => {
      procInfo.process.once('close', () => resolve());
    });
  }

  // Denormalize back to platform-specific paths in results
  return {
    success: errors.length === 0,
    errors: errors.map(e => ({
      ...e,
      file: process.platform === 'win32'
        ? e.file.replace(/\//g, '\\')
        : e.file
    })),
    warnings: warnings.map(w => ({
      ...w,
      file: process.platform === 'win32'
        ? w.file.replace(/\//g, '\\')
        : w.file
    }))
  };
}
