import { spawn, ChildProcess, execSync } from 'child_process';
import * as fs from 'fs';
import * as path from 'path';
import { PassThrough } from 'stream';
import { JavaOptions } from '../types';
import { withRetry, ErrorCode, classifyError, enhanceError } from './errors';

function getJavaCommand(): string {
  return 'java' + (process.platform === 'win32' ? '.exe' : '');
}
const DEFAULT_GC_OPTION = '-XX:+UseParallelGC';

/**
 * Information about a spawned Java process
 */
export interface ProcessInfo {
  process: ChildProcess;
  stdout: NodeJS.ReadableStream | null;
  stderr: NodeJS.ReadableStream | null;
  mergedOutput: PassThrough;
  kill?: () => void;
}

/**
 * Find the Java executable on the system
 *
 * @param javaHome Optional JAVA_HOME path
 * @returns Path to java executable
 * @throws Error if Java not found
 */
export function findJavaExecutable(javaHome?: string): string {
  const javaCmd = getJavaCommand();
  // If javaHome is provided, use it
  if (javaHome) {
    const javaExec = buildJavaPathFromHome(javaHome);
    if (!javaExec) {
      throw new Error(
        `Java executable not found in "${javaHome}".\n\n` +
        `Please ensure Java is installed in this directory, or use --java-home to specify a different location.`
      );
    }
    return javaExec;
  }

  // Try environment variables (JAVA_HOME, etc.)
  const envHomes = collectJavaHomesFromEnv();
  for (const envHome of envHomes) {
    const javaExec = buildJavaPathFromHome(envHome);
    if (javaExec) {
      return javaExec;
    }
  }

  // Fall back to 'java' command in PATH
  return javaCmd;
}

/**
 * Run a Java command with the TLA+ tools
 *
 * @param jarPath Path to the jar file (classpath)
 * @param mainClass Main class to execute
 * @param args Arguments to pass to the main class
 * @param javaOpts Java options (e.g., -Xmx, -D properties)
 * @param javaHome Optional JAVA_HOME path
 * @param workingDir Optional working directory for the process
 * @param timeoutMs Optional timeout in milliseconds
 * @returns ProcessInfo with the spawned process and output streams
 */
export async function runJavaCommand(
  jarPath: string,
  mainClass: string,
  args: string[],
  javaOpts: string[] = [],
  javaHome?: string,
  workingDir?: string,
  timeoutMs?: number
): Promise<ProcessInfo> {
  const javaPath = findJavaExecutable(javaHome);

  // Build Java options with classpath and GC options
  const opts = buildJavaOptions(javaOpts, jarPath);

  // Build complete command: java [opts] [mainClass] [args]
  const fullArgs = opts.concat([mainClass]).concat(args);

  // Wrap spawn in retry logic for transient failures
  return await withRetry(
    async () => new Promise<ProcessInfo>((resolve, reject) => {
    const spawnOptions: any = { cwd: workingDir || process.cwd() };

    // Enable proper termination on Windows
    if (process.platform === 'win32') {
      spawnOptions.shell = true;
      spawnOptions.windowsHide = true;
    }

    const proc = spawn(javaPath, fullArgs, spawnOptions);

    // Cross-platform kill helper
    const killProcess = () => {
      if (process.platform === 'win32') {
        try {
          execSync(`taskkill /pid ${proc.pid} /T /F`, { stdio: 'ignore' });
        } catch {
          proc.kill('SIGKILL');
        }
      } else {
        proc.kill('SIGTERM');
      }
    };

    // Set up timeout if specified
    let timeoutId: NodeJS.Timeout | undefined;
    if (timeoutMs && timeoutMs > 0) {
      timeoutId = setTimeout(() => {
        killProcess();
        reject(new Error(`Process timed out after ${timeoutMs}ms`));
      }, timeoutMs);
    }

    // Create merged output stream (stdout + stderr)
    const mergedOutput = new PassThrough();

    if (proc.stdout) {
      proc.stdout.pipe(mergedOutput, { end: false });
    }
    if (proc.stderr) {
      proc.stderr.pipe(mergedOutput, { end: false });
    }

    // Close merged stream when process ends
    const endMerged = () => {
      if (timeoutId) {
        clearTimeout(timeoutId);
      }
      mergedOutput.end();
    };
    proc.once('exit', endMerged);
    proc.once('close', endMerged);

    // If the process already exited, defer end() to next event loop
    if (proc.exitCode !== null) {
      setImmediate(endMerged);
    }

    const cleanup = () => {
      proc.removeListener('error', onError);
      proc.removeListener('spawn', onSpawn);
    };

    const onError = (err: Error) => {
      cleanup();
      reject(enhanceError(
        new Error(`Failed to launch Java process using "${javaPath}": ${err.message}`),
        {
          context: {
            javaPath,
            mainClass,
            args: args.slice(0, 3) // Truncate to avoid huge logs
          }
        }
      ));
    };

    const onSpawn = () => {
      cleanup();
      resolve({
        process: proc,
        stdout: proc.stdout,
        stderr: proc.stderr,
        mergedOutput,
        kill: killProcess
      });
    };

    proc.once('error', onError);
    proc.once('spawn', onSpawn);
  }),
    {
      maxAttempts: 3,
      initialDelayMs: 100,
      maxDelayMs: 10000,
      backoffMultiplier: 10,
      shouldRetry: (error) => {
        const code = classifyError(error);
        return code === ErrorCode.JAVA_SPAWN_FAILED;
      }
    }
  );
}

/**
 * Build Java options array with classpath and GC settings
 *
 * @param customOptions Custom Java options provided by user
 * @param defaultClassPath Default classpath (tla2tools.jar)
 * @returns Array of Java options
 */
export function buildJavaOptions(customOptions: string[], defaultClassPath: string): string[] {
  const opts = customOptions.slice(0);
  mergeClassPathOption(opts, defaultClassPath);
  mergeGCOption(opts, DEFAULT_GC_OPTION);
  return opts;
}

/**
 * Build full path to Java executable from JAVA_HOME
 *
 * @param javaHome JAVA_HOME path
 * @returns Full path to java executable, or undefined if not found
 */
function buildJavaPathFromHome(javaHome: string): string | undefined {
  const javaCmd = getJavaCommand();
  const candidate = path.join(javaHome, 'bin', javaCmd);
  return fs.existsSync(candidate) ? candidate : undefined;
}

/**
 * Collect Java home locations from environment variables
 *
 * @returns Array of potential JAVA_HOME paths
 */
function collectJavaHomesFromEnv(): string[] {
  let envVars = [
    'JAVA_HOME',
    'JDK_HOME',
    // ARM64 variants
    'JAVA_HOME_21_ARM64',
    'JAVA_HOME_17_ARM64',
    'JAVA_HOME_11_ARM64',
    // X64 variants
    'JAVA_HOME_21_X64',
    'JAVA_HOME_17_X64',
    'JAVA_HOME_11_X64',
    'JAVA_HOME_8_X64'
  ];

  // Prioritize ARM64 on Apple Silicon
  if (process.platform === 'darwin' && process.arch === 'arm64') {
    const armVars = envVars.filter(v => v.includes('ARM64'));
    const otherVars = envVars.filter(v => !v.includes('ARM64'));
    envVars = [...armVars, ...otherVars];
  }

  const seen = new Set<string>();
  const homes: string[] = [];

  for (const name of envVars) {
    const val = process.env[name];
    if (val && !seen.has(val)) {
      homes.push(val);
      seen.add(val);
    }
  }

  return homes;
}

/**
 * Add default GC option if no custom one is provided
 *
 * @param options Options array to modify
 * @param defaultGC Default GC option
 */
function mergeGCOption(options: string[], defaultGC: string): void {
  const gcOption = options.find(opt => opt.startsWith('-XX:+Use') && opt.endsWith('GC'));
  if (!gcOption) {
    options.push(defaultGC);
  }
}

/**
 * Merge custom classpath with default classpath
 * Custom libraries are given precedence over default ones
 *
 * @param options Options array to modify
 * @param defaultClassPath Default classpath
 */
function mergeClassPathOption(options: string[], defaultClassPath: string): void {
  let cpIdx = -1;
  for (let i = 0; i < options.length; i++) {
    const option = options[i];
    if (option === '-cp' || option === '-classpath') {
      cpIdx = i + 1;
      break;
    }
  }

  if (cpIdx < 0 || cpIdx >= options.length) {
    // No custom classpath provided, use the default one
    options.push('-cp', defaultClassPath);
    return;
  }

  let classPath = options[cpIdx];
  if (containsTlaToolsLib(classPath)) {
    return;
  }

  if (classPath.length > 0) {
    classPath += path.delimiter;
  }
  classPath += defaultClassPath;
  options[cpIdx] = classPath;
}

/**
 * Check if classpath already contains tla2tools.jar
 *
 * @param classPath Classpath string
 * @returns True if tla2tools.jar is in the classpath
 */
function containsTlaToolsLib(classPath: string): boolean {
  const TLA_TOOLS_LIB_NAME = 'tla2tools.jar';
  const TLA_TOOLS_LIB_NAME_END_UNIX = '/' + TLA_TOOLS_LIB_NAME;
  const TLA_TOOLS_LIB_NAME_END_WIN = '\\' + TLA_TOOLS_LIB_NAME;

  const paths = classPath.split(path.delimiter);
  for (const p of paths) {
    if (p === TLA_TOOLS_LIB_NAME ||
        p.endsWith(TLA_TOOLS_LIB_NAME_END_UNIX) ||
        p.endsWith(TLA_TOOLS_LIB_NAME_END_WIN)) {
      return true;
    }
  }
  return false;
}
