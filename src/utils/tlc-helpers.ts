import * as fs from "fs";
import * as path from "path";
import { buildJavaOptions, findJavaExecutable } from "./java";
import { withRetry } from "./errors";
import { runProcess } from "./process-runner";
import { getClassPath, getModuleSearchPaths } from "./tla-tools";
import { mapTlcOutputLine } from "./tlc";
import { StringDecoder } from "string_decoder";

const TLC_MAIN_CLASS = "tlc2.TLC";

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
export type TlcProgressCallback = (
  progress: {
    progress: number;
    total?: number;
    message?: string;
    level?: "info" | "error";
  },
  notificationSignal: AbortSignal,
) => void | Promise<void>;

/**
 * Specification files (TLA and CFG)
 */
export interface SpecFiles {
  tlaFilePath: string;
  cfgFilePath: string;
}

/**
 * Run TLC model checker and wait for completion.
 *
 * @param tlaFilePath - Path to the TLA+ spec file
 * @param cfgFileName - Path to the config file (absolute paths preserve external configs)
 * @param tlcOptions - TLC command-line options
 * @param javaOpts - Java command-line options
 * @param toolsDir - Path to tools directory
 * @param javaHome - Optional Java home path
 * @param timeoutMs - Optional timeout in milliseconds
 * @param signal - Optional abort signal
 * @param onProgress - Live TLC lifecycle/statistics messages. Progress counts
 *   updates, not percent complete; the state-space total is unknown.
 */
// @implements QG-REVIEW-006
export async function runTlcAndWait(
  tlaFilePath: string,
  cfgFileName: string,
  tlcOptions: string[],
  javaOpts: string[],
  toolsDir: string,
  javaHome?: string,
  timeoutMs?: number,
  signal?: AbortSignal,
  onProgress?: TlcProgressCallback,
): Promise<TlcResult> {
  const classPath = getClassPath(toolsDir);
  const moduleSearchPaths = getModuleSearchPaths(toolsDir);

  const libPaths = moduleSearchPaths.filter((p) => !p.startsWith("jarfile:")).join(path.delimiter);

  const javaOptions = javaOpts.slice();
  if (onProgress && !javaOptions.some((opt) => opt.startsWith("-Dtlc2.TLC.progressInterval="))) {
    javaOptions.push("-Dtlc2.TLC.progressInterval=5");
  }
  if (libPaths) {
    javaOptions.push(`-DTLA-Library=${libPaths}`);
  }

  const tlaFileName = path.basename(tlaFilePath);
  const args = [tlaFileName, "-tool", "-modelcheck"];
  if (cfgFileName) {
    args.push("-config", cfgFileName);
  }
  args.push(...tlcOptions);

  const javaPath = findJavaExecutable(javaHome);
  const fullArgs = buildJavaOptions(javaOptions, classPath).concat([TLC_MAIN_CLASS]).concat(args);

  let progress = 0;
  let notifications = Promise.resolve();
  const events: Parameters<TlcProgressCallback>[0][] = [];
  let sending = false;
  const notificationController = new AbortController();
  const cancelNotifications = () => notificationController.abort();
  signal?.addEventListener("abort", cancelNotifications, { once: true });
  if (signal?.aborted) cancelNotifications();
  const deliver = async (event: Parameters<TlcProgressCallback>[0]) => {
    if (notificationController.signal.aborted) return;
    let timer: ReturnType<typeof setTimeout> | undefined;
    let interrupted: () => void = () => {};
    const cancelled = new Promise<void>((resolve) => {
      interrupted = resolve;
      notificationController.signal.addEventListener("abort", interrupted, { once: true });
      timer = setTimeout(cancelNotifications, 1000);
    });
    try {
      await Promise.race([
        Promise.resolve().then(() => onProgress?.(event, notificationController.signal)),
        cancelled,
      ]);
    } catch {
      /* Notifications are best effort. */
    } finally {
      clearTimeout(timer);
      notificationController.signal.removeEventListener("abort", interrupted);
    }
  };
  const finishNotifications = async () => {
    await notifications;
    cancelNotifications();
    signal?.removeEventListener("abort", cancelNotifications);
  };
  const emit = (message: string, level: "info" | "error" = "info") => {
    if (!onProgress || notificationController.signal.aborted) return;
    const event = { progress: progress++, message, level };
    if (events.length === 32) events[31] = event;
    else events.push(event);
    if (sending) return;
    sending = true;
    notifications = (async () => {
      let current;
      while ((current = events.shift())) {
        await deliver(current);
      }
      sending = false;
    })();
  };
  // Codes from upstream tlc2.output.EC; -tool wraps native messages with these IDs.
  const phases = new Map([
    [2185, "TLC execution started"],
    [2186, "TLC execution finished"],
    [2192, "TLC checking temporal properties"],
    [2267, "TLC temporal checking finished"],
    [2195, "TLC checkpoint started"],
    [2196, "TLC checkpoint finished"],
  ]);
  const statisticsCodes = new Set([2200, 2206, 2209]);
  const statistics =
    /^Progress\([-\d]+\) at [\d: -]+: [-\d,]+ states generated(?: \([-\d,]+ s\/min\))?, [-\d,]+ distinct states found(?: \([-\d,]+ ds\/min\))?, [-\d,]+ states left on queue\.$/;
  const lastUpdate = new Map<number, number>();
  const deferredStatistics = new Map<number, string>();
  const streams = {
    stdout: { decoder: new StringDecoder("utf8"), pending: "", code: 0 },
    stderr: { decoder: new StringDecoder("utf8"), pending: "", code: 0 },
  };
  const consume = (stream: "stdout" | "stderr", text: string) => {
    const state = streams[stream];
    const lines = (state.pending + text).split(/\r?\n/);
    state.pending = (lines.pop() ?? "").slice(-65536);
    for (const line of lines) {
      const start = /^@!@!@STARTMSG (\d+):\d+ @!@!@$/.exec(line);
      if (start) {
        state.code = Number(start[1]);
        const phase = phases.get(state.code);
        if (phase && performance.now() - (lastUpdate.get(state.code) ?? -Infinity) >= 1000) {
          lastUpdate.set(state.code, performance.now());
          emit(phase);
        }
      } else if (line.startsWith("@!@!@ENDMSG")) {
        state.code = 0;
      } else if (statisticsCodes.has(state.code) && statistics.test(line)) {
        if (performance.now() - (lastUpdate.get(state.code) ?? -Infinity) >= 1000) {
          lastUpdate.set(state.code, performance.now());
          deferredStatistics.delete(state.code);
          emit(line);
        } else deferredStatistics.set(state.code, line);
      }
    }
  };
  emit("Starting TLC");

  const result = await withRetry(async () => {
    const attemptResult = await runProcess({
      command: javaPath,
      args: fullArgs,
      cwd: path.dirname(tlaFilePath),
      timeoutMs,
      signal,
      onOutput: (chunk, stream) => consume(stream, streams[stream].decoder.write(chunk)),
    });

    if (!attemptResult.timedOut && !attemptResult.aborted && attemptResult.exitCode === null) {
      const errorDetails = attemptResult.stderr || attemptResult.combined || "Unknown error.";
      throw new Error(`Failed to launch Java process using "${javaPath}": ${errorDetails}`);
    }

    return attemptResult;
  }).catch(async (error) => {
    emit("TLC could not be started", "error");
    await finishNotifications();
    throw error;
  });

  for (const stream of ["stdout", "stderr"] as const) {
    consume(stream, streams[stream].decoder.end() + "\n");
  }
  for (const message of deferredStatistics.values()) emit(message);

  const output: string[] = [];
  if (result.combined.length > 0) {
    const lines = result.combined.split(/\r?\n/);
    for (let i = 0; i < lines.length; i++) {
      const line = lines[i];
      const cleanedLine = mapTlcOutputLine(line);
      if (cleanedLine !== undefined) {
        output.push(cleanedLine);
      }
    }
  }

  if (result.timedOut) {
    output.push(`TLC process timed out after ${timeoutMs ?? 0}ms.`);
  }
  if (result.aborted) {
    output.push("TLC process was aborted.");
  }

  const exitCode = result.timedOut ? 124 : result.aborted ? 130 : (result.exitCode ?? 0);
  emit(
    result.timedOut
      ? "TLC timed out"
      : result.aborted
        ? "TLC cancelled"
        : `TLC finished with exit code ${exitCode}`,
    exitCode === 0 ? "info" : "error",
  );
  await finishNotifications();

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
  const baseName = path.basename(tlaFilePath, ".tla");

  // First, try the simple case: MySpec.tla -> MySpec.cfg
  const simpleCfg = path.join(dir, `${baseName}.cfg`);
  if (fs.existsSync(simpleCfg)) {
    return {
      tlaFilePath,
      cfgFilePath: simpleCfg,
    };
  }

  // Second, try the MC prefix pattern: MySpec.tla -> MCMySpec.tla + MCMySpec.cfg
  const mcBaseName = `MC${baseName}`;
  const mcTlaPath = path.join(dir, `${mcBaseName}.tla`);
  const mcCfgPath = path.join(dir, `${mcBaseName}.cfg`);

  if (fs.existsSync(mcTlaPath) && fs.existsSync(mcCfgPath)) {
    return {
      tlaFilePath: mcTlaPath,
      cfgFilePath: mcCfgPath,
    };
  }

  // No config file found
  return null;
}
