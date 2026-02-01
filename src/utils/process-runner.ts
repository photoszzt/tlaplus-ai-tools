import { spawn, execSync, ChildProcess, SpawnOptions } from 'child_process';
import type { Readable } from 'stream';

export interface RunProcessOptions {
  command: string;
  args: string[];
  cwd?: string;
  env?: Record<string, string>;
  timeoutMs?: number;
  killGraceMs?: number;
  signal?: AbortSignal;
  maxOutputBytes?: number;
}

export interface RunProcessResult {
  exitCode: number | null;
  timedOut: boolean;
  aborted: boolean;
  killed: boolean;
  stdout: string;
  stderr: string;
  combined: string;
}

const DEFAULT_KILL_GRACE_MS = 5000;
const DEFAULT_MAX_OUTPUT_BYTES = 1024 * 1024;

type OutputBuffers = {
  stdout: Buffer;
  stderr: Buffer;
  combined: Buffer;
};

function normalizeMaxBytes(maxBytes?: number): number {
  if (maxBytes === undefined || Number.isNaN(maxBytes)) {
    return DEFAULT_MAX_OUTPUT_BYTES;
  }
  if (maxBytes <= 0) {
    return 0;
  }
  return Math.floor(maxBytes);
}

function appendTail(existing: Buffer, chunk: Buffer, maxBytes: number): Buffer {
  if (maxBytes <= 0) {
    return Buffer.alloc(0);
  }
  if (chunk.length >= maxBytes) {
    return chunk.subarray(chunk.length - maxBytes);
  }
  const total = existing.length + chunk.length;
  if (total <= maxBytes) {
    return Buffer.concat([existing, chunk]);
  }
  const keep = maxBytes - chunk.length;
  const sliced = existing.subarray(existing.length - keep);
  return Buffer.concat([sliced, chunk]);
}

function appendOutput(buffers: OutputBuffers, target: keyof OutputBuffers, chunk: Buffer, maxBytes: number): void {
  buffers[target] = appendTail(buffers[target], chunk, maxBytes);
}

function toBuffer(chunk: Buffer | string): Buffer {
  return Buffer.isBuffer(chunk) ? chunk : Buffer.from(chunk);
}

function safeResume(stream?: Readable | null): void {
  if (!stream) {
    return;
  }
  stream.resume();
}

function killProcessTree(proc: ChildProcess, signal: NodeJS.Signals): void {
  if (!proc.pid) {
    return;
  }

  if (process.platform === 'win32') {
    if (signal === 'SIGKILL') {
      try {
        execSync(`taskkill /pid ${proc.pid} /T /F`, { stdio: 'ignore' });
        return;
      } catch {
        // Fall back to regular kill below.
      }
    }
    try {
      proc.kill(signal);
    } catch {
      // Ignore kill errors.
    }
    return;
  }

  if (process.platform === 'linux') {
    try {
      process.kill(-proc.pid, signal);
      return;
    } catch {
      // Fall back to direct kill.
    }
  }

  try {
    proc.kill(signal);
  } catch {
    // Ignore kill errors.
  }
}

export async function runProcess(options: RunProcessOptions): Promise<RunProcessResult> {
  const maxOutputBytes = normalizeMaxBytes(options.maxOutputBytes);
  const killGraceMs = options.killGraceMs ?? DEFAULT_KILL_GRACE_MS;
  const buffers: OutputBuffers = {
    stdout: Buffer.alloc(0),
    stderr: Buffer.alloc(0),
    combined: Buffer.alloc(0)
  };

  let timedOut = false;
  let aborted = false;
  let killed = false;
  let resolved = false;
  let exitCode: number | null = null;

  let timeoutId: NodeJS.Timeout | undefined;
  let graceId: NodeJS.Timeout | undefined;
  let forceResolveId: NodeJS.Timeout | undefined;

  let processHandle: ChildProcess | null = null;

  return await new Promise<RunProcessResult>((resolve) => {
    const finalize = (code: number | null) => {
      if (resolved) {
        return;
      }
      resolved = true;

      if (timeoutId) {
        clearTimeout(timeoutId);
      }
      if (graceId) {
        clearTimeout(graceId);
      }
      if (forceResolveId) {
        clearTimeout(forceResolveId);
      }

      if (options.signal) {
        options.signal.removeEventListener('abort', onAbort);
      }

      if (processHandle) {
        processHandle.removeListener('error', onError);
        processHandle.removeListener('close', onClose);
        processHandle.removeListener('exit', onExit);

        cleanupStream(processHandle.stdout, onStdoutData, onStreamError);
        cleanupStream(processHandle.stderr, onStderrData, onStreamError);
      }

      resolve({
        exitCode: code,
        timedOut,
        aborted,
        killed,
        stdout: buffers.stdout.toString(),
        stderr: buffers.stderr.toString(),
        combined: buffers.combined.toString()
      });
    };

    const terminate = (reason: 'timeout' | 'abort') => {
      if (reason === 'timeout') {
        timedOut = true;
      } else {
        aborted = true;
      }

      if (!processHandle?.pid) {
        finalize(exitCode);
        return;
      }

      const grace = reason === 'abort' ? 0 : killGraceMs;
      killed = true;
      killProcessTree(processHandle, 'SIGTERM');

      graceId = setTimeout(() => {
        killProcessTree(processHandle!, 'SIGKILL');
      }, Math.max(0, grace));

      forceResolveId = setTimeout(() => {
        finalize(exitCode);
      }, Math.max(0, grace) + 1000);
    };

    const onExit = (code: number | null) => {
      exitCode = code;
    };

    const onClose = (code: number | null) => {
      exitCode = code;
      finalize(exitCode);
    };

    const onError = (err: Error) => {
      const message = `Process error: ${err.message}\n`;
      const buf = Buffer.from(message);
      appendOutput(buffers, 'stderr', buf, maxOutputBytes);
      appendOutput(buffers, 'combined', buf, maxOutputBytes);
      finalize(exitCode);
    };

    const onStreamError = (err: Error) => {
      const message = `Stream error: ${err.message}\n`;
      const buf = Buffer.from(message);
      appendOutput(buffers, 'stderr', buf, maxOutputBytes);
      appendOutput(buffers, 'combined', buf, maxOutputBytes);
    };

    const onStdoutData = (chunk: Buffer | string) => {
      const buf = toBuffer(chunk);
      appendOutput(buffers, 'stdout', buf, maxOutputBytes);
      appendOutput(buffers, 'combined', buf, maxOutputBytes);
    };

    const onStderrData = (chunk: Buffer | string) => {
      const buf = toBuffer(chunk);
      appendOutput(buffers, 'stderr', buf, maxOutputBytes);
      appendOutput(buffers, 'combined', buf, maxOutputBytes);
    };

    const onAbort = () => {
      terminate('abort');
    };

    const spawnOptions: SpawnOptions = {
      cwd: options.cwd ?? process.cwd(),
      env: options.env ? { ...process.env, ...options.env } : process.env,
      detached: process.platform !== 'win32',
      windowsHide: process.platform === 'win32',
      stdio: ['ignore', 'pipe', 'pipe']
    };

    processHandle = spawn(options.command, options.args, spawnOptions);
    const child = processHandle;
    if (!child) {
      finalize(exitCode);
      return;
    }

    child.once('error', onError);
    child.once('close', onClose);
    child.once('exit', onExit);

    if (child.stdout) {
      child.stdout.on('data', onStdoutData);
      child.stdout.on('error', onStreamError);
      safeResume(child.stdout);
    }

    if (child.stderr) {
      child.stderr.on('data', onStderrData);
      child.stderr.on('error', onStreamError);
      safeResume(child.stderr);
    }

    if (options.timeoutMs && options.timeoutMs > 0) {
      timeoutId = setTimeout(() => {
        terminate('timeout');
      }, options.timeoutMs);
    }

    if (options.signal) {
      if (options.signal.aborted) {
        onAbort();
      } else {
        options.signal.addEventListener('abort', onAbort);
      }
    }
  });
}

function cleanupStream(
  stream: Readable | null | undefined,
  onData: (chunk: Buffer | string) => void,
  onError: (err: Error) => void
): void {
  if (!stream) {
    return;
  }
  stream.removeListener('data', onData);
  stream.removeListener('error', onError);
  stream.removeAllListeners('end');
  stream.removeAllListeners('close');
  stream.removeAllListeners('readable');
  stream.destroy();
}
