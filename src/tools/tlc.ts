import { z } from 'zod';
import * as fs from 'fs';
import * as path from 'path';
import { ServerConfig } from '../types';
import { resolveAndValidatePath } from '../utils/paths';
import { getSpecFiles, runTlcAndWait } from '../utils/tlc-helpers';
import { EnhancedError, enhanceError, ErrorCode } from '../utils/errors';

/**
 * Format an error response with error code and suggested actions
 */
function formatErrorResponse(error: Error): string {
  const enhanced = error instanceof EnhancedError ? error : enhanceError(error);

  const parts = [
    `Error [${enhanced.code}]: ${error.message}`,
    '',
    'Suggested Actions:',
    ...getSuggestedActions(enhanced.code)
  ];

  if (enhanced.metadata.retriesExhausted) {
    parts.push('', `Failed after ${enhanced.metadata.retryAttempt} retry attempts.`);
  }

  if (process.env.VERBOSE || process.env.DEBUG) {
    parts.push('', 'Stack Trace:', enhanced.metadata.stack || 'N/A');
  }

  return parts.join('\n');
}

const DEFAULT_SMOKE_TIMEOUT_MS = 120000;
const DEFAULT_EXPLORE_TIMEOUT_MS = 600000;
const DEFAULT_TRACE_TIMEOUT_MS = 600000;

type ToolContext = {
  signal?: AbortSignal;
  request?: { signal?: AbortSignal };
  _meta?: {
    progressToken?: string | number;
    [key: string]: unknown;
  };
  sendNotification?: (notification: any) => Promise<void>;
};

function getAbortSignal(context?: ToolContext): AbortSignal | undefined {
  return context?.signal ?? context?.request?.signal;
}

function getProgressToken(context?: ToolContext): string | number | undefined {
  return context?._meta?.progressToken;
}

async function sendProgress(
  context: ToolContext | undefined,
  progress: number,
  total?: number,
  message?: string
): Promise<void> {
  const progressToken = getProgressToken(context);
  if (!progressToken || !context?.sendNotification) {
    return;
  }

  await context.sendNotification({
    method: 'notifications/progress',
    params: {
      progressToken,
      progress,
      total,
      message
    }
  });
}

function parseTimeoutMs(value: unknown): number | undefined {
  if (typeof value === 'number' && Number.isFinite(value) && value > 0) {
    return Math.floor(value);
  }
  if (typeof value === 'string' && value.trim() !== '') {
    const parsed = Number(value);
    if (Number.isFinite(parsed) && parsed > 0) {
      return Math.floor(parsed);
    }
  }
  return undefined;
}

function extractFingerprintFromTrace(traceFilePath: string): number | undefined {
  const fileName = path.basename(traceFilePath);
  const match = /_F(\d+)_/.exec(fileName);
  if (match && match[1]) {
    return Number.parseInt(match[1], 10);
  }
  return undefined;
}

function resolveTimeoutMs(value: unknown, envKey: string, fallback: number): number {
  const direct = parseTimeoutMs(value);
  if (direct !== undefined) {
    return direct;
  }
  const envValue = parseTimeoutMs(process.env[envKey]);
  return envValue ?? fallback;
}

/**
 * Get suggested actions based on error code
 */
function getSuggestedActions(code: ErrorCode): string[] {
  const suggestions: Partial<Record<ErrorCode, string[]>> = {
    [ErrorCode.JAVA_NOT_FOUND]: [
      '- Install Java 17 or later',
      '- Set JAVA_HOME environment variable',
      '- Use --java-home to specify Java location'
    ],
    [ErrorCode.CONFIG_TOOLS_NOT_FOUND]: [
      '- Use --tools-dir to specify TLA+ tools location',
      '- Ensure tla2tools.jar exists in tools directory'
    ],
    [ErrorCode.FILE_NOT_FOUND]: [
      '- Verify the file path is correct',
      '- Check file permissions'
    ],
    [ErrorCode.JAR_LOCKED]: [
      '- Close other programs using the JAR file',
      '- Check for antivirus software locking files'
    ],
    [ErrorCode.JAR_ENTRY_NOT_FOUND]: [
      '- Verify the jarfile URI is correct',
      '- Check that the JAR file contains the expected module'
    ],
    [ErrorCode.JAR_EXTRACTION_FAILED]: [
      '- Check available disk space',
      '- Verify write permissions to temp directory'
    ]
  };

  return suggestions[code] || ['- Check error message for details'];
}

/**
 * Register all TLC tools with the MCP server
 * - check: Exhaustive model checking
 * - smoke: Quick smoke test (random simulation)
 * - explore: Generate and print behavior traces
 * - trace: Load and replay TLC trace files
 */
export async function registerTlcTools(
  server: any,
  config: ServerConfig
): Promise<void> {
  // Tool 1: Model check
  server.tool(
    'tlaplus_mcp_tlc_check',
    'Perform an exhaustive model check of the TLA+ module provided as an input file using TLC. Model checking is a formal verification method that systematically explores all reachable states of a system to verify its correctness. This includes checking both safety and liveness properties, and identifying any counterexamples that violate the specified properties. Please note that TLC requires the fully qualified file path to the TLA+ module. Be aware that, due to the potential for state-space explosion, exhaustive model checking may be computationally intensive and time-consuming. In some cases, it may be infeasible to check very large models exhaustively. For guidance on TLC configuration files, see the tlc-config-files.md knowledgebase article.',
    {
      fileName: z.string(),
      cfgFile: z.string().optional(),
      extraOpts: z.array(z.string()).optional(),
      extraJavaOpts: z.array(z.string()).optional()
    },
    async ({ fileName, cfgFile, extraOpts, extraJavaOpts }: {
      fileName: string;
      cfgFile?: string;
      extraOpts?: string[];
      extraJavaOpts?: string[];
    }) => {
      try {
        // Resolve and validate file path
        const absolutePath = resolveAndValidatePath(fileName, config.workingDir);

        // Check if file exists
        if (!fs.existsSync(absolutePath)) {
          return {
            content: [{
              type: 'text',
              text: `File ${absolutePath} does not exist on disk.`
            }]
          };
        }

        // Ensure tools directory is configured
        if (!config.toolsDir) {
          return {
            content: [{
              type: 'text',
              text: 'TLA+ tools directory not configured. Use --tools-dir to specify the location.'
            }]
          };
        }

        // Find spec files (TLA + CFG)
        const specFiles = await getSpecFiles(absolutePath);
        if (!specFiles) {
          const specName = path.basename(absolutePath, path.extname(absolutePath));
          return {
            content: [{
              type: 'text',
              text: `No ${specName}.cfg or MC${specName}.tla/MC${specName}.cfg files found for ${absolutePath}. ` +
                `Please create an MC${specName}.tla and MC${specName}.cfg file according to the provided TLC guidelines.`
            }]
          };
        }

        // Use provided cfgFile if specified
        // @implements REQ-CODEX-001, SCN-CODEX-001-01, SCN-CODEX-001-02
        let configFilePath = specFiles.cfgFilePath;
        if (cfgFile) {
          const resolvedCfgPath = resolveAndValidatePath(cfgFile, config.workingDir);
          if (!fs.existsSync(resolvedCfgPath)) {
            return {
              content: [{
                type: 'text',
                text: `Config file ${resolvedCfgPath} does not exist on disk.`
              }]
            };
          }
          // @implements REQ-CODEX-002, SCN-CODEX-002-01
          configFilePath = resolvedCfgPath;
        }

        // Build TLC options: -cleanup -modelcheck [extraOpts]
        const tlcOptions = ['-cleanup', '-modelcheck', ...(extraOpts || [])];
        const javaOpts = extraJavaOpts || [];

        // Run TLC and wait for completion
        const result = await runTlcAndWait(
          specFiles.tlaFilePath,
          path.basename(configFilePath),
          tlcOptions,
          javaOpts,
          config.toolsDir,
          config.javaHome || undefined
        );

        return {
          content: [{
            type: 'text',
            text: `Model check completed with exit code ${result.exitCode}.\n\n` +
              `Output:\n${result.output.join('\n')}`
          }]
        };
      } catch (error) {
        return {
          content: [{
            type: 'text',
            text: formatErrorResponse(error as Error)
          }]
        };
      }
    }
  );

  // Tool 2: Smoke test
  server.tool(
    'tlaplus_mcp_tlc_smoke',
    'Smoke test the TLA+ module using TLC with the provided input file. Smoke testing is a lightweight verification technique that runs TLC in simulation mode to randomly explore as many behaviors as possible within a specified time limit. This method does not attempt to exhaustively explore the entire state space. If no counterexample is found, it does not imply that the module is correct—only that no violations were observed within the constraints of the test. If a counterexample is found, it demonstrates that the module violates at least one of its specified properties. Note that any counterexample produced may not be minimal due to the non-exhaustive nature of the search. TLC expects the fully qualified file path to the input module.',
    {
      fileName: z.string(),
      cfgFile: z.string().optional(),
      extraOpts: z.array(z.string()).optional(),
      extraJavaOpts: z.array(z.string()).optional(),
      timeoutMs: z.number().int().positive().optional()
    },
    async ({ fileName, cfgFile, extraOpts, extraJavaOpts, timeoutMs }: {
      fileName: string;
      cfgFile?: string;
      extraOpts?: string[];
      extraJavaOpts?: string[];
      timeoutMs?: number;
    }, context?: ToolContext) => {
      try {
        // Resolve and validate file path
        const absolutePath = resolveAndValidatePath(fileName, config.workingDir);

        // Check if file exists
        if (!fs.existsSync(absolutePath)) {
          return {
            content: [{
              type: 'text',
              text: `File ${absolutePath} does not exist on disk.`
            }]
          };
        }

        // Ensure tools directory is configured
        if (!config.toolsDir) {
          return {
            content: [{
              type: 'text',
              text: 'TLA+ tools directory not configured. Use --tools-dir to specify the location.'
            }]
          };
        }

        // Find spec files (TLA + CFG)
        const specFiles = await getSpecFiles(absolutePath);
        if (!specFiles) {
          const specName = path.basename(absolutePath, path.extname(absolutePath));
          return {
            content: [{
              type: 'text',
              text: `No ${specName}.cfg or MC${specName}.tla/MC${specName}.cfg files found for ${absolutePath}. ` +
                `Please create an MC${specName}.tla and MC${specName}.cfg file according to the provided TLC guidelines.`
            }]
          };
        }

        // Use provided cfgFile if specified
        // @implements REQ-CODEX-001, SCN-CODEX-001-01, SCN-CODEX-001-02
        let configFilePath = specFiles.cfgFilePath;
        if (cfgFile) {
          const resolvedCfgPath = resolveAndValidatePath(cfgFile, config.workingDir);
          if (!fs.existsSync(resolvedCfgPath)) {
            return {
              content: [{
                type: 'text',
                text: `Config file ${resolvedCfgPath} does not exist on disk.`
              }]
            };
          }
          // @implements REQ-CODEX-002, SCN-CODEX-002-01
          configFilePath = resolvedCfgPath;
        }

        // Build TLC options: -cleanup -simulate [extraOpts]
        const tlcOptions = ['-cleanup', '-simulate', ...(extraOpts || [])];
        // Add stopAfter for smoke test (3 seconds)
        const javaOpts = ['-Dtlc2.TLC.stopAfter=3', ...(extraJavaOpts || [])];

        // Run TLC and wait for completion
        const timeoutMsResolved = resolveTimeoutMs(timeoutMs, 'TLC_SMOKE_TIMEOUT_MS', DEFAULT_SMOKE_TIMEOUT_MS);
        const signal = getAbortSignal(context);
        const result = await runTlcAndWait(
          specFiles.tlaFilePath,
          path.basename(configFilePath),
          tlcOptions,
          javaOpts,
          config.toolsDir,
          config.javaHome || undefined,
          timeoutMsResolved,
          signal,
          (progress) => {
            sendProgress(context, progress.progress, progress.total, progress.message).catch(() => {});
          }
        );

        return {
          content: [{
            type: 'text',
            text: `Smoke test completed with exit code ${result.exitCode}.\n\n` +
              `Output:\n${result.output.join('\n')}`
          }]
        };
      } catch (error) {
        return {
          content: [{
            type: 'text',
            text: formatErrorResponse(error as Error)
          }]
        };
      }
    }
  );

  // Tool 3: Explore behaviors
  server.tool(
    'tlaplus_mcp_tlc_explore',
    'Explore the given TLA+ module by using TLC to randomly generate and print a behavior—a sequence of states, where each state represents an assignment of values to the module\'s variables. Choose a meaningful value for the behavior length N that is neither too small nor too large, based on your estimate of what constitutes an interesting behavior for this particular module.',
    {
      fileName: z.string(),
      behaviorLength: z.number().min(1),
      cfgFile: z.string().optional(),
      extraOpts: z.array(z.string()).optional(),
      extraJavaOpts: z.array(z.string()).optional(),
      timeoutMs: z.number().int().positive().optional()
    },
    async ({ fileName, behaviorLength, cfgFile, extraOpts, extraJavaOpts, timeoutMs }: {
      fileName: string;
      behaviorLength: number;
      cfgFile?: string;
      extraOpts?: string[];
      extraJavaOpts?: string[];
      timeoutMs?: number;
    }, context?: ToolContext) => {
      try {
        // Resolve and validate file path
        const absolutePath = resolveAndValidatePath(fileName, config.workingDir);

        // Check if file exists
        if (!fs.existsSync(absolutePath)) {
          return {
            content: [{
              type: 'text',
              text: `File ${absolutePath} does not exist on disk.`
            }]
          };
        }

        // Ensure tools directory is configured
        if (!config.toolsDir) {
          return {
            content: [{
              type: 'text',
              text: 'TLA+ tools directory not configured. Use --tools-dir to specify the location.'
            }]
          };
        }

        // Find spec files (TLA + CFG)
        const specFiles = await getSpecFiles(absolutePath);
        if (!specFiles) {
          const specName = path.basename(absolutePath, path.extname(absolutePath));
          return {
            content: [{
              type: 'text',
              text: `No ${specName}.cfg or MC${specName}.tla/MC${specName}.cfg files found for ${absolutePath}. ` +
                `Please create an MC${specName}.tla and MC${specName}.cfg file according to the provided TLC guidelines.`
            }]
          };
        }

        // Use provided cfgFile if specified
        // @implements REQ-CODEX-001, SCN-CODEX-001-01, SCN-CODEX-001-02
        let configFilePath = specFiles.cfgFilePath;
        if (cfgFile) {
          const resolvedCfgPath = resolveAndValidatePath(cfgFile, config.workingDir);
          if (!fs.existsSync(resolvedCfgPath)) {
            return {
              content: [{
                type: 'text',
                text: `Config file ${resolvedCfgPath} does not exist on disk.`
              }]
            };
          }
          // @implements REQ-CODEX-002, SCN-CODEX-002-01
          configFilePath = resolvedCfgPath;
        }

        // Build TLC options: -cleanup -simulate -invlevel <behaviorLength> [extraOpts]
        const tlcOptions = [
          '-cleanup',
          '-simulate',
          '-invlevel',
          behaviorLength.toString(),
          ...(extraOpts || [])
        ];
        // Add stopAfter for exploration (3 seconds)
        const javaOpts = ['-Dtlc2.TLC.stopAfter=3', ...(extraJavaOpts || [])];

        // Run TLC and wait for completion
        const timeoutMsResolved = resolveTimeoutMs(timeoutMs, 'TLC_EXPLORE_TIMEOUT_MS', DEFAULT_EXPLORE_TIMEOUT_MS);
        const signal = getAbortSignal(context);
        const result = await runTlcAndWait(
          specFiles.tlaFilePath,
          path.basename(configFilePath),
          tlcOptions,
          javaOpts,
          config.toolsDir,
          config.javaHome || undefined,
          timeoutMsResolved,
          signal,
          (progress) => {
            sendProgress(context, progress.progress, progress.total, progress.message).catch(() => {});
          }
        );

        return {
          content: [{
            type: 'text',
            text: `Behavior exploration completed with exit code ${result.exitCode}.\n\n` +
              `Output:\n${result.output.join('\n')}`
          }]
        };
      } catch (error) {
        return {
          content: [{
            type: 'text',
            text: formatErrorResponse(error as Error)
          }]
        };
      }
    }
  );

  // Tool 4: Trace replay
  server.tool(
    'tlaplus_mcp_tlc_trace',
    'Load and replay a previously generated TLC trace file. This tool is particularly useful after tlaplus_mcp_tlc_check finds a counterexample and automatically generates a trace file. Trace files are .tlc files stored in the .vscode/tlc/ directory with the naming pattern: {specName}_trace_T{timestamp}_F{fp}_W{workers}_M{mode}.tlc. By rerunning TLC with -loadtrace, you can add or modify ALIAS expressions in the configuration file to derive compound values, rename variables, filter out variables, or create custom animations of the trace for better analysis. The ALIAS feature allows you to evaluate expressions on pairs of states (s -> t) in the error trace and display custom formatted output instead of raw state dumps. For comprehensive guidance on ALIAS expressions, see resource tlaplus://knowledge/tlc-alias-expressions.md.',
    {
      fileName: z.string(),
      traceFile: z.string(),
      cfgFile: z.string().optional(),
      extraOpts: z.array(z.string()).optional(),
      extraJavaOpts: z.array(z.string()).optional()
    },
    async ({ fileName, traceFile, cfgFile, extraOpts, extraJavaOpts }: {
      fileName: string;
      traceFile: string;
      cfgFile?: string;
      extraOpts?: string[];
      extraJavaOpts?: string[];
    }, context?: ToolContext) => {
      try {
        const absolutePath = resolveAndValidatePath(fileName, config.workingDir);

        if (!fs.existsSync(absolutePath)) {
          return {
            content: [{
              type: 'text',
              text: `File ${absolutePath} does not exist on disk.`
            }]
          };
        }

        if (!config.toolsDir) {
          return {
            content: [{
              type: 'text',
              text: 'TLA+ tools directory not configured. Use --tools-dir to specify the location.'
            }]
          };
        }

        const specFiles = await getSpecFiles(absolutePath);
        if (!specFiles) {
          const specName = path.basename(absolutePath, path.extname(absolutePath));
          return {
            content: [{
              type: 'text',
              text: `No ${specName}.cfg or MC${specName}.tla/MC${specName}.cfg files found for ${absolutePath}. ` +
                `Please create an MC${specName}.tla and MC${specName}.cfg file according to the provided TLC guidelines.`
            }]
          };
        }

        // @implements REQ-CODEX-001, SCN-CODEX-001-01, SCN-CODEX-001-03
        let configFilePath = specFiles.cfgFilePath;
        if (cfgFile) {
          const resolvedCfgPath = resolveAndValidatePath(cfgFile, config.workingDir);
          if (!fs.existsSync(resolvedCfgPath)) {
            return {
              content: [{
                type: 'text',
                text: `Config file ${resolvedCfgPath} does not exist on disk.`
              }]
            };
          }
          // @implements REQ-CODEX-002, SCN-CODEX-002-01
          configFilePath = resolvedCfgPath;
        }

        const absoluteTracePath = resolveAndValidatePath(traceFile, config.workingDir);
        if (!fs.existsSync(absoluteTracePath)) {
          return {
            content: [{
              type: 'text',
              text: `Trace file ${absoluteTracePath} does not exist on disk.`
            }]
          };
        }

        const fpValue = extractFingerprintFromTrace(absoluteTracePath);
        const baseOptions = fpValue === undefined
          ? ['-cleanup', '-loadtrace', 'tlc', absoluteTracePath]
          : ['-cleanup', '-fp', String(fpValue), '-loadtrace', 'tlc', absoluteTracePath];
        const tlcOptions = baseOptions.concat(extraOpts || []);
        const javaOpts = extraJavaOpts || [];

        const timeoutMsResolved = resolveTimeoutMs(undefined, 'TLC_TRACE_TIMEOUT_MS', DEFAULT_TRACE_TIMEOUT_MS);
        const signal = getAbortSignal(context);
        const result = await runTlcAndWait(
          specFiles.tlaFilePath,
          path.basename(configFilePath),
          tlcOptions,
          javaOpts,
          config.toolsDir,
          config.javaHome || undefined,
          timeoutMsResolved,
          signal,
          (progress) => {
            sendProgress(context, progress.progress, progress.total, progress.message).catch(() => {});
          }
        );

        return {
          content: [{
            type: 'text',
            text: `Trace replay completed with exit code ${result.exitCode}.\n\n` +
              `Output:\n${result.output.join('\n')}`
          }]
        };
      } catch (error) {
        return {
          content: [{
            type: 'text',
            text: formatErrorResponse(error as Error)
          }]
        };
      }
    }
  );
}
