import { z } from 'zod';
import { McpServer } from '@modelcontextprotocol/sdk/server/mcp.js';
import * as fs from 'fs';
import * as path from 'path';
import { ServerConfig } from '../types';
import { resolveAndValidatePath } from '../utils/paths';
import { runSanyParse, parseSanyOutput } from '../utils/sany';
import { extractSymbols } from '../utils/symbols';
import { isJarfileUri, parseJarfileUri, listTlaModulesInJar, resolveJarfilePath } from '../utils/jarfile';
import { getModuleSearchPaths } from '../utils/tla-tools';
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
    ],
    [ErrorCode.XMLEXPORTER_USAGE_ERROR]: [
      '- Run `npm run setup` to install pinned tools (v1.8.0)',
      '- Verify `tools/tla2tools.jar` matches v1.8.0 with correct checksum',
      '- If checksum mismatch: delete `tools/tla2tools.jar` and re-run `npm run setup`',
      '- This error indicates XMLExporter argument incompatibility with your TLA+ tools version'
    ]
  };

  return suggestions[code] || ['- Check error message for details'];
}

/**
 * Register all SANY tools with the MCP server
 * - parse: Parse TLA+ module for syntax errors
 * - symbol: Extract symbols from TLA+ module
 * - modules: List available TLA+ modules
 */
export async function registerSanyTools(
  server: any,
  config: ServerConfig
): Promise<void> {
  // Tool 1: Parse
  server.tool(
    'sany_parse',
    'Parse the input TLA+ module using SANY from the TLA+ tools. Use SANY to perform syntax and level-checking of the module. Ensure that the input is provided as a fully qualified file path, as required by the tool.',
    {
      fileName: z.string()
    },
    async ({ fileName }: { fileName: string }) => {
      try {
        if (!config.toolsDir) {
          return {
            content: [{
              type: 'text',
              text: 'TLA+ tools directory not configured. Use --tools-dir to specify the location.'
            }]
          };
        }

        let absolutePath: string;

        if (isJarfileUri(fileName)) {
          try {
            absolutePath = resolveJarfilePath(fileName);
          } catch (err) {
            return {
              content: [{
                type: 'text',
                text: `Error resolving jarfile URI: ${err instanceof Error ? err.message : String(err)}`
              }]
            };
          }
        } else {
          absolutePath = resolveAndValidatePath(fileName, config.workingDir);
          if (!fs.existsSync(absolutePath)) {
            return {
              content: [{
                type: 'text',
                text: `File ${absolutePath} does not exist on disk.`
              }]
            };
          }
        }

        const procInfo = await runSanyParse(absolutePath, config.toolsDir, config.javaHome || undefined);
        const result = await parseSanyOutput(procInfo);

        if (result.success) {
          return {
            content: [{
              type: 'text',
              text: `No errors found in the TLA+ specification ${absolutePath}.`
            }]
          };
        } else {
          const errorMessages = result.errors.map(err => {
            return `Parsing of file ${err.file} failed at line ${err.line} with error: '${err.message}'`;
          });

          return {
            content: [{
              type: 'text',
              text: errorMessages.join('\n')
            }]
          };
        }
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

  // Tool 2: Symbol extraction
  server.tool(
    'sany_symbol',
    'Extract all symbols from the given TLA+ module. Use this tool to identify the symbols defined in a TLA+ specification—such as when generating a TLC configuration file. It assists in determining the list of CONSTANTS, the initialization predicate, the next-state relation, the overall behavior specification (Spec), and any defined safety or liveness properties. Note: SANY expects the fully qualified file path to the TLA+ module.',
    {
      fileName: z.string().describe('The full path to the file containing the TLA+ module (including jarfile:... paths for modules inside JAR archives).'),
      includeExtendedModules: z.boolean().optional().describe('If true, includes symbols from extended and instantiated modules. By default, only symbols from the current module are included.')
    },
    async ({ fileName, includeExtendedModules }: { fileName: string; includeExtendedModules?: boolean }) => {
      try {
        if (!config.toolsDir) {
          return {
            content: [{
              type: 'text',
              text: 'TLA+ tools directory not configured. Use --tools-dir to specify the location.'
            }]
          };
        }

        let absolutePath: string;

        if (isJarfileUri(fileName)) {
          try {
            absolutePath = resolveJarfilePath(fileName);
          } catch (err) {
            return {
              content: [{
                type: 'text',
                text: `Error resolving jarfile URI: ${err instanceof Error ? err.message : String(err)}`
              }]
            };
          }
        } else {
          absolutePath = resolveAndValidatePath(fileName, config.workingDir);
          if (!fs.existsSync(absolutePath)) {
            return {
              content: [{
                type: 'text',
                text: `File ${absolutePath} does not exist on disk.`
              }]
            };
          }
        }

        const result = await extractSymbols(
          absolutePath,
          config.toolsDir,
          includeExtendedModules ?? false,
          config.javaHome || undefined
        );

        return {
          content: [{
            type: 'text',
            text: JSON.stringify(result, null, 2)
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

  // Tool 3: List modules
  server.tool(
    'sany_modules',
    'Retrieves a list of all TLA+ modules recognized by SANY, making it easy to see which modules can be imported into a TLA+ specification.',
    {},
    async () => {
      try {
        if (!config.toolsDir) {
          return {
            content: [{
              type: 'text',
              text: 'TLA+ tools directory not configured. Use --tools-dir to specify the location.'
            }]
          };
        }

        const searchPaths = getModuleSearchPaths(config.toolsDir);
        const results: string[] = [];
        const errors: string[] = [];

        for (const searchPath of searchPaths) {
          if (isJarfileUri(searchPath)) {
            try {
              const { jarPath, innerPath } = parseJarfileUri(searchPath);
              const modules = listTlaModulesInJar(jarPath, innerPath, true);
              results.push(...modules);
            } catch (err) {
              errors.push(`Warning: Failed to scan ${searchPath}: ${err instanceof Error ? err.message : String(err)}`);
            }
          } else {
            if (!fs.existsSync(searchPath)) {
              continue;
            }

            try {
              const entries = await fs.promises.readdir(searchPath);
              for (const entry of entries) {
                if (!entry.endsWith('.tla')) continue;
                if (entry.startsWith('_')) continue;
                results.push(path.join(searchPath, entry));
              }
            } catch (err) {
              errors.push(`Warning: Failed to read ${searchPath}: ${err instanceof Error ? err.message : String(err)}`);
            }
          }
        }

        const legacyPath = path.join(config.toolsDir, 'StandardModules');
        if (fs.existsSync(legacyPath) && !searchPaths.includes(legacyPath)) {
          try {
            const entries = await fs.promises.readdir(legacyPath);
            for (const entry of entries) {
              if (!entry.endsWith('.tla')) continue;
              if (entry.startsWith('_')) continue;
              results.push(path.join(legacyPath, entry));
            }
          } catch {
            // Ignore errors on legacy path
          }
        }

        if (results.length === 0 && errors.length === 0) {
          return {
            content: [{
              type: 'text',
              text: 'No TLA+ modules found. Standard modules are typically bundled in JAR files. ' +
                'JAR file support will be added in a future update.'
            }]
          };
        }

        let output = results.join('\n');
        if (errors.length > 0) {
          output += '\n\n' + errors.join('\n');
        }

        return {
          content: [{ type: 'text', text: output }]
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
