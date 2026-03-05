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
import { formatErrorResponse } from './shared/error-formatting';
import { registerTool } from './shared/tool-registration';

/**
 * Register all SANY tools with the MCP server
 * - parse: Parse TLA+ module for syntax errors
 * - symbol: Extract symbols from TLA+ module
 * - modules: List available TLA+ modules
 */
// @implements REQ-REVIEW-002, SCN-REVIEW-002-01
export async function registerSanyTools(
  server: McpServer,
  config: ServerConfig
): Promise<void> {
  // Tool 1: Parse
  registerTool(server,
    'tlaplus_mcp_sany_parse',
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

        // @implements REQ-CODEX-005, SCN-CODEX-005-01, SCN-CODEX-005-03
        // @implements REQ-CODEX-006, SCN-CODEX-006-01
        if (isJarfileUri(fileName)) {
          // Parse the jarfile URI first — report parse errors distinctly
          let jarPath: string;
          try {
            ({ jarPath } = parseJarfileUri(fileName));
          } catch (err) {
            return {
              content: [{
                type: 'text',
                text: `Invalid jarfile URI: ${err instanceof Error ? err.message : String(err)}`
              }]
            };
          }
          // Validate JAR file path against workingDir when confined
          if (config.workingDir) {
            try {
              resolveAndValidatePath(jarPath, config.workingDir);
            } catch (err) {
              const message = err instanceof Error ? err.message : String(err);
              return {
                content: [{
                  type: 'text',
                  text: message.startsWith('Access denied:') ? message : `Access denied: ${message}`
                }]
              };
            }
          }
          try {
            absolutePath = await resolveJarfilePath(fileName);
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
  registerTool(server,
    'tlaplus_mcp_sany_symbol',
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

        // @implements REQ-CODEX-005, SCN-CODEX-005-02, SCN-CODEX-005-03
        // @implements REQ-CODEX-006, SCN-CODEX-006-01
        if (isJarfileUri(fileName)) {
          // Parse the jarfile URI first — report parse errors distinctly
          let jarPath: string;
          try {
            ({ jarPath } = parseJarfileUri(fileName));
          } catch (err) {
            return {
              content: [{
                type: 'text',
                text: `Invalid jarfile URI: ${err instanceof Error ? err.message : String(err)}`
              }]
            };
          }
          // Validate JAR file path against workingDir when confined
          if (config.workingDir) {
            try {
              resolveAndValidatePath(jarPath, config.workingDir);
            } catch (err) {
              const message = err instanceof Error ? err.message : String(err);
              return {
                content: [{
                  type: 'text',
                  text: message.startsWith('Access denied:') ? message : `Access denied: ${message}`
                }]
              };
            }
          }
          try {
            absolutePath = await resolveJarfilePath(fileName);
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
  registerTool(server,
    'tlaplus_mcp_sany_modules',
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
