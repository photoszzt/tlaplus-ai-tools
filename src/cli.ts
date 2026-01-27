import * as fs from 'fs';
import * as path from 'path';
import { ServerConfig } from './types';

/**
 * Parse command line arguments into ServerConfig
 */
export function parseArgs(argv: string[]): ServerConfig {
  const config: ServerConfig = {
    http: false,
    port: 3000,
    workingDir: null,
    toolsDir: null,
    kbDir: null,
    javaHome: null,
    verbose: false,
  };

  for (let i = 0; i < argv.length; i++) {
    const arg = argv[i];

    switch (arg) {
      case '--http':
        config.http = true;
        break;

      case '--port':
        const port = parseInt(argv[++i], 10);
        if (isNaN(port) || port < 0 || port > 65535) {
          throw new Error(`Invalid port number: ${argv[i]}. Must be between 0 and 65535.`);
        }
        config.port = port;
        break;

      case '--working-dir':
        config.workingDir = path.resolve(argv[++i]);
        break;

      case '--tools-dir':
        config.toolsDir = path.resolve(argv[++i]);
        break;

      case '--kb-dir':
        config.kbDir = path.resolve(argv[++i]);
        break;

      case '--java-home':
        config.javaHome = path.resolve(argv[++i]);
        break;

      case '--verbose':
        config.verbose = true;
        break;

      case '--help':
      case '-h':
        showHelp();
        process.exit(0);
        break;

      case '--version':
      case '-v':
        showVersion();
        process.exit(0);
        break;

      default:
        throw new Error(`Unknown argument: ${arg}. Use --help for usage information.`);
    }
  }

  return config;
}

/**
 * Display help information
 */
export function showHelp(): void {
  console.log(`
TLA+ MCP Server

Model Context Protocol (MCP) server for TLA+ formal specification tools.

USAGE:
  tlaplus-mcp-server [options]

OPTIONS:
  --http                    Enable HTTP transport (default: stdio)
  --port <number>           HTTP server port (default: 3000, use 0 for random)
  --working-dir <path>      Working directory for TLA+ files (restricts file access)
  --tools-dir <path>        Path to TLA+ tools directory (auto-detected if omitted)
  --kb-dir <path>           Path to knowledge base directory (auto-detected if omitted)
  --java-home <path>        Path to Java installation (uses system Java if omitted)
  --verbose                 Enable debug logging
  --help, -h                Show this help message
  --version, -v             Show version information

EXAMPLES:
  # Start in stdio mode (for Claude Desktop)
  tlaplus-mcp-server

  # Start in HTTP mode
  tlaplus-mcp-server --http --port 3000

  # Specify custom paths
  tlaplus-mcp-server --tools-dir /opt/tlaplus/tools --kb-dir /opt/tlaplus/docs

  # Restrict to project directory
  tlaplus-mcp-server --working-dir /home/user/my-tla-project

  # Enable verbose logging
  tlaplus-mcp-server --verbose

DOCUMENTATION:
  https://github.com/tlaplus/vscode-tlaplus/tree/master/packages/mcp-server
`);
}

/**
 * Display version information
 */
export function showVersion(): void {
  try {
    const packageJsonPath = path.join(__dirname, '..', 'package.json');
    const packageJson = JSON.parse(fs.readFileSync(packageJsonPath, 'utf-8'));
    console.log(`TLA+ MCP Server v${packageJson.version}`);
  } catch (error) {
    console.log('TLA+ MCP Server (version unknown)');
  }
}
