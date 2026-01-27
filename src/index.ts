#!/usr/bin/env node

import { parseArgs } from './cli';
import { TLAPlusMCPServer } from './server';
import { autoDetectToolsDir, autoDetectKbDir, validateDirectory } from './utils/paths';

async function main() {
  try {
    // Parse command line arguments
    const config = parseArgs(process.argv.slice(2));

    // Auto-detect paths if not provided
    if (!config.toolsDir) {
      config.toolsDir = await autoDetectToolsDir();
      if (config.toolsDir) {
        console.error(`[INFO] Auto-detected tools directory: ${config.toolsDir}`);
      }
    }

    if (!config.kbDir) {
      config.kbDir = await autoDetectKbDir();
      if (config.kbDir) {
        console.error(`[INFO] Auto-detected knowledge base directory: ${config.kbDir}`);
      }
    }

    // Validate directories if specified
    if (config.toolsDir) {
      await validateDirectory(config.toolsDir, 'TLA+ tools');
    }

    if (config.kbDir) {
      await validateDirectory(config.kbDir, 'Knowledge base');
    }

    if (config.workingDir) {
      await validateDirectory(config.workingDir, 'Working');
    }

    // Start the server
    const server = new TLAPlusMCPServer(config);
    await server.start();
  } catch (error) {
    console.error('Fatal error:', error instanceof Error ? error.message : String(error));
    process.exit(1);
  }
}

main();
