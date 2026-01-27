#!/usr/bin/env node

/**
 * Post-install script for tlaplus-ai-tools
 * Automatically downloads TLA+ tools if not present
 */

const path = require('path');
const fs = require('fs');

// Determine installation location
function getPluginRoot() {
  if (process.env.CLAUDE_PLUGIN_ROOT) {
    // Marketplace or Claude Code managed installation
    return process.env.CLAUDE_PLUGIN_ROOT;
  } else {
    // npm install or local development
    return path.resolve(__dirname, '..');
  }
}

const pluginRoot = getPluginRoot();
const toolsDir = path.join(pluginRoot, 'tools');

console.log('TLA+ AI Tools: Post-install setup');
console.log(`Plugin root: ${pluginRoot}`);

// Check if tools already exist
const tlaToolsJar = path.join(toolsDir, 'tla2tools.jar');
const communityJar = path.join(toolsDir, 'CommunityModules-deps.jar');

if (fs.existsSync(tlaToolsJar) && fs.existsSync(communityJar)) {
  console.log('✓ TLA+ tools already installed');
  process.exit(0);
}

// Tools not found, run setup
console.log('Downloading TLA+ tools...');
console.log('This may take a minute...');

try {
  // Run the setup script
  const setupScript = path.join(__dirname, 'setup.js');
  require(setupScript);
  console.log('✓ TLA+ tools installed successfully');
  console.log('');
  console.log('Run /tla-setup in Claude Code to verify installation');
} catch (error) {
  console.error('✗ Failed to download TLA+ tools');
  console.error('Error:', error.message);
  console.error('');
  console.error('You can manually run: npm run setup');
  console.error('Or use /tla-setup command in Claude Code');
  // Don't fail installation if tools download fails
  process.exit(0);
}
