#!/usr/bin/env node

/**
 * Global Installer for TLA+ AI Tools (OpenCode)
 * 
 * This script installs the TLA+ AI Tools plugin globally for OpenCode:
 * 1. Copies plugin file to ~/.config/opencode/plugins/tlaplus-ai-tools.js
 * 2. Patches global OpenCode config to enable MCP server
 * 3. Installs skills globally (symlink or copy)
 * 4. Installs commands globally (symlink or copy)
 * 5. Writes installation marker
 * 
 * Usage:
 *   npm run install-global
 *   node scripts/install-global.js
 * 
 * Idempotent: Running twice is safe and won't duplicate or fail.
 */

const path = require('path');
const fs = require('fs');

// Get plugin root (where this script is located)
const pluginRoot = path.resolve(__dirname, '..');

// Import installer utilities (compiled TypeScript)
const distPath = path.join(pluginRoot, 'dist', 'opencode');

// Check if dist/ exists
if (!fs.existsSync(distPath)) {
  console.error('❌ Error: dist/ directory not found');
  console.error('');
  console.error('Please run: npm run build');
  console.error('');
  process.exit(1);
}

// Import utilities
let paths, configPatcher, skillsInstaller, commandsInstaller, installState;

try {
  paths = require(path.join(distPath, 'paths.js'));
  configPatcher = require(path.join(distPath, 'config-patcher.js'));
  skillsInstaller = require(path.join(distPath, 'skills-installer.js'));
  commandsInstaller = require(path.join(distPath, 'commands-installer.js'));
  installState = require(path.join(distPath, 'install-state.js'));
} catch (error) {
  console.error('❌ Error: Failed to load installer utilities');
  console.error('');
  console.error('Please run: npm run build');
  console.error('');
  console.error('Details:', error.message);
  process.exit(1);
}

/**
 * Main installation function
 */
async function installGlobal() {
  console.log('╔════════════════════════════════════════════════════════════╗');
  console.log('║  TLA+ AI Tools - Global Installer for OpenCode            ║');
  console.log('╚════════════════════════════════════════════════════════════╝');
  console.log('');

  const globalDir = paths.getGlobalOpenCodeDir();

  console.log(`📁 Installation directory: ${globalDir}`);
  console.log('');

  // Step 1: Check prerequisites
  console.log('🔍 Step 1/5: Checking prerequisites...');

  const distIndexPath = path.join(pluginRoot, 'dist', 'index.js');
  const toolsDir = path.join(pluginRoot, 'tools');

  if (!fs.existsSync(distIndexPath)) {
    console.error('   ❌ Missing: dist/index.js');
    console.error('   Please run: npm run build');
    console.error('');
    process.exit(1);
  }

  if (!fs.existsSync(toolsDir)) {
    console.error('   ❌ Missing: tools/ directory');
    console.error('   Please run: npm run setup');
    console.error('');
    process.exit(1);
  }

  console.log('   ✅ Prerequisites OK');
  console.log('');

  // Step 2: Patch OpenCode config
  console.log('🔧 Step 2/5: Patching OpenCode config...');

  const configPath = path.join(globalDir, 'opencode.json');

  try {
    const patchResult = await configPatcher.patchOpenCodeConfig(
      configPath,
      pluginRoot
    );
    
    if (!patchResult.success) {
      console.error(`   ❌ Failed to patch config: ${patchResult.error}`);
      process.exit(1);
    }
    
    if (patchResult.created) {
      console.log(`   ✅ Created config: ${patchResult.configPath}`);
    } else if (patchResult.modified) {
      console.log(`   ✅ Updated config: ${patchResult.configPath}`);
      if (patchResult.backupPath) {
        console.log(`   📦 Backup saved: ${patchResult.backupPath}`);
      }
    } else {
      console.log(`   ✅ Config already correct (no changes needed)`);
    }
  } catch (error) {
    console.error(`   ❌ Error patching config: ${error.message}`);
    process.exit(1);
  }
  
  console.log('');

  // Step 3: Install skills
  console.log('📚 Step 3/5: Installing skills...');

  try {
    const skillsResult = skillsInstaller.installSkills(pluginRoot);
    
    if (!skillsResult.success) {
      console.error(`   ❌ Failed to install skills`);
      for (const skill of skillsResult.skills) {
        if (skill.error) {
          console.error(`      - ${skill.skillName}: ${skill.error}`);
        }
      }
      process.exit(1);
    }
    
    if (skillsResult.installedCount > 0) {
      console.log(`   ✅ Installed ${skillsResult.installedCount} skill(s)`);
      for (const skill of skillsResult.skills) {
        if (skill.installed) {
          const method = skill.symlinked ? 'symlinked' : 'copied';
          console.log(`      - ${skill.skillName} (${method})`);
        }
      }
    }
    
    if (skillsResult.alreadyInstalledCount > 0) {
      console.log(`   ✅ ${skillsResult.alreadyInstalledCount} skill(s) already installed`);
    }
  } catch (error) {
    console.error(`   ❌ Error installing skills: ${error.message}`);
    process.exit(1);
  }
  
  console.log('');

  // Step 4: Install commands
  console.log('⚡ Step 4/5: Installing commands...');

  try {
    const commandsResult = commandsInstaller.installCommands(pluginRoot);
    
    if (!commandsResult.success) {
      console.error(`   ❌ Failed to install commands`);
      for (const command of commandsResult.commands) {
        if (command.error) {
          console.error(`      - ${command.commandName}: ${command.error}`);
        }
      }
      process.exit(1);
    }
    
    if (commandsResult.installedCount > 0) {
      console.log(`   ✅ Installed ${commandsResult.installedCount} command(s)`);
      for (const command of commandsResult.commands) {
        if (command.installed) {
          const method = command.symlinked ? 'symlinked' : 'copied';
          console.log(`      - ${command.commandName} (${method})`);
        }
      }
    }
    
    if (commandsResult.alreadyInstalledCount > 0) {
      console.log(`   ✅ ${commandsResult.alreadyInstalledCount} command(s) already installed`);
    }
  } catch (error) {
    console.error(`   ❌ Error installing commands: ${error.message}`);
    process.exit(1);
  }
  
  console.log('');

  // Step 5: Write installation marker
  console.log('📝 Step 5/5: Writing installation marker...');

  try {
    const markerPath = installState.getMarkerPath(globalDir);
    installState.writeInstallState(markerPath, 'installed');
    console.log(`   ✅ Marker written: ${markerPath}`);
  } catch (error) {
    console.error(`   ❌ Error writing marker: ${error.message}`);
    // Don't fail installation if marker write fails
  }
  
  console.log('');
  console.log('╔════════════════════════════════════════════════════════════╗');
  console.log('║  ✅ Global installation complete!                          ║');
  console.log('╚════════════════════════════════════════════════════════════╝');
  console.log('');
  console.log('📋 What was installed:');
  console.log(`   • MCP server config: ${configPath}`);
  console.log(`   • Skills: ${path.join(globalDir, 'skills')}`);
  console.log(`   • Commands: ${path.join(globalDir, 'commands')}`);
  console.log('');
  console.log('🚀 Next steps:');
  console.log('   1. Start OpenCode: opencode');
  console.log('   2. Verify MCP connection: opencode mcp list');
  console.log('   3. Try a command: /tla-parse <spec.tla>');
  console.log('');
  console.log('📚 Available skills:');
  console.log('   • tla-getting-started');
  console.log('   • tla-model-checking');
  console.log('   • tla-refinement-proofs');
  console.log('   • tla-spec-review');
  console.log('   • tla-debug-violations');
  console.log('   • tla-create-animations');
  console.log('');
  console.log('⚡ Available commands:');
  console.log('   • /tla-parse, /tla-symbols, /tla-smoke');
  console.log('   • /tla-check, /tla-review, /tla-setup');
  console.log('');
  console.log('💡 To uninstall:');
  console.log(`   • Remove: ${globalDir}`);
  console.log('');
}

// Run installer
installGlobal().catch((error) => {
  console.error('');
  console.error('❌ Installation failed:', error.message);
  console.error('');
  console.error('Stack trace:', error.stack);
  process.exit(1);
});
