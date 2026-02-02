# Installation Guide - TLA+ AI Tools

Complete installation guide for Claude Code and OpenCode.

## Quick Start

```bash
# Clone or navigate to repository
cd tlaplus-ai-tools

# Install dependencies
npm install

# Build MCP server
npm run build

# Download TLA+ tools (if not already done)
npm run setup

# Verify installation
npm run verify

# Install globally (optional)
npm link
```

## Migrating from v1.x

**IMPORTANT**: Version 2.0+ uses global installation only. Per-project installation (`.opencode/` directory) is no longer supported.

If upgrading from v1.x:

```bash
# Remove per-project artifacts (optional)
rm -rf .opencode/

# Install globally
npm run install-global
```

See [Uninstallation](#migrating-from-v1x-per-project-installation) for details.

## Prerequisites

### Required

- **Node.js** 18.0.0 or higher
  - Check: `node --version`
  - Install: https://nodejs.org/

- **Java** 11 or higher (for TLA+ tools)
  - Check: `java -version`
  - Install: https://adoptium.net/

### Optional

- **Git** (for cloning repository)

## Installation Methods

### Method 1: Claude Code Marketplace (Coming Soon)

```
1. Open Claude Code
2. Run: /plugin install tlaplus
3. Plugin auto-downloads TLA+ tools
4. Ready to use!
```

### Method 2: Global npm Install

```bash
# Install globally from npm (when published)
npm install -g tlaplus-ai-tools

# Or install from local directory
cd tlaplus-ai-tools
npm install
npm run build
npm run setup
npm link

# For OpenCode: Run global installer
npm run install-global

# Start Claude Code or OpenCode
claude
# or
opencode

# Verify plugin loaded
/plugin list
```

**Global Install for OpenCode**:

The `npm run install-global` command installs the plugin globally for OpenCode:

- Patches `~/.config/opencode/opencode.json` to enable MCP server
- Installs skills to `~/.config/opencode/skills/` (symlink or copy)
- Installs commands to `~/.config/opencode/commands/` (symlink or copy)
- Writes installation marker to prevent repeated prompts

**Idempotent**: Running `npm run install-global` multiple times is safe and won't duplicate or fail.

### Method 3: Local Plugin Directory

```bash
# Clone repository
git clone https://github.com/photoszzt/tlaplus-ai-tools.git
cd tlaplus-ai-tools

# Install and build
npm install
npm run build
npm run setup

# Start Claude Code with plugin directory
claude --plugin-dir $(pwd)
```

### Method 4: Development Mode

```bash
# For plugin development
cd tlaplus-ai-tools

# Install dependencies
npm install

# Build in watch mode
npm run dev

# In another terminal, start Claude Code
claude --plugin-dir $(pwd)
```

## Platform-Specific Instructions

### macOS

```bash
# Install Node.js via Homebrew
brew install node

# Install Java via Homebrew
brew install openjdk@17

# Set JAVA_HOME
echo 'export JAVA_HOME=$(/usr/libexec/java_home)' >> ~/.zshrc
source ~/.zshrc

# Install plugin
cd tlaplus-ai-tools
npm install
npm run build
npm run setup
npm link
```

### Linux (Ubuntu/Debian)

```bash
# Install Node.js
curl -fsSL https://deb.nodesource.com/setup_20.x | sudo -E bash -
sudo apt-get install -y nodejs

# Install Java
sudo apt-get install -y openjdk-17-jdk

# Set JAVA_HOME
echo 'export JAVA_HOME=/usr/lib/jvm/java-17-openjdk-amd64' >> ~/.bashrc
source ~/.bashrc

# Install plugin
cd tlaplus-ai-tools
npm install
npm run build
npm run setup
npm link
```

### Windows

```powershell
# Install Node.js from https://nodejs.org/
# Install Java from https://adoptium.net/

# Set JAVA_HOME in System Environment Variables
# Add to PATH: %JAVA_HOME%\bin

# Install plugin
cd tlaplus-ai-tools
npm install
npm run build
npm run setup
npm link
```

**Note on Symlinks**: On Windows, the installer attempts to create symlinks for skills and commands. If symlink creation fails (e.g., due to lack of Developer Mode or administrative privileges), it will **automatically fall back to copying** the files. No manual intervention or special permissions are required.

## Configuration

### Claude Code Configuration

**Location**:

- macOS: `~/Library/Application Support/Claude/claude_desktop_config.json`
- Linux: `~/.config/Claude/claude_desktop_config.json`
- Windows: `%APPDATA%\Claude\claude_desktop_config.json`

**Minimal Configuration**:

```json
{
  "plugins": {
    "tlaplus": {
      "enabled": true
    }
  }
}
```

**With Custom Settings** (optional):

Create `.claude/tlaplus.local.md` in your project:

```yaml
---
javaHome: /usr/lib/jvm/java-17
toolsDir: /opt/tlaplus/tools
tlcDefaults:
  workers: 4
  heapSize: 4096
hooks:
  autoParseOnSave: true
  suggestConfigGeneration: true
---
# TLA+ Plugin Settings

Custom configuration for this project.
```

### OpenCode Configuration

After running `npm run install-global`, the plugin is configured globally:

**What gets installed**:
- MCP server config: `~/.config/opencode/opencode.json`
- Skills: `~/.config/opencode/skills/tla-*`
- Commands: `~/.config/opencode/commands/tla-*`
- Installation marker: `~/.config/opencode/.tlaplus-install-state.json`

**Commands**: 6 TLA+ commands are available globally:
- `/tla-parse`, `/tla-symbols`, `/tla-smoke`, `/tla-check`, `/tla-review`, `/tla-setup`

These commands are automatically discovered by OpenCode and invoked as `/command-name` in the TUI.

**Verification**:

```bash
# Check MCP server connection
opencode mcp list
# Expected: ✓ tlaplus [connected]

# Check skills
opencode debug skill | grep tla-
# Expected: All 6 TLA+ skills listed
```

## Verification

After installation, verify everything works:

```bash
# Run verification script
npm run verify

# Expected output:
# ✓ Java found
# ✓ Node.js version OK
# ✓ TLA+ tools present
# ✓ Plugin structure valid
# ✓ MCP server compiled
# ✓ All checks passed!
```

### Verify in Claude Code

```
# Check plugin loaded
/plugin list

# Should show: tlaplus

# Check skills available
/skills list

# Should show:
# - tla-getting-started
# - tla-model-checking
# - tla-refinement-proofs
# - tla-spec-review
# - tla-debug-violations
# - tla-create-animations

# Check commands available
/help

# Should show:
# - /tla-parse
# - /tla-check
# - /tla-smoke
# - /tla-symbols
# - /tla-review
# - /tla-setup
```

### Test Basic Functionality

Create a test spec:

```bash
cat > /tmp/Test.tla << 'EOF'
---- MODULE Test ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = x + 1
====
EOF
```

Test commands:

```
/tla-parse @/tmp/Test.tla
# Should parse successfully

/tla-symbols @/tmp/Test.tla
# Should extract symbols (Init, Next, x)

/tla-setup
# Should verify installation
```

## Troubleshooting

### Java Not Found

**Error**: `Java executable not found`

**Solution**:

```bash
# Check Java installed
java -version

# If not installed:
# macOS: brew install openjdk@17
# Linux: sudo apt-get install openjdk-17-jdk
# Windows: Download from https://adoptium.net/

# Set JAVA_HOME
export JAVA_HOME=/path/to/java
```

### TLA+ Tools Not Found

**Error**: `TLA+ tools jar not found`

**Solution**:

```bash
# Run setup to download tools
npm run setup

# Or specify custom location
export TLA_TOOLS_DIR=/path/to/tools
```

### Plugin Not Loading

**Error**: Plugin doesn't appear in `/plugin list`

**Solution**:

```bash
# Verify plugin directory
ls -la .claude-plugin/plugin.json

# Check npm link
npm link

# Restart Claude Code
# Try explicit plugin directory
claude --plugin-dir $(pwd)
```

### Commands Not Showing

**Error**: Commands don't appear in `/help`

**Solution**:

```bash
# Verify commands directory
ls -la commands/*.md

# Check plugin.json
cat .claude-plugin/plugin.json | grep commands

# Restart Claude Code
```

### Build Errors

**Error**: TypeScript compilation fails

**Solution**:

```bash
# Clean and rebuild
rm -rf dist node_modules
npm install
npm run build

# Check for errors
npx tsc --noEmit
```

### Permission Errors

**Error**: `EACCES: permission denied`

**Solution**:

```bash
# Fix npm permissions (global)
sudo chown -R $(whoami) ~/.npm
sudo chown -R $(whoami) /usr/local/lib/node_modules

# Or use npx without global install
npx tlaplus-ai-tools
```

## Updating

### Update from npm

```bash
npm update -g tlaplus-ai-tools
```

### Update from git

```bash
cd tlaplus-ai-tools
git pull origin main
npm install
npm run build
npm run setup  # If tools updated

# For OpenCode global install: Re-run installer
npm run install-global
```

### Update TLA+ Tools Only

```bash
npm run setup
```

This downloads the latest TLA+ tools.

## Uninstallation

### Remove Global Installation

```bash
# Uninstall npm package
npm uninstall -g tlaplus-ai-tools
# Or if linked
npm unlink
```

### Remove OpenCode Global Integration

To completely remove the global OpenCode integration:

```bash
# macOS/Linux
rm -rf ~/.config/opencode/skills/tla-*
rm -rf ~/.config/opencode/commands/tla-*
rm ~/.config/opencode/.tlaplus-install-state.json

# Windows (PowerShell)
Remove-Item -Recurse -Force "$HOME\.config\opencode\skills\tla-*"
Remove-Item -Recurse -Force "$HOME\.config\opencode\commands\tla-*"
Remove-Item -Force "$HOME\.config\opencode\.tlaplus-install-state.json"
```

**Note**: You may also need to manually remove the `tlaplus` MCP server entry from `~/.config/opencode/opencode.json`.

### Migrating from v1.x (Per-Project Installation)

If you previously used v1.x with per-project installation, remove the `.opencode/` directory:

```bash
# macOS/Linux
rm -rf .opencode/

# Windows (PowerShell)
Remove-Item -Recurse -Force ".opencode\"
```

Then install globally using `npm run install-global`.

**Note**: The `.opencode/` directory is no longer used in v2.0+.

### Reset Installation State

If you need to reinstall or reset the installation:

```bash
# macOS/Linux
rm ~/.config/opencode/.tlaplus-install-state.json
npm run install-global

# Windows (PowerShell)
Remove-Item -Force "$HOME\.config\opencode\.tlaplus-install-state.json"
npm run install-global
```

### Remove Configuration

```bash
# Claude Code config
# Edit and remove tlaplus section from:
# macOS: ~/Library/Application Support/Claude/claude_desktop_config.json
# Linux: ~/.config/Claude/claude_desktop_config.json
# Windows: %APPDATA%\Claude\claude_desktop_config.json

# Project settings
rm .claude/tlaplus.local.md
```

## Advanced Configuration

### Custom Java Options

Set in `.claude/tlaplus.local.md`:

```yaml
---
tlcDefaults:
  heapSize: 8192 # 8GB heap
  workers: 8 # 8 worker threads
---
```

### Custom TLA+ Tools Location

```yaml
---
toolsDir: /opt/tlaplus/tools
---
```

### Disable Hooks

```yaml
---
hooks:
  autoParseOnSave: false
  suggestConfigGeneration: false
---
```

## Support

### Getting Help

- **Documentation**: Check TESTING.md and README.md
- **Issues**: https://github.com/photoszzt/tlaplus-ai-tools/issues
- **TLA+ Help**: https://groups.google.com/g/tlaplus

### Commands for Help

```
/tla-setup          # Verify installation
/tla-parse --help   # Command help
/help               # All available commands
```

### Debug Mode

Enable verbose logging:

```bash
DEBUG=1 npm run verify
VERBOSE=1 claude --plugin-dir $(pwd)
```

## Next Steps

After installation:

1. **Learn TLA+**: Trigger `tla-getting-started` skill
2. **Create first spec**: Follow tutorial
3. **Generate config**: Use `/tla-symbols`
4. **Run model checking**: Use `/tla-check`
5. **Review specs**: Use `/tla-review`

Happy formal verification! 🎉
