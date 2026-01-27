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
# Install globally from npm
npm install -g tlaplus-ai-tools

# Or install from local directory
cd tlaplus-ai-tools
npm install
npm link

# Start Claude Code
cc

# Verify plugin loaded
/plugin list
```

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
cc --plugin-dir $(pwd)

# Or in OpenCode
opencode --plugin-dir $(pwd)
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
cc --plugin-dir $(pwd)
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

**Location**: `~/.config/opencode/plugins/`

Create plugin directory:
```bash
mkdir -p ~/.config/opencode/plugins/tlaplus
```

Link or copy plugin:
```bash
# Link (for development)
ln -s $(pwd) ~/.config/opencode/plugins/tlaplus

# Or copy (for production)
cp -r tlaplus-ai-tools ~/.config/opencode/plugins/tlaplus
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
cc --plugin-dir $(pwd)
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
npx tlaplus-mcp-server
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
```

### Update TLA+ Tools Only

```bash
npm run setup
```

This downloads the latest TLA+ tools.

## Uninstallation

### Remove Global Installation

```bash
npm uninstall -g tlaplus-ai-tools
# Or
npm unlink
```

### Remove Local Installation

```bash
rm -rf tlaplus-ai-tools
```

### Remove Configuration

```bash
# Claude Code config
# Edit and remove tlaplus section from:
# ~/.config/Claude/claude_desktop_config.json

# OpenCode config
rm -rf ~/.config/opencode/plugins/tlaplus

# Project settings
rm .claude/tlaplus.local.md
```

## Advanced Configuration

### Custom Java Options

Set in `.claude/tlaplus.local.md`:

```yaml
---
tlcDefaults:
  heapSize: 8192        # 8GB heap
  workers: 8            # 8 worker threads
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
VERBOSE=1 cc --plugin-dir $(pwd)
```

## Next Steps

After installation:

1. **Learn TLA+**: Trigger `tla-getting-started` skill
2. **Create first spec**: Follow tutorial
3. **Generate config**: Use `/tla-symbols`
4. **Run model checking**: Use `/tla-check`
5. **Review specs**: Use `/tla-review`

Happy formal verification! 🎉
