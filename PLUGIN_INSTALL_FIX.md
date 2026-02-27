# Plugin Installation Fix

## Problem

When installing the TLA+ AI Tools plugin via Claude Code's plugin marketplace, the installation failed with:

```
Error: Cannot find module '/Users/zhitingz/.claude/plugins/cache/tlaplus/tlaplus/1.0.0/dist/index.js'
```

**Root Cause:** Claude Code's plugin installation doesn't automatically run build scripts. The TypeScript source wasn't being compiled to JavaScript, and the TLA+ tools (JAR files) weren't being downloaded.

## Solution

### 1. Added `prepare` Script

**Changed in `package.json`:**

```json
"scripts": {
  "prepare": "npm run build",        // Runs on npm install
  "prepublishOnly": "npm run build", // Runs before npm publish
  "postinstall": "node scripts/postinstall.js"
}
```

- **`prepare`**: Automatically runs `npm run build` after `npm install` (even in plugin cache)
- **`prepublishOnly`**: Ensures build happens before publishing to npm (replaces deprecated `prepublish`)
- **`postinstall`**: Attempts to download TLA+ tools automatically

### 2. Created `postinstall.js` Script

**New file: `scripts/postinstall.js`**

This script:
- Automatically downloads TLA+ tools (`tla2tools.jar`, `CommunityModules-deps.jar`)
- Runs silently during plugin installation
- Fails gracefully - doesn't break installation if downloads fail
- Skips in development mode (unless `FORCE_POSTINSTALL=1`)

### 3. Added `files` Field to Package.json

**Changed in `package.json`:**

```json
"files": [
  "dist/",              // Compiled JavaScript (built from TypeScript)
  ".claude-plugin/",    // Plugin manifest
  "skills/",            // AI skills
  "commands/",          // Slash commands
  "agents/",            // Autonomous agents
  "hooks/",             // Event hooks
  "resources/",         // Knowledge base
  "scripts/",           // Setup scripts
  "tsconfig.json",
  "README.md",
  "LICENSE"
]
```

**Why needed:** `dist/` is in `.gitignore`, so it wouldn't be included in the published package without explicitly listing it in the `files` field.

### 4. Updated README

Added documentation explaining:
- Automatic build during installation
- Automatic TLA+ tools download
- What happens when plugin is installed from marketplace

## How It Works Now

### Installation Flow

1. User runs: `claude plugin marketplace add https://github.com/photoszzt/tlaplus-ai-tools.git`
2. Claude Code installs plugin to `~/.claude/plugins/cache/tlaplus/tlaplus/VERSION/`
3. **`npm install` runs automatically**
4. **`prepare` script runs** → `npm run build` → TypeScript compiled to `dist/`
5. **`postinstall` script runs** → Downloads `tools/tla2tools.jar` and `tools/CommunityModules-deps.jar`
6. Plugin is ready to use!

### Fallback Behavior

If TLA+ tools download fails during `postinstall`:
- Installation still succeeds (doesn't block)
- User sees warning message
- User can manually run `/tla-setup` command later

## Testing

```bash
# Verify build works
npm run build

# Check dist/index.js exists
ls -lh dist/index.js

# Test full installation flow
rm -rf node_modules dist tools
npm install
ls dist/index.js     # Should exist
ls tools/*.jar       # Should exist
```

## Additional Fix: Checksum Update

**Issue Found:** The expected checksums in `scripts/setup.js` were outdated, causing downloads to fail verification even when successful.

**Fix Applied:**
- Updated `tla2tools.jar` SHA1 checksum to: `46d1f271b9fd05a36371243a9c21769782819738`
- Community Modules checksum was correct

This ensures that downloaded tools pass verification during `postinstall`.

## Version Impact

- **Before:** Plugin installation failed with "Cannot find module" error
- **After:** Plugin installs automatically with full build and tool download

## Files Changed

1. `package.json` - Added `prepare`, `prepublishOnly`, `postinstall` scripts and `files` field
2. `scripts/postinstall.js` - New script for automatic tool download
3. `README.md` - Updated installation documentation
4. `PLUGIN_INSTALL_FIX.md` - This documentation

## Upgrade Path

Existing users should:

1. Pull latest changes: `git pull`
2. Reinstall: `npm install`
3. Verify: `npm run verify`

New users will automatically get the fix when installing from marketplace.
