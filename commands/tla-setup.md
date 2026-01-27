---
name: tla-setup
description: Verify TLA+ tools installation and fix common issues
argument-hint: ""
allowed-tools: [Bash, Read, Write, Grep]
---

# TLA+ Setup and Verification

Interactive command to verify TLA+ tools installation and fix common configuration issues.

## Usage

```
/tla-setup
/tla-setup --fix
```

## What This Command Does

1. Checks Java installation (version >= 11)
2. Verifies TLA+ tools (tla2tools.jar, CommunityModules-deps.jar)
3. Tests MCP server connection
4. Validates plugin structure
5. Offers to fix issues automatically

## Verification Steps

### 1. Java Check
- Locates Java executable
- Verifies version 11 or higher
- Shows Java path and version

**If missing**: Provides installation instructions for Java

### 2. TLA+ Tools Check
- Checks for tla2tools.jar
- Checks for CommunityModules-deps.jar
- Verifies files are readable

**If missing**: Offers to download tools automatically

### 3. MCP Server Check
- Verifies dist/index.js exists
- Tests server can start
- Validates MCP tool availability

**If issues**: Suggests running `npm run build`

### 4. Plugin Structure Check
- Verifies all required directories exist
- Checks plugin.json manifest
- Validates skills, commands, agents

### 5. Test Parse
- Attempts to parse a simple test spec
- Confirms end-to-end functionality

## Auto-Fix Mode

With `--fix` flag, automatically:
- Downloads missing TLA+ tools
- Runs npm build if needed
- Creates missing directories
- Fixes common permission issues

## Output

Displays checklist with status:
- ✓ Java 17 found at /usr/lib/jvm/java-17
- ✓ TLA+ tools present
- ✓ MCP server compiled
- ⚠ Missing commands directory
- ✗ Parse test failed

## When to Use

- After installing plugin
- When commands don't work
- Before starting TLA+ work
- After system updates
- When troubleshooting issues

## Related

- Run `npm run verify` for command-line verification
- Run `scripts/verify.sh --fix` for automated fixes
- Check `.claude/tlaplus.local.md` for custom configuration

## Implementation

Execute verification script and present results interactively. Offer fixes based on detected issues.
