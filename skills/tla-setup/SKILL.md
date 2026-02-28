---
name: tla-setup
description: Verify TLA+ tools installation and fix common issues
version: 1.0.0
allowed-tools: [Bash, Read, Write, Grep, mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_sany_modules, mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_sany_parse]
---

# TLA+ Tools Setup

Interactive guide to verify and setup TLA+ tools (Java, tla2tools.jar, CommunityModules).

**IMPORTANT: Always use the MCP tools listed above for TLA+ operations. Only use Bash for system checks like `java -version`. Never fall back to running Java or TLC commands via Bash for parsing or model checking.**

## Usage

```
/tla-setup
```

**Note:** This skill does not require a spec file argument. It validates the TLA+ tools installation.

## What This Does

1. Checks Java installation and version
2. Verifies TLA+ tools (tla2tools.jar, CommunityModules-deps.jar)
3. Tests MCP server connection
4. Guides user through any missing dependencies
5. Runs verification tests

**IMPORTANT:** This skill does NOT mutate repository state unless explicitly instructed by the user within the session.

## Implementation

**Step 1: Welcome Message**

Print:

```
═══════════════════════════════════════════════════════════
TLA+ TOOLS SETUP & VERIFICATION
═══════════════════════════════════════════════════════════

This guide will verify your TLA+ tools installation.

Checking:
  1. Java (JDK 11+)
  2. TLA+ Tools (tla2tools.jar, CommunityModules-deps.jar)
  3. MCP Server Connection
  4. Basic Functionality

─────────────────────────────────────────────────────────
```

**Step 2: Check Java**

Run via Bash:

```bash
java -version
```

Parse output to extract version number.

If Java not found:

```
Java not found

Java 11 or higher is required to run TLA+ tools.

Installation instructions:
  macOS:   brew install openjdk@17
  Linux:   sudo apt-get install openjdk-17-jdk
  Windows: Download from https://adoptium.net/

After installing, verify with: java -version
```

If Java version < 11:

```
Java version too old (found: <version>, required: 11+)

Please upgrade Java:
  macOS:   brew install openjdk@17
  Linux:   sudo apt-get install openjdk-17-jdk
  Windows: Download from https://adoptium.net/
```

If Java version >= 11:

```
Java found: <version>
```

**Step 3: Check TLA+ Tools**

Check for tools in expected locations using Read tool:

1. `tools/tla2tools.jar` (relative to repo root)
2. `tools/CommunityModules-deps.jar`

If tools not found:

```
TLA+ tools not found

Expected location: tools/tla2tools.jar

To download tools, run:
  npm run setup

Or manually download:
  1. Visit: https://github.com/tlaplus/tlaplus/releases
  2. Download tla2tools.jar
  3. Place in: tools/tla2tools.jar

For CommunityModules:
  1. Visit: https://github.com/tlaplus/CommunityModules/releases
  2. Download CommunityModules-deps.jar
  3. Place in: tools/CommunityModules-deps.jar
```

If tools found:

```
TLA+ tools found
  - tla2tools.jar: <size> bytes
  - CommunityModules-deps.jar: <size> bytes
```

**Step 4: Check MCP Server Connection**

Try calling `mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_sany_modules` to list available modules.

If MCP call fails:

```
MCP server connection failed

The MCP server may not be running or configured correctly.

Troubleshooting:
  1. Verify plugin is loaded: /plugin list
  2. Check MCP server logs
  3. Rebuild: npm run build
  4. Restart Claude Code
```

If MCP call succeeds:

```
MCP server connected
  Available TLA+ modules: <count>
```

**Step 5: Run Verification Tests**

Test basic functionality by parsing a simple spec.

Create temporary test spec in memory:

```tla
---- MODULE SetupTest ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = x + 1
====
```

Write to temporary file: `/tmp/tlaplus-setup-test.tla`

Call `mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_sany_parse` with the test file.

If parse succeeds:

```
SANY parser working
```

If parse fails:

```
SANY parser test failed

This may indicate a problem with the TLA+ tools or Java setup.
Check the error message above for details.
```

Clean up temporary file.

**Step 6: Summary Report**

Print final summary:

```
─────────────────────────────────────────────────────────
SETUP VERIFICATION SUMMARY
─────────────────────────────────────────────────────────

<if all checks passed>
All checks passed!

Your TLA+ tools are ready to use.

Next steps:
  1. Create a TLA+ specification (.tla file)
  2. Run: /tla-parse <spec.tla>
  3. Run: /tla-symbols <spec.tla>
  4. Run: /tla-smoke <spec.tla>
  5. Run: /tla-check <spec.tla>

For learning TLA+, ask: "teach me TLA+"
<else>
Some checks failed

Please address the issues above before using TLA+ tools.

Common issues:
  - Java not installed or too old -> Install Java 11+
  - TLA+ tools missing -> Run: npm run setup
  - MCP server not running -> Rebuild and restart

Need help? Check INSTALLATION.md or ask for assistance.
<endif>

═══════════════════════════════════════════════════════════
```

**Step 7: Offer Interactive Setup**

If any checks failed, ask user:

```
Would you like me to help fix these issues? (yes/no)
```

If user says yes:

- For missing Java: Provide detailed installation instructions for their platform
- For missing tools: Offer to run `npm run setup` (ask permission first)
- For MCP issues: Guide through rebuild and restart process

**IMPORTANT:** Only mutate repository state (e.g., run `npm run setup`) if user explicitly agrees.

## Example Output (All Checks Pass)

```
═══════════════════════════════════════════════════════════
TLA+ TOOLS SETUP & VERIFICATION
═══════════════════════════════════════════════════════════

This guide will verify your TLA+ tools installation.

Checking:
  1. Java (JDK 11+)
  2. TLA+ Tools (tla2tools.jar, CommunityModules-deps.jar)
  3. MCP Server Connection
  4. Basic Functionality

─────────────────────────────────────────────────────────

Java found: openjdk 17.0.2
TLA+ tools found
  - tla2tools.jar: 15234567 bytes
  - CommunityModules-deps.jar: 8765432 bytes
MCP server connected
  Available TLA+ modules: 47
SANY parser working

─────────────────────────────────────────────────────────
SETUP VERIFICATION SUMMARY
─────────────────────────────────────────────────────────

All checks passed!

Your TLA+ tools are ready to use.

Next steps:
  1. Create a TLA+ specification (.tla file)
  2. Run: /tla-parse <spec.tla>
  3. Run: /tla-symbols <spec.tla>
  4. Run: /tla-smoke <spec.tla>
  5. Run: /tla-check <spec.tla>

For learning TLA+, ask: "teach me TLA+"

═══════════════════════════════════════════════════════════
```
