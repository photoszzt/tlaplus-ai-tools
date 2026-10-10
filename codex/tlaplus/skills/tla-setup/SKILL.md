---
name: tla-setup
description: >-
  Verify or repair the TLA+ Codex plugin, Java, TLA+ tools JARs, MCP server,
  and SANY parser. Use for setup, installation, missing tools, Java errors,
  MCP connection failures, or an environment check.
version: 1.0.0
---

# TLA+ tools setup and verification

Check the complete toolchain and report the result of each check. A spec file is
optional. Use the TLA+ MCP tools for parsing and model checking; shell commands
are for environment checks and setup only.

## 1. Check Java

Run `java -version` and read its output, which Java commonly writes to stderr.
Confirm that the executable works and its major version is at least 11. Report
the detected version. If Java is missing or too old, explain that Java 11+ is
required and give installation guidance for the user's platform. Recheck after
installation when the user has asked you to set up or repair the environment.

## 2. Check the bundled TLA+ tools

Start from this loaded skill's absolute file path and walk up to the directory
containing `.codex-plugin/plugin.json`. That is the installed runtime root.
`codex plugin list --json` identifies the installation, but its source path
is the marketplace checkout, not the runtime cache; do not repair that source
by mistake. Read the root manifest's declared `.mcp-codex.json`; its
`cwd: "."` resolves to this installed plugin root. Check that both of these
files exist there and have nonzero size:

- `tools/tla2tools.jar`
- `tools/CommunityModules-deps.jar`

Report each path and size. The first MCP startup downloads missing JARs. If
startup setup failed, fix the reported Java, npm, or network error and restart
the MCP server. For manual repair, run `npm run setup` in the installed runtime
root. Do not substitute unverified JAR versions. Reinstall `tlaplus@tlaplus` and
start a new task after refreshing a Git marketplace installation.

## 3. Check the MCP connection

Find the MCP tools ending in `tlaplus_mcp_sany_modules` and
`tlaplus_mcp_sany_parse`; Codex may prefix their names. Call
`tlaplus_mcp_sany_modules` and report how many modules it lists. If it works,
the MCP server is connected.

If the tools are missing or the call fails:

1. Check `codex plugin list --json` for an enabled `tlaplus` installation and
   report its marketplace and source path.
2. Check the installed plugin's `.mcp-codex.json` command, args, and cwd. Confirm
   that `scripts/start.js` and `src/index.ts` exist in the runtime root.
3. Check Node.js availability and whether the runtime dependencies declared in
   the plugin's `package.json` are installed. Startup installs missing production
   dependencies with npm lifecycle scripts disabled; it runs TypeScript through
   `tsx` without a manual build. If automatic setup failed, fix the reported
   error and restart. For manual provisioning, run
   `npm ci --omit=dev --ignore-scripts` and `npm run setup` in the installed root.
4. If the plugin was just installed or rebuilt, start a new Codex task so the
   new MCP tools and skills can load. If tracked source files are missing,
   refresh the marketplace and reinstall the plugin.

Do not run Java or TLC directly as a substitute for a failed MCP connection.

## 4. Verify SANY with a known-good spec

Create a temporary directory and write `SetupTest.tla` containing:

```tla
---- MODULE SetupTest ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = x + 1
====
```

Call `tlaplus_mcp_sany_parse` with `fileName` set to the absolute path of that
file. Report whether parsing succeeded and include any error returned by the
tool. Delete the temporary file and directory afterward. If the user supplied
a spec, you may also parse it, but keep the known-good test separate so a user
spec error is not mistaken for a broken installation.

## 5. Report and repair

Summarize Java, both JARs, MCP connection, and SANY parsing as pass or fail,
with the evidence collected above. For every failed check, state the concrete
fix and verify it after applying it when setup or repair was requested. When
all checks pass, suggest `$tla-parse`, `$tla-symbols`, `$tla-smoke`, or
`$tla-check` as appropriate for the user's next task.
