# Codex plugin

Install from the GitHub or GitLab marketplace URL shown in the repository
README, then add `tlaplus@tlaplus`. No local clone, Python, pnpm, or build step
is required. Node.js 18.14+, npm, Java 11+, and network access are required for
the first startup.

The tracked root `.codex-plugin/plugin.json` loads the skills in
`codex/tlaplus/skills/` and the MCP configuration in `.mcp-codex.json`. Codex
resolves `cwd: "."` to the installed plugin directory. MCP arguments use
relative paths; plugin-root variable interpolation is not supported here.

On the first MCP startup, `scripts/start.js` installs production dependencies
with npm and lifecycle scripts disabled, downloads missing TLA+ JARs using
`scripts/setup.js`, and runs the shared TypeScript server through `tsx`.
Later startups reuse the installed dependencies and JARs. Setup output stays
off stdout so it cannot corrupt the MCP connection.

For local development, register the repository directly with
`codex plugin marketplace add /path/to/tlaplus-ai-tools` and add
`tlaplus@tlaplus`. To update a Git installation, run
`codex plugin marketplace upgrade tlaplus`, then reinstall with
`codex plugin add tlaplus@tlaplus` and start a new task.

If previously installed from `tlaplus-local`, remove that old plugin using
`codex plugin remove tlaplus@tlaplus-local` before installing from the new
marketplace. Do not keep both enabled under the same MCP server name.

For setup failures, use `$tla-setup`. It checks Java, the installed runtime's
JARs, the MCP connection, and a known-good SANY parse. Missing dependency or
JAR setup fails startup with a diagnostic; fix the reported environment or
network issue and restart the MCP server. `TLAPLUS_NO_AUTO_INSTALL=1` disables
automatic setup when you want to provision the cached runtime yourself.
