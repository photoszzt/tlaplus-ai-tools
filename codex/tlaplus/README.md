# Codex plugin source

Run `python3 scripts/build_codex_plugin.py` from the repository root to assemble the Codex plugin at `plugins/tlaplus`. The Codex skills and references live in this directory. The build adds the shared compiled MCP server, bundled TLA+ JARs, and knowledge base. It writes an MCP config using the absolute output path.

Build the TypeScript server with `pnpm run build` and download the TLA+ JARs with `pnpm run setup` first if those generated files are absent. Then run `python3 scripts/build_codex_plugin.py` from the repository root. That step installs and verifies runtime dependencies using pnpm; pass `--package-manager bun` to use Bun. The server never installs packages at startup. Dependencies are declared in `package.json` and tracked in the repository lockfiles. Node.js 18.14+, pnpm or Bun, and Java 11+ are required.

The repository marketplace at `.agents/plugins/marketplace.json` points to the assembled plugin. Register the repository with `codex plugin marketplace add <repo-root>`, then install `tlaplus@tlaplus-local`. After rebuilding an already installed plugin, refresh its cache version using the plugin-creator update helper and reinstall it from `tlaplus-local`. Start a new Codex task to load the updated skills and MCP tools.

For setup failures, run `$tla-setup` in a new task. It checks Java 11+, both bundled JARs, the MCP connection, and a known-good SANY parse. Claude Code's `/plugin list` and restart steps do not apply to Codex; use `codex plugin list --json` and start a new Codex task after installation or repair.
