#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CODEX_HOME="${HOME}/.codex"
SKILLS_DIR="${CODEX_HOME}/skills"
LEGACY_AGENTS_DIR="${CODEX_HOME}/agents"
CONFIG_FILE="${CODEX_HOME}/config.toml"
TIMESTAMP="$(date +%Y%m%d-%H%M%S)"
BACKUP_ROOT="${CODEX_HOME}/backups/tlaplus-ai-tools/${TIMESTAMP}"

require_command() {
  local command_name="$1"
  if ! command -v "$command_name" >/dev/null 2>&1; then
    echo "Error: required command not found: ${command_name}" >&2
    exit 1
  fi
}

ensure_runtime() {
  echo "==> Checking local runtime"
  require_command node
  require_command npm
  require_command codex

  cd "$ROOT_DIR"

  if node -e 'require.resolve("@modelcontextprotocol/sdk"); require.resolve("express"); require.resolve("fast-xml-parser"); require.resolve("adm-zip"); require.resolve("zod"); require.resolve("tsx/cjs");' >/dev/null 2>&1; then
    echo "    npm dependencies already available"
  else
    echo "    Installing npm dependencies"
    npm install --no-audit --no-fund
  fi

  if [[ -f "${ROOT_DIR}/tools/tla2tools.jar" && -f "${ROOT_DIR}/tools/CommunityModules-deps.jar" ]]; then
    echo "    TLA+ tools already available"
  else
    echo "    Downloading TLA+ tools"
    npm run setup
  fi
}

backup_config_if_present() {
  if [[ -f "$CONFIG_FILE" ]]; then
    mkdir -p "$BACKUP_ROOT"
    cp "$CONFIG_FILE" "${BACKUP_ROOT}/config.toml.bak"
    echo "    Backed up Codex config to ${BACKUP_ROOT}/config.toml.bak"
  fi
}

register_mcp_server() {
  echo "==> Registering Codex MCP server"
  backup_config_if_present
  codex mcp add tlaplus \
    --env TLAPLUS_AUTO_INSTALL=1 \
    -- node "${ROOT_DIR}/scripts/start.js" >/dev/null
  echo "    Registered MCP server 'tlaplus'"
}

install_skills() {
  echo "==> Installing Codex skills"
  mkdir -p "$SKILLS_DIR"

  TLAPLUS_CODEX_ROOT="$ROOT_DIR" \
  TLAPLUS_CODEX_SKILLS_DIR="$SKILLS_DIR" \
  TLAPLUS_CODEX_BACKUP_ROOT="$BACKUP_ROOT" \
  node <<'NODE'
const fs = require('fs');
const path = require('path');

const repoRoot = process.env.TLAPLUS_CODEX_ROOT;
const skillsSrc = path.join(repoRoot, 'skills');
const skillsDst = process.env.TLAPLUS_CODEX_SKILLS_DIR;
const backupRoot = process.env.TLAPLUS_CODEX_BACKUP_ROOT;
const knowledgebaseRoot = path.join(repoRoot, 'resources', 'knowledgebase');

const oldPrefix = 'mcp__plugin_tlaplus_tlaplus__';
const newPrefix = 'mcp__tlaplus__';

function rewriteMarkdown(content) {
  return content
    .split(oldPrefix)
    .join(newPrefix)
    .replace(/resource:\/\/knowledgebase\/([A-Za-z0-9._-]+)/g, (_, name) =>
      path.join(knowledgebaseRoot, name)
    )
    .replace(/skill:\/\/([A-Za-z0-9._-]+)/g, (_, name) =>
      path.join(skillsDst, name, 'SKILL.md')
    )
    .replace(/\/plugin list/g, 'codex mcp list')
    .replace(/Restart Claude Code/g, 'Restart Codex');
}

function rewriteTree(dirPath, rewritten) {
  for (const entry of fs.readdirSync(dirPath, { withFileTypes: true })) {
    const fullPath = path.join(dirPath, entry.name);
    if (entry.isDirectory()) {
      rewriteTree(fullPath, rewritten);
      continue;
    }
    if (!entry.isFile() || !entry.name.endsWith('.md')) {
      continue;
    }

    const original = fs.readFileSync(fullPath, 'utf8');
    const updated = rewriteMarkdown(original);
    if (updated !== original) {
      fs.writeFileSync(fullPath, updated);
      rewritten.push(fullPath);
    }
  }
}

const installed = [];
const backedUp = [];
const rewritten = [];

for (const entry of fs.readdirSync(skillsSrc, { withFileTypes: true })) {
  if (!entry.isDirectory() || entry.name.startsWith('.')) {
    continue;
  }

  const srcDir = path.join(skillsSrc, entry.name);
  const dstDir = path.join(skillsDst, entry.name);

  if (fs.existsSync(dstDir)) {
    const backupDir = path.join(backupRoot, 'skills', entry.name);
    fs.mkdirSync(path.dirname(backupDir), { recursive: true });
    fs.cpSync(dstDir, backupDir, { recursive: true });
    fs.rmSync(dstDir, { recursive: true, force: true });
    backedUp.push(backupDir);
  }

  fs.cpSync(srcDir, dstDir, { recursive: true });
  rewriteTree(dstDir, rewritten);
  installed.push(dstDir);
}

console.log(`    Installed ${installed.length} skills into ${skillsDst}`);
if (backedUp.length > 0) {
  console.log(`    Backed up ${backedUp.length} existing skill directories to ${path.join(backupRoot, 'skills')}`);
}
if (rewritten.length > 0) {
  console.log(`    Rewrote Codex-specific references in ${rewritten.length} markdown files`);
}
NODE
}

cleanup_legacy_agents() {
  echo "==> Cleaning up legacy Codex agents"

  TLAPLUS_CODEX_LEGACY_AGENTS_DIR="$LEGACY_AGENTS_DIR" \
  TLAPLUS_CODEX_BACKUP_ROOT="$BACKUP_ROOT" \
  TLAPLUS_CODEX_CONFIG_FILE="$CONFIG_FILE" \
  node <<'NODE'
const fs = require('fs');
const path = require('path');

const agentsDir = process.env.TLAPLUS_CODEX_LEGACY_AGENTS_DIR;
const backupRoot = process.env.TLAPLUS_CODEX_BACKUP_ROOT;
const configFile = process.env.TLAPLUS_CODEX_CONFIG_FILE;

const legacyAgentFiles = [
  'trace-analyzer.toml',
  'animation-creator.toml',
];
const legacyAgentTables = [
  'agents."trace-analyzer"',
  'agents."animation-creator"',
];

function findTable(lines, tableName) {
  const pattern = new RegExp(`^\\s*\\[${tableName.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}\\]\\s*$`);
  return lines.findIndex(line => pattern.test(line));
}

function tableEnd(lines, startIndex) {
  for (let i = startIndex + 1; i < lines.length; i += 1) {
    if (/^\s*\[.*\]\s*$/.test(lines[i])) {
      return i;
    }
  }
  return lines.length;
}

function removeTable(lines, tableName) {
  let index = findTable(lines, tableName);
  if (index === -1) {
    return false;
  }

  let start = index;
  let end = tableEnd(lines, index);
  if (end < lines.length && lines[end].trim() === '') {
    end += 1;
  } else if (start > 0 && lines[start - 1].trim() === '') {
    start -= 1;
  }
  lines.splice(start, end - start);
  return true;
}

const backedUp = [];
const removedFiles = [];
const removedTables = [];

if (fs.existsSync(agentsDir)) {
  for (const fileName of legacyAgentFiles) {
    const source = path.join(agentsDir, fileName);
    if (!fs.existsSync(source)) {
      continue;
    }

    const backupFile = path.join(backupRoot, 'agents', fileName);
    fs.mkdirSync(path.dirname(backupFile), { recursive: true });
    fs.copyFileSync(source, backupFile);
    fs.rmSync(source, { force: true });
    backedUp.push(backupFile);
    removedFiles.push(source);
  }

  if (fs.readdirSync(agentsDir).length === 0) {
    fs.rmdirSync(agentsDir);
  }
}

if (fs.existsSync(configFile)) {
  const configLines = fs.readFileSync(configFile, 'utf8').split(/\r?\n/);
  let configChanged = false;
  for (const tableName of legacyAgentTables) {
    const removed = removeTable(configLines, tableName);
    configChanged = removed || configChanged;
    if (removed) {
      removedTables.push(tableName);
    }
  }

  if (configChanged) {
    fs.writeFileSync(configFile, `${configLines.join('\n').replace(/\n*$/, '\n')}`);
  }
}

if (removedFiles.length === 0 && removedTables.length === 0) {
  console.log('    No legacy agent configs found');
} else {
  if (removedFiles.length > 0) {
    console.log(`    Removed ${removedFiles.length} legacy agent config file(s)`);
  }
  if (backedUp.length > 0) {
    console.log(`    Backed up removed agent config file(s) to ${path.join(backupRoot, 'agents')}`);
  }
  if (removedTables.length > 0) {
    console.log(`    Removed legacy agent tables from config.toml: ${removedTables.join(', ')}`);
  }
}
NODE
}

print_summary() {
  echo
  echo "Codex install complete."
  echo "  Repo: ${ROOT_DIR}"
  echo "  MCP server: tlaplus -> node ${ROOT_DIR}/scripts/start.js"
  echo "  Skills: ${SKILLS_DIR}/tla-*"
  if [[ -d "$BACKUP_ROOT" ]]; then
    echo "  Backups: ${BACKUP_ROOT}"
  fi
  echo
  echo "Verify with:"
  echo "  codex mcp list"
  echo "  codex mcp get tlaplus"
}

ensure_runtime
register_mcp_server
install_skills
cleanup_legacy_agents
print_summary
