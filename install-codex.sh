#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CODEX_HOME="${HOME}/.codex"
SKILLS_DIR="${CODEX_HOME}/skills"
AGENTS_DIR="${CODEX_HOME}/agents"
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

install_agents() {
  echo "==> Installing Codex agents"
  mkdir -p "$AGENTS_DIR"

  TLAPLUS_CODEX_ROOT="$ROOT_DIR" \
  TLAPLUS_CODEX_AGENTS_DIR="$AGENTS_DIR" \
  TLAPLUS_CODEX_BACKUP_ROOT="$BACKUP_ROOT" \
  TLAPLUS_CODEX_CONFIG_FILE="$CONFIG_FILE" \
  node <<'NODE'
const fs = require('fs');
const path = require('path');

const repoRoot = process.env.TLAPLUS_CODEX_ROOT;
const agentsDir = process.env.TLAPLUS_CODEX_AGENTS_DIR;
const backupRoot = process.env.TLAPLUS_CODEX_BACKUP_ROOT;
const configFile = process.env.TLAPLUS_CODEX_CONFIG_FILE;

const agentSpecs = [
  {
    name: 'trace-analyzer',
    source: path.join(repoRoot, 'agents', 'trace-analyzer.md'),
    configFile: 'agents/trace-analyzer.toml',
  },
  {
    name: 'animation-creator',
    source: path.join(repoRoot, 'agents', 'animation-creator.md'),
    configFile: 'agents/animation-creator.toml',
  },
];

function parseAgentMarkdown(markdown) {
  let body = markdown;
  let description = '';
  const frontmatterMatch = markdown.match(/^---\n([\s\S]*?)\n---\n?/);
  if (frontmatterMatch) {
    body = markdown.slice(frontmatterMatch[0].length);
    const descriptionMatch = frontmatterMatch[1].match(/^description:\s*(.+)$/m);
    if (descriptionMatch) {
      description = descriptionMatch[1].trim().replace(/^["']|["']$/g, '');
    }
  }
  return { body: body.trimStart(), description };
}

function tomlMultilineString(value) {
  if (!value.includes("'''")) {
    return `'''\n${value}\n'''`;
  }
  return `"""\n${value.replace(/\\/g, '\\\\').replace(/"/g, '\\"')}\n"""`;
}

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

function setTableKey(lines, tableName, key, valueLine) {
  let changed = false;
  let index = findTable(lines, tableName);
  if (index === -1) {
    if (lines.length > 0 && lines[lines.length - 1].trim() !== '') {
      lines.push('');
    }
    lines.push(`[${tableName}]`);
    lines.push(valueLine);
    return true;
  }

  const end = tableEnd(lines, index);
  const pattern = new RegExp(`^\\s*${key.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}\\s*=`);
  for (let i = index + 1; i < end; i += 1) {
    if (pattern.test(lines[i])) {
      if (lines[i] !== valueLine) {
        lines[i] = valueLine;
        changed = true;
      }
      return changed;
    }
  }

  lines.splice(end, 0, valueLine);
  return true;
}

const installed = [];
const backedUp = [];
const configured = [];

let configLines = fs.existsSync(configFile)
  ? fs.readFileSync(configFile, 'utf8').split(/\r?\n/)
  : [];
let configChanged = false;

configChanged = setTableKey(
  configLines,
  'features',
  'multi_agent',
  'multi_agent = true'
) || configChanged;

for (const spec of agentSpecs) {
  if (!fs.existsSync(spec.source)) {
    continue;
  }

  const markdown = fs.readFileSync(spec.source, 'utf8');
  const parsed = parseAgentMarkdown(markdown);
  const destination = path.join(agentsDir, path.basename(spec.configFile));

  if (fs.existsSync(destination)) {
    const backupFile = path.join(backupRoot, 'agents', path.basename(spec.configFile));
    fs.mkdirSync(path.dirname(backupFile), { recursive: true });
    fs.copyFileSync(destination, backupFile);
    backedUp.push(backupFile);
  }

  const agentConfig = [
    'model = "gpt-5.4"',
    'model_reasoning_effort = "medium"',
    `developer_instructions = ${tomlMultilineString(parsed.body)}`,
    '',
  ].join('\n');
  fs.writeFileSync(destination, agentConfig);
  installed.push(destination);

  const tableName = `agents."${spec.name}"`;
  configChanged = setTableKey(
    configLines,
    tableName,
    'description',
    `description = "${parsed.description || spec.name}"`
  ) || configChanged;
  configChanged = setTableKey(
    configLines,
    tableName,
    'config_file',
    `config_file = "${spec.configFile}"`
  ) || configChanged;
  configured.push(spec.name);
}

if (configChanged) {
  fs.writeFileSync(configFile, `${configLines.join('\n').replace(/\n*$/, '\n')}`);
}

console.log(`    Installed ${installed.length} agent configs into ${agentsDir}`);
if (backedUp.length > 0) {
  console.log(`    Backed up ${backedUp.length} existing agent configs to ${path.join(backupRoot, 'agents')}`);
}
if (configured.length > 0) {
  console.log(`    Registered agent tables: ${configured.join(', ')}`);
}
NODE
}

print_summary() {
  echo
  echo "Codex install complete."
  echo "  Repo: ${ROOT_DIR}"
  echo "  MCP server: tlaplus -> node ${ROOT_DIR}/scripts/start.js"
  echo "  Skills: ${SKILLS_DIR}/tla-*"
  echo "  Agents: ${AGENTS_DIR}/trace-analyzer.toml, ${AGENTS_DIR}/animation-creator.toml"
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
install_agents
print_summary
