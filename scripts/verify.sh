#!/bin/bash

# Verification script for tlaplus-ai-tools installation
# Usage: ./scripts/verify.sh [--fix]

set -e

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

FIX_MODE=false
if [[ "$1" == "--fix" ]]; then
  FIX_MODE=true
fi

echo "TLA+ AI Tools - Installation Verification"
echo "=========================================="
echo ""

# Determine plugin root
if [[ -n "$CLAUDE_PLUGIN_ROOT" ]]; then
  PLUGIN_ROOT="$CLAUDE_PLUGIN_ROOT"
else
  PLUGIN_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
fi

echo "Plugin root: $PLUGIN_ROOT"
echo ""

ERRORS=0
WARNINGS=0

# Check 1: Java installation
echo -n "Checking Java installation... "
if command -v java &> /dev/null; then
  JAVA_VERSION=$(java -version 2>&1 | head -n 1 | cut -d'"' -f2 | cut -d'.' -f1)
  if [[ "$JAVA_VERSION" -ge 11 ]]; then
    echo -e "${GREEN}✓${NC} Java $JAVA_VERSION found"
  else
    echo -e "${RED}✗${NC} Java version too old (found $JAVA_VERSION, need 11+)"
    ERRORS=$((ERRORS + 1))
  fi
else
  echo -e "${RED}✗${NC} Java not found"
  echo "  Install Java 11 or higher: https://adoptium.net/"
  ERRORS=$((ERRORS + 1))
fi

# Check 2: Node.js version
echo -n "Checking Node.js version... "
NODE_VERSION=$(node -v | cut -d'v' -f2 | cut -d'.' -f1)
if [[ "$NODE_VERSION" -ge 18 ]]; then
  echo -e "${GREEN}✓${NC} Node.js v$NODE_VERSION"
else
  echo -e "${YELLOW}⚠${NC} Node.js version $NODE_VERSION (recommend 18+)"
  WARNINGS=$((WARNINGS + 1))
fi

# Check 3: TLA+ tools
echo -n "Checking TLA+ tools... "
TOOLS_DIR="$PLUGIN_ROOT/tools"
TLA_TOOLS="$TOOLS_DIR/tla2tools.jar"
COMMUNITY_MODULES="$TOOLS_DIR/CommunityModules-deps.jar"

if [[ -f "$TLA_TOOLS" && -f "$COMMUNITY_MODULES" ]]; then
  echo -e "${GREEN}✓${NC} TLA+ tools found"
else
  echo -e "${RED}✗${NC} TLA+ tools missing"
  ERRORS=$((ERRORS + 1))

  if [[ "$FIX_MODE" == true ]]; then
    echo "  Downloading TLA+ tools..."
    cd "$PLUGIN_ROOT"
    npm run setup
    if [[ $? -eq 0 ]]; then
      echo -e "  ${GREEN}✓${NC} TLA+ tools downloaded"
      ERRORS=$((ERRORS - 1))
    else
      echo -e "  ${RED}✗${NC} Failed to download tools"
    fi
  else
    echo "  Run: npm run setup"
    echo "  Or: ./scripts/verify.sh --fix"
  fi
fi

# Check 4: Plugin structure
echo -n "Checking plugin structure... "
REQUIRED_DIRS=("skills" "commands" "agents" "hooks" "dist" ".claude-plugin")
MISSING_DIRS=()

for dir in "${REQUIRED_DIRS[@]}"; do
  if [[ ! -d "$PLUGIN_ROOT/$dir" ]]; then
    MISSING_DIRS+=("$dir")
  fi
done

if [[ ${#MISSING_DIRS[@]} -eq 0 ]]; then
  echo -e "${GREEN}✓${NC} All directories present"
else
  echo -e "${YELLOW}⚠${NC} Missing directories: ${MISSING_DIRS[*]}"
  WARNINGS=$((WARNINGS + 1))
fi

# Check 5: Manifest file
echo -n "Checking plugin manifest... "
MANIFEST="$PLUGIN_ROOT/.claude-plugin/plugin.json"
if [[ -f "$MANIFEST" ]]; then
  echo -e "${GREEN}✓${NC} plugin.json found"
else
  echo -e "${RED}✗${NC} plugin.json missing"
  ERRORS=$((ERRORS + 1))
fi

# Check 6: Built files
echo -n "Checking compiled files... "
if [[ -f "$PLUGIN_ROOT/dist/index.js" ]]; then
  echo -e "${GREEN}✓${NC} MCP server compiled"
else
  echo -e "${YELLOW}⚠${NC} MCP server not compiled"
  WARNINGS=$((WARNINGS + 1))
  echo "  Run: npm run build"
fi

# Check 7: Commands directory
echo -n "Checking commands... "
COMMAND_COUNT=$(find "$PLUGIN_ROOT/commands" -name "tla-*.md" 2>/dev/null | wc -l)
if [[ $COMMAND_COUNT -ge 6 ]]; then
  echo -e "${GREEN}✓${NC} $COMMAND_COUNT commands found"
else
  echo -e "${YELLOW}⚠${NC} Only $COMMAND_COUNT commands found (expected 6)"
  WARNINGS=$((WARNINGS + 1))
fi

# Summary
echo ""
echo "=========================================="
if [[ $ERRORS -eq 0 && $WARNINGS -eq 0 ]]; then
  echo -e "${GREEN}✓ All checks passed!${NC}"
  echo "Plugin is ready to use."
  exit 0
elif [[ $ERRORS -eq 0 ]]; then
  echo -e "${YELLOW}⚠ $WARNINGS warning(s)${NC}"
  echo "Plugin should work but has minor issues."
  exit 0
else
  echo -e "${RED}✗ $ERRORS error(s), $WARNINGS warning(s)${NC}"
  echo "Please fix errors before using the plugin."
  if [[ "$FIX_MODE" != true ]]; then
    echo ""
    echo "Run with --fix to automatically fix some issues:"
    echo "  ./scripts/verify.sh --fix"
  fi
  exit 1
fi
