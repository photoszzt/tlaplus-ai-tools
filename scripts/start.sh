#!/usr/bin/env bash
set -e

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

if [ ! -d node_modules ]; then
  npm install --ignore-scripts 2>/dev/null
fi

exec npx tsx src/index.ts "$@"
