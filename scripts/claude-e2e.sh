#!/bin/bash

set -euox pipefail

SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )

PROJ_DIR=$(realpath $SCRIPT_DIR/../)

COMMON_ARG="--model haiku --plugin-dir $(realpath $SCRIPT_DIR/../)"

claude $COMMON_ARG \
  --allowedTools "mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_sany_parse" \
  --print "/tla-parse @${PROJ_DIR}/test-specs/Counter.tla"

claude $COMMON_ARG \
  --allowedTools "mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_sany_parse,mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_sany_symbol" \
  --print "/tla-symbols @${PROJ_DIR}/test-specs/Counter.tla"


claude $COMMON_ARG \
  --allowedTools "mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_tlc_check" \
  --print "/tla-check @${PROJ_DIR}/test-specs/Counter.tla @${PROJ_DIR}/test-specs/Counter.cfg"

claude $COMMON_ARG \
  --allowedTools "mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_tlc_parse,mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_tlc_symbol,mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_tlc_smoke" \
  --print "/tla-review @${PROJ_DIR}/test-specs/Counter.tla"

claude $COMMON_ARG \
  --allowedTools "mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_tlc_sany_modules,mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_tlc_sany_parse" \
  --print "/tla-setup"

claude $COMMON_ARG \
  --allowedTools "mcp__plugin_tlaplus_tlaplus__tlaplus_mcp_tlc_smoke" \
  --print "/tla-smoke @${PROJ_DIR}/test-specs/Counter.tla"
