#!/bin/bash

set -euox pipefail

SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )

PROJ_DIR=$(realpath $SCRIPT_DIR/../)

COMMON_ARG="run --model $MODEL"

opencode $COMMON_ARG tla-parse ${PROJ_DIR}/test-specs/Counter.tla

opencode $COMMON_ARG tla-symbols ${PROJ_DIR}/test-specs/Counter.tla

opencode $COMMON_ARG tla-check ${PROJ_DIR}/test-specs/Counter.tla ${PROJ_DIR}/test-specs/Counter.cfg

opencode $COMMON_ARG tla-review ${PROJ_DIR}/test-specs/Counter.tla

opencode $COMMON_ARG tla-smoke ${PROJ_DIR}/test-specs/Counter.tla

opencode $COMMON_ARG tla-setup
