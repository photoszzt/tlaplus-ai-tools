# Claude Code E2E Testing

## Overview

The Claude Code E2E test validates that TLA+ commands and skills work correctly in the Claude Code environment. We use two complementary approaches:

1.  **Non-interactive Skill E2E**: Uses Claude Code's `--print` flag to run skills non-interactively.
2.  **Interactive Command E2E**: Uses `pexpect` to automate an interactive Claude Code session, testing actual commands (`/tla-parse`, etc.) which are not available in `--print` mode.

## Interactive Command E2E

This test uses `pexpect` to simulate a real user interacting with Claude Code. It is the most robust way to verify command integration.

### How It Works

The script `tlaplus-ai-tools/scripts/claude-code-interactive-e2e.py` performs the following steps:

1.  **Spawns Claude Code**: Starts an interactive session with a predictable PTY size (120x40) to prevent line wrapping.
2.  **Readiness Gate**: Sends `/help` and waits for both `tla-parse` and `tla-symbols` to appear in the output. This ensures the plugin is fully loaded.
3.  **Command Execution**: Sends commands like `/tla-parse @test-specs/Counter.tla`.
4.  **Robust Capture**: Uses a "capture until quiet" loop that never drops partial output on timeouts.
5.  **Normalization**: Strips ANSI escape sequences and normalizes carriage returns (`\r`) before asserting on markers.
6.  **Marker Assertion**: Verifies expected output markers (e.g., `Spec path:`, `CFG written:`).
7.  **Artifact Generation**: On failure, it saves raw transcripts, normalized transcripts, and metadata to `test-artifacts/interactive/`.

### Running Locally

To run the interactive E2E tests, you must opt-in via an environment variable:

```bash
# Install dependencies
python3 -m pip install -r tlaplus-ai-tools/requirements-dev.txt

# Run the test
CLAUDE_CODE_E2E=1 python3 tlaplus-ai-tools/scripts/claude-code-interactive-e2e.py
```

### Configuration

- `CLAUDE_CODE_E2E`: Set to `1` to enable.
- `READINESS_TIMEOUT`: Seconds to wait for `/help` (default: 30).
- `COMMAND_TIMEOUT`: Seconds to wait for command output (default: 60).

## Non-interactive Skill E2E

The script `scripts/claude-code-skill-e2e.mjs` uses Claude Code's `--print` flag:

```bash
claude --print --plugin-dir $(pwd) "/tla-getting-started"
```

Note: Commands (like `/tla-parse`) are **not** supported in `--print` mode and will fail with "Unknown skill". Use the Interactive E2E for commands.

## Test Cases (Interactive)

| Command | Prompt | Expected Markers |
|---------|--------|------------------|
| `/tla-parse` | `/tla-parse @test-specs/Counter.tla` | `Spec path:`, `Counter.tla` |
| `/tla-symbols` | `/tla-symbols @test-specs/Counter.tla` | `Spec path:`, `CFG written:` |

## Troubleshooting & Artifacts

If a test fails, check `tlaplus-ai-tools/test-artifacts/interactive/`:
- `*_raw.txt`: Exact terminal output (with ANSI codes).
- `*_normalized.txt`: Cleaned text for easier reading.
- `*_metadata.json`: Details about the failure stage and timeouts.

