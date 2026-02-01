#!/usr/bin/env python3
"""
Interactive E2E test for Claude Code with TLA+ commands.

This script uses pexpect to automate an interactive Claude Code session,
testing /tla-parse and /tla-symbols commands with robust output capture.

Key features:
- Readiness gate via /help command
- Never drops partial output on TIMEOUT
- ANSI escape sequence and CR normalization
- Predictable PTY size to reduce line wrapping
- Explicit drain periods between commands
- Ordering sanity checks for marker sequences

Usage:
    CLAUDE_CODE_E2E=1 python3 claude-code-interactive-e2e.py

Environment variables:
    CLAUDE_CODE_E2E: Set to "1" to enable (opt-in only)
    READINESS_TIMEOUT: Timeout for /help readiness gate (default: 30s)
    COMMAND_TIMEOUT: Timeout for command execution (default: 60s)
"""

import os
import sys
import re
import time
import json
from datetime import datetime
from pathlib import Path

try:
    import pexpect
except ImportError:
    print(
        "ERROR: pexpect not installed. Install with: pip install pexpect",
        file=sys.stderr,
    )
    sys.exit(1)


# ============================================================================
# Configuration
# ============================================================================

SCRIPT_DIR = Path(__file__).parent.resolve()
PROJ_DIR = SCRIPT_DIR.parent
TEST_SPEC = PROJ_DIR / "test-specs" / "Counter.tla"
ARTIFACT_DIR = PROJ_DIR / "test-artifacts" / "interactive"

# Timeouts (seconds)
READINESS_TIMEOUT = int(os.getenv("READINESS_TIMEOUT", "30"))
COMMAND_TIMEOUT = int(os.getenv("COMMAND_TIMEOUT", "60"))
DRAIN_PERIOD = 0.5  # seconds to wait for output to settle

# PTY size (predictable dimensions to reduce wrapping)
PTY_ROWS = 40
PTY_COLS = 120


# ============================================================================
# Output Normalization Helpers
# ============================================================================


def strip_ansi_escapes(text: str) -> str:
    """
    Remove ANSI escape sequences from text.

    Handles:
    - Color codes: \\x1b[...m
    - Cursor movement: \\x1b[...H, \\x1b[...A, etc.
    - Other control sequences
    """
    # Remove ANSI CSI sequences (ESC [ ... letter)
    text = re.sub(r"\x1b\[[0-9;]*[a-zA-Z]", "", text)
    # Remove ANSI OSC sequences (ESC ] ... BEL/ST)
    text = re.sub(r"\x1b\][^\x07\x1b]*(?:\x07|\x1b\\)", "", text)
    # Remove other ESC sequences
    text = re.sub(r"\x1b[^[]", "", text)
    return text


def normalize_cr(text: str) -> str:
    """
    Normalize carriage return (CR) sequences.

    Converts CR-based line updates into stable text by:
    1. Splitting on CR
    2. Taking the last segment (final state after CR updates)
    3. Normalizing CRLF to LF
    """
    lines = []
    for line in text.split("\n"):
        # Handle CR within a line - take the last segment
        if "\r" in line:
            segments = line.split("\r")
            line = segments[-1]  # Last segment is the final state
        lines.append(line)
    return "\n".join(lines)


def normalize_output(text: str) -> str:
    """
    Full normalization pipeline for captured output.

    Steps:
    1. Strip ANSI escape sequences
    2. Normalize CR sequences
    3. Normalize CRLF to LF
    """
    text = strip_ansi_escapes(text)
    text = normalize_cr(text)
    text = text.replace("\r\n", "\n")
    return text


# ============================================================================
# Capture Logic
# ============================================================================


def capture_until_quiet(
    child, timeout: float, drain_period: float = DRAIN_PERIOD
) -> str:
    """
    Capture output until the child process is quiet for drain_period seconds.

    This function NEVER drops output:
    - Always appends child.before on TIMEOUT
    - Always appends child.after on pattern match
    - Continues until no new output for drain_period

    Args:
        child: pexpect spawn object
        timeout: Maximum total time to wait
        drain_period: How long to wait for silence

    Returns:
        Accumulated output (raw, not normalized)
    """
    accumulated = []
    start_time = time.time()
    last_output_time = start_time

    while True:
        elapsed = time.time() - start_time
        if elapsed >= timeout:
            break

        # Calculate remaining timeout
        remaining = timeout - elapsed
        wait_time = min(drain_period, remaining)

        try:
            # Try to match any output
            index = child.expect(
                [pexpect.TIMEOUT, pexpect.EOF, r".+"], timeout=wait_time
            )

            if index == 0:  # TIMEOUT
                # CRITICAL: Always append child.before on TIMEOUT
                if child.before:
                    accumulated.append(child.before)
                    last_output_time = time.time()

                # Check if we've been quiet long enough
                quiet_duration = time.time() - last_output_time
                if quiet_duration >= drain_period:
                    break

            elif index == 1:  # EOF
                # CRITICAL: Always append child.before on EOF
                if child.before:
                    accumulated.append(child.before)
                break

            else:  # Pattern matched (index == 2)
                # Append both before and after
                if child.before:
                    accumulated.append(child.before)
                if child.after:
                    accumulated.append(child.after)
                last_output_time = time.time()

        except pexpect.TIMEOUT:
            # Explicit timeout exception - still capture before
            if child.before:
                accumulated.append(child.before)
            break
        except pexpect.EOF:
            # Explicit EOF exception - still capture before
            if child.before:
                accumulated.append(child.before)
            break

    # Combine all accumulated output
    if isinstance(accumulated[0], bytes) if accumulated else False:
        return b"".join(accumulated).decode("utf-8", errors="replace")
    return "".join(accumulated)


def send_command_and_capture(
    child, command: str, timeout: float = COMMAND_TIMEOUT
) -> str:
    """
    Send a command and capture its output robustly.

    Steps:
    1. Send command with newline
    2. Brief pause to let command start
    3. Capture until quiet
    4. Drain any remaining output

    Args:
        child: pexpect spawn object
        command: Command to send (without newline)
        timeout: Maximum time to wait for output

    Returns:
        Captured output (raw, not normalized)
    """
    # Send command
    child.sendline(command)

    # Brief pause to let command start processing
    time.sleep(0.1)

    # Capture output
    output = capture_until_quiet(child, timeout)

    # Additional drain period to ensure clean state
    time.sleep(DRAIN_PERIOD)

    return output


# ============================================================================
# Test Logic
# ============================================================================


def check_readiness(child) -> tuple[bool, str]:
    """
    Check if Claude Code is ready by running /help and looking for both commands.

    Returns:
        (success, transcript) tuple
    """
    print("Checking readiness via /help...")

    output = send_command_and_capture(child, "/help", timeout=READINESS_TIMEOUT)
    normalized = normalize_output(output)

    # Check for both required commands
    has_parse = "tla-parse" in normalized
    has_symbols = "tla-symbols" in normalized

    if has_parse and has_symbols:
        print("✓ Readiness check passed: both tla-parse and tla-symbols found")
        return True, output
    else:
        print("✗ Readiness check failed:")
        if not has_parse:
            print("  - Missing: tla-parse")
        if not has_symbols:
            print("  - Missing: tla-symbols")
        return False, output


def test_tla_parse(child, spec_path: Path) -> tuple[bool, str]:
    """
    Test /tla-parse command.

    Expected markers:
    - "Spec path:"
    - "Counter.tla"

    Returns:
        (success, transcript) tuple
    """
    print(f"\nTesting /tla-parse @{spec_path}...")

    command = f"/tla-parse @{spec_path}"
    output = send_command_and_capture(child, command)
    normalized = normalize_output(output)

    # Check for expected markers
    has_spec_path = "Spec path:" in normalized
    has_counter = "Counter.tla" in normalized

    success = has_spec_path and has_counter

    if success:
        print("✓ /tla-parse test passed")
    else:
        print("✗ /tla-parse test failed:")
        if not has_spec_path:
            print("  - Missing marker: 'Spec path:'")
        if not has_counter:
            print("  - Missing marker: 'Counter.tla'")

    return success, output


def test_tla_symbols(child, spec_path: Path) -> tuple[bool, str]:
    """
    Test /tla-symbols command.

    Expected markers:
    - "Spec path:"
    - "CFG written:"

    Returns:
        (success, transcript) tuple
    """
    print(f"\nTesting /tla-symbols @{spec_path}...")

    command = f"/tla-symbols @{spec_path}"
    output = send_command_and_capture(child, command)
    normalized = normalize_output(output)

    # Check for expected markers
    has_spec_path = "Spec path:" in normalized
    has_cfg_written = "CFG written:" in normalized

    success = has_spec_path and has_cfg_written

    if success:
        print("✓ /tla-symbols test passed")
    else:
        print("✗ /tla-symbols test failed:")
        if not has_spec_path:
            print("  - Missing marker: 'Spec path:'")
        if not has_cfg_written:
            print("  - Missing marker: 'CFG written:'")

    return success, output


def check_marker_ordering(full_transcript: str) -> bool:
    """
    Sanity check: ensure /tla-parse markers appear before /tla-symbols markers.

    This helps detect desynchronization issues.

    Returns:
        True if ordering is correct, False otherwise
    """
    normalized = normalize_output(full_transcript)

    # Find positions of markers
    parse_marker_pos = normalized.find("/tla-parse")
    symbols_marker_pos = normalized.find("/tla-symbols")

    if parse_marker_pos == -1 or symbols_marker_pos == -1:
        # Can't check ordering if markers are missing
        return True

    if parse_marker_pos < symbols_marker_pos:
        print("✓ Marker ordering check passed")
        return True
    else:
        print("✗ Marker ordering check failed: /tla-symbols appears before /tla-parse")
        return False


def write_failure_artifacts(full_transcript: str, metadata: dict):
    """
    Write failure artifacts to test-artifacts/interactive/ directory.

    Creates three files:
    - {timestamp}_raw.txt: Raw transcript with ANSI/CR sequences
    - {timestamp}_normalized.txt: Normalized transcript
    - {timestamp}_metadata.json: Test metadata (timeouts, timestamps, etc.)

    Args:
        full_transcript: Raw transcript string
        metadata: Dictionary with test metadata
    """
    # Ensure artifact directory exists
    ARTIFACT_DIR.mkdir(parents=True, exist_ok=True)

    # Generate timestamp for filenames
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")

    # Write raw transcript
    raw_path = ARTIFACT_DIR / f"{timestamp}_raw.txt"
    with open(raw_path, "w", encoding="utf-8") as f:
        f.write(full_transcript)

    # Write normalized transcript
    normalized_path = ARTIFACT_DIR / f"{timestamp}_normalized.txt"
    with open(normalized_path, "w", encoding="utf-8") as f:
        f.write(normalize_output(full_transcript))

    # Write metadata
    metadata_path = ARTIFACT_DIR / f"{timestamp}_metadata.json"
    with open(metadata_path, "w", encoding="utf-8") as f:
        json.dump(metadata, f, indent=2)

    print(f"\n📁 Failure artifacts written:")
    print(f"   Raw: {raw_path}")
    print(f"   Normalized: {normalized_path}")
    print(f"   Metadata: {metadata_path}")


# ============================================================================
# Main
# ============================================================================


def main():
    """Main entry point for interactive E2E test."""

    # Check opt-in flag
    if os.getenv("CLAUDE_CODE_E2E") != "1":
        print("Interactive E2E test skipped (set CLAUDE_CODE_E2E=1 to enable)")
        return 0

    print("=" * 80)
    print("Claude Code Interactive E2E Test")
    print("=" * 80)
    print(f"Project dir: {PROJ_DIR}")
    print(f"Test spec: {TEST_SPEC}")
    print(f"Readiness timeout: {READINESS_TIMEOUT}s")
    print(f"Command timeout: {COMMAND_TIMEOUT}s")
    print("=" * 80)

    # Check that test spec exists
    if not TEST_SPEC.exists():
        print(f"ERROR: Test spec not found: {TEST_SPEC}", file=sys.stderr)
        return 1

    # Spawn Claude Code with predictable PTY size
    print("\nSpawning Claude Code...")
    start_time = datetime.now()

    try:
        child = pexpect.spawn(
            "claude",
            [
                "--model",
                "haiku",
                "--plugin-dir",
                str(PROJ_DIR),
                "--dangerously-skip-permissions",
            ],
            cwd=str(PROJ_DIR),
            dimensions=(PTY_ROWS, PTY_COLS),
            encoding="utf-8",
            codec_errors="replace",
        )
        child.delaybeforesend = (
            0.05  # Small delay before sending to reduce race conditions
        )

    except Exception as e:
        print(f"ERROR: Failed to spawn Claude Code: {e}", file=sys.stderr)
        return 1

    # Accumulate full transcript
    full_transcript = []

    # Metadata for failure artifacts
    metadata = {
        "start_time": start_time.isoformat(),
        "readiness_timeout": READINESS_TIMEOUT,
        "command_timeout": COMMAND_TIMEOUT,
        "pty_dimensions": {"rows": PTY_ROWS, "cols": PTY_COLS},
        "test_spec": str(TEST_SPEC),
    }

    try:
        # Wait for initial banner/startup
        print("Waiting for initial startup...")
        time.sleep(2)
        startup_output = capture_until_quiet(child, timeout=5)
        full_transcript.append(startup_output)

        # Readiness check
        ready, readiness_output = check_readiness(child)
        full_transcript.append(readiness_output)

        if not ready:
            print(
                "\nERROR: Readiness check failed. Claude Code may not be ready.",
                file=sys.stderr,
            )
            print("\nReadiness output (normalized):")
            print("-" * 80)
            print(normalize_output(readiness_output))
            print("-" * 80)

            # Write failure artifacts
            metadata["failure_stage"] = "readiness"
            metadata["end_time"] = datetime.now().isoformat()
            write_failure_artifacts("\n".join(full_transcript), metadata)
            return 1

        # Test /tla-parse
        parse_success, parse_output = test_tla_parse(child, TEST_SPEC)
        full_transcript.append(parse_output)

        # Test /tla-symbols
        symbols_success, symbols_output = test_tla_symbols(child, TEST_SPEC)
        full_transcript.append(symbols_output)

        # Check marker ordering
        full_transcript_str = "\n".join(full_transcript)
        ordering_ok = check_marker_ordering(full_transcript_str)

        # Final result
        print("\n" + "=" * 80)
        if parse_success and symbols_success and ordering_ok:
            print("✓ All tests passed!")
            return 0
        else:
            print("✗ Some tests failed")
            print("\nFull transcript (normalized):")
            print("-" * 80)
            print(normalize_output(full_transcript_str))
            print("-" * 80)

            # Write failure artifacts
            metadata["failure_stage"] = "test_execution"
            metadata["parse_success"] = parse_success
            metadata["symbols_success"] = symbols_success
            metadata["ordering_ok"] = ordering_ok
            metadata["end_time"] = datetime.now().isoformat()
            write_failure_artifacts(full_transcript_str, metadata)
            return 1

    except Exception as e:
        print(f"\nERROR: Test execution failed: {e}", file=sys.stderr)
        import traceback

        traceback.print_exc()

        # Write failure artifacts
        metadata["failure_stage"] = "exception"
        metadata["exception"] = str(e)
        metadata["end_time"] = datetime.now().isoformat()
        write_failure_artifacts("\n".join(full_transcript), metadata)
        return 1

    finally:
        # Clean shutdown
        try:
            child.sendline("/exit")
            child.expect(pexpect.EOF, timeout=5)
        except:
            pass
        child.close()


if __name__ == "__main__":
    sys.exit(main())
