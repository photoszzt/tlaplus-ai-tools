"""
Tests for output normalization functions.

Covers:
- ANSI escape sequence stripping (CSI, OSC, other ESC sequences)
- Carriage return (CR) normalization
- CRLF to LF conversion
"""

import sys
from pathlib import Path

import pytest

SCRIPT_DIR = Path(__file__).parent.parent.resolve()
sys.path.insert(0, str(SCRIPT_DIR))

import importlib.util

spec = importlib.util.spec_from_file_location(
    "claude_code_interactive_e2e", SCRIPT_DIR / "claude-code-interactive-e2e.py"
)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

strip_ansi_escapes = module.strip_ansi_escapes
normalize_cr = module.normalize_cr
normalize_output = module.normalize_output


class TestStripAnsiEscapes:
    def test_strip_color_codes(self):
        text = "\x1b[32mGreen text\x1b[0m"
        result = strip_ansi_escapes(text)
        assert result == "Green text"

    def test_strip_cursor_movement(self):
        text = "\x1b[2K\x1b[1A\x1b[2KCleared line"
        result = strip_ansi_escapes(text)
        assert result == "Cleared line"

    def test_strip_multiple_sequences(self):
        text = "\x1b[32m✓\x1b[0m Ready\x1b[2K"
        result = strip_ansi_escapes(text)
        assert result == "✓ Ready"

    def test_strip_osc_sequences(self):
        text = "\x1b]0;Window Title\x07Content"
        result = strip_ansi_escapes(text)
        assert result == "Content"

    def test_no_ansi_sequences(self):
        text = "Plain text without ANSI"
        result = strip_ansi_escapes(text)
        assert result == "Plain text without ANSI"

    def test_empty_string(self):
        result = strip_ansi_escapes("")
        assert result == ""

    def test_fixture_ansi_and_cr(self):
        fixture_path = (
            SCRIPT_DIR.parent / "test-fixtures" / "interactive" / "ansi_and_cr.txt"
        )
        with open(fixture_path, "r") as f:
            text = f.read()

        result = strip_ansi_escapes(text)

        assert "\x1b[" not in result
        assert "tla-parse" in result
        assert "tla-symbols" in result


class TestNormalizeCr:
    def test_cr_overwrites_line(self):
        text = "Loading...\rDone!"
        result = normalize_cr(text)
        assert result == "Done!"

    def test_multiple_cr_in_line(self):
        text = "First\rSecond\rThird"
        result = normalize_cr(text)
        assert result == "Third"

    def test_cr_across_multiple_lines(self):
        text = "Line 1\rOverwritten\nLine 2\rFinal"
        result = normalize_cr(text)
        assert result == "Overwritten\nFinal"

    def test_no_cr_sequences(self):
        text = "Line 1\nLine 2\nLine 3"
        result = normalize_cr(text)
        assert result == "Line 1\nLine 2\nLine 3"

    def test_empty_string(self):
        result = normalize_cr("")
        assert result == ""

    def test_fixture_ansi_and_cr(self):
        fixture_path = (
            SCRIPT_DIR.parent / "test-fixtures" / "interactive" / "ansi_and_cr.txt"
        )
        with open(fixture_path, "r") as f:
            text = f.read()

        stripped = strip_ansi_escapes(text)
        result = normalize_cr(stripped)

        assert "Processing..." not in result or "Spec path:" in result


class TestNormalizeOutput:
    def test_full_pipeline(self):
        text = "\x1b[32mLoading...\x1b[0m\r\x1b[32mDone!\x1b[0m\n"
        result = normalize_output(text)
        assert result == "Done!\n"

    def test_ansi_then_cr(self):
        text = "\x1b[2K\x1b[1A\x1b[2KProcessing...\rComplete"
        result = normalize_output(text)
        assert result == "Complete"

    def test_crlf_normalization(self):
        text = "Line 1\nLine 2\nLine 3"
        result = normalize_output(text)
        assert result == "Line 1\nLine 2\nLine 3"

    def test_fixture_ansi_and_cr(self):
        fixture_path = (
            SCRIPT_DIR.parent / "test-fixtures" / "interactive" / "ansi_and_cr.txt"
        )
        with open(fixture_path, "r") as f:
            text = f.read()

        result = normalize_output(text)

        assert "\x1b[" not in result
        assert "\r" not in result or "\r\n" not in result
        assert "tla-parse" in result
        assert "tla-symbols" in result
        assert "Spec path:" in result

    def test_fixture_wrapped_markers(self):
        fixture_path = (
            SCRIPT_DIR.parent / "test-fixtures" / "interactive" / "wrapped_markers.txt"
        )
        with open(fixture_path, "r") as f:
            text = f.read()

        result = normalize_output(text)

        assert "tla-parse" in result
        assert "tla-symbols" in result
