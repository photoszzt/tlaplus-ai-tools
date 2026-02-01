"""
Tests for marker detection logic.

Covers:
- Readiness gate: requires BOTH tla-parse and tla-symbols
- /tla-parse completion: requires Spec path: and Counter.tla
- /tla-symbols completion: requires Spec path: and CFG written:
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

normalize_output = module.normalize_output
check_marker_ordering = module.check_marker_ordering


class TestReadinessMarkers:
    def test_both_commands_present(self):
        output = """
        Available commands:
          /tla-parse @<spec>  - Parse TLA+ specification
          /tla-symbols @<spec> - Extract symbols from specification
          /exit - Exit Claude Code
        """
        normalized = normalize_output(output)

        has_parse = "tla-parse" in normalized
        has_symbols = "tla-symbols" in normalized

        assert has_parse
        assert has_symbols

    def test_missing_tla_parse(self):
        output = """
        Available commands:
          /tla-symbols @<spec> - Extract symbols from specification
          /exit - Exit Claude Code
        """
        normalized = normalize_output(output)

        has_parse = "tla-parse" in normalized
        has_symbols = "tla-symbols" in normalized

        assert not has_parse
        assert has_symbols

    def test_missing_tla_symbols(self):
        output = """
        Available commands:
          /tla-parse @<spec>  - Parse TLA+ specification
          /exit - Exit Claude Code
        """
        normalized = normalize_output(output)

        has_parse = "tla-parse" in normalized
        has_symbols = "tla-symbols" in normalized

        assert has_parse
        assert not has_symbols

    def test_fixture_banner_only(self):
        fixture_path = (
            SCRIPT_DIR.parent / "test-fixtures" / "interactive" / "banner_only.txt"
        )
        with open(fixture_path, "r") as f:
            text = f.read()

        normalized = normalize_output(text)

        has_parse = "tla-parse" in normalized
        has_symbols = "tla-symbols" in normalized

        assert not has_parse
        assert not has_symbols

    def test_fixture_ansi_and_cr(self):
        fixture_path = (
            SCRIPT_DIR.parent / "test-fixtures" / "interactive" / "ansi_and_cr.txt"
        )
        with open(fixture_path, "r") as f:
            text = f.read()

        normalized = normalize_output(text)

        has_parse = "tla-parse" in normalized
        has_symbols = "tla-symbols" in normalized

        assert has_parse
        assert has_symbols


class TestTlaParseMarkers:
    def test_both_markers_present(self):
        output = """
        /tla-parse @test-specs/Counter.tla
        Spec path: test-specs/Counter.tla
        Parsed successfully
        """
        normalized = normalize_output(output)

        has_spec_path = "Spec path:" in normalized
        has_counter = "Counter.tla" in normalized

        assert has_spec_path
        assert has_counter

    def test_missing_spec_path(self):
        output = """
        /tla-parse @test-specs/Counter.tla
        Counter.tla
        Parsed successfully
        """
        normalized = normalize_output(output)

        has_spec_path = "Spec path:" in normalized
        has_counter = "Counter.tla" in normalized

        assert not has_spec_path
        assert has_counter

    def test_missing_counter_tla(self):
        output = """
        /tla-parse @test-specs/Example.tla
        Spec path: test-specs/Example.tla
        Parsed successfully
        """
        normalized = normalize_output(output)

        has_spec_path = "Spec path:" in normalized
        has_counter = "Counter.tla" in normalized

        assert has_spec_path
        assert not has_counter

    def test_fixture_ansi_and_cr(self):
        fixture_path = (
            SCRIPT_DIR.parent / "test-fixtures" / "interactive" / "ansi_and_cr.txt"
        )
        with open(fixture_path, "r") as f:
            text = f.read()

        normalized = normalize_output(text)

        has_spec_path = "Spec path:" in normalized
        has_counter = "Counter.tla" in normalized

        assert has_spec_path
        assert has_counter


class TestTlaSymbolsMarkers:
    def test_both_markers_present(self):
        output = """
        /tla-symbols @test-specs/Counter.tla
        Spec path: test-specs/Counter.tla
        CFG written: test-specs/Counter.generated.cfg
        """
        normalized = normalize_output(output)

        has_spec_path = "Spec path:" in normalized
        has_cfg_written = "CFG written:" in normalized

        assert has_spec_path
        assert has_cfg_written

    def test_missing_spec_path(self):
        output = """
        /tla-symbols @test-specs/Counter.tla
        CFG written: test-specs/Counter.generated.cfg
        """
        normalized = normalize_output(output)

        has_spec_path = "Spec path:" in normalized
        has_cfg_written = "CFG written:" in normalized

        assert not has_spec_path
        assert has_cfg_written

    def test_missing_cfg_written(self):
        output = """
        /tla-symbols @test-specs/Counter.tla
        Spec path: test-specs/Counter.tla
        Symbols extracted successfully
        """
        normalized = normalize_output(output)

        has_spec_path = "Spec path:" in normalized
        has_cfg_written = "CFG written:" in normalized

        assert has_spec_path
        assert not has_cfg_written

    def test_fixture_ansi_and_cr(self):
        fixture_path = (
            SCRIPT_DIR.parent / "test-fixtures" / "interactive" / "ansi_and_cr.txt"
        )
        with open(fixture_path, "r") as f:
            text = f.read()

        normalized = normalize_output(text)

        has_spec_path = "Spec path:" in normalized
        has_cfg_written = "CFG written:" in normalized

        assert has_spec_path
        assert has_cfg_written


class TestMarkerOrdering:
    def test_correct_ordering(self):
        transcript = """
        /tla-parse @test-specs/Counter.tla
        Spec path: test-specs/Counter.tla
        
        /tla-symbols @test-specs/Counter.tla
        Spec path: test-specs/Counter.tla
        """

        result = check_marker_ordering(transcript)
        assert result is True

    def test_incorrect_ordering(self):
        transcript = """
        /tla-symbols @test-specs/Counter.tla
        Spec path: test-specs/Counter.tla
        
        /tla-parse @test-specs/Counter.tla
        Spec path: test-specs/Counter.tla
        """

        result = check_marker_ordering(transcript)
        assert result is False

    def test_missing_markers(self):
        transcript = """
        Some output without markers
        """

        result = check_marker_ordering(transcript)
        assert result is True

    def test_fixture_ansi_and_cr(self):
        fixture_path = (
            SCRIPT_DIR.parent / "test-fixtures" / "interactive" / "ansi_and_cr.txt"
        )
        with open(fixture_path, "r") as f:
            text = f.read()

        result = check_marker_ordering(text)
        assert result is True
