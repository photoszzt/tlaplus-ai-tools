"""
Tests for capture logic that preserves TIMEOUT output.

Covers:
- Simulated capture sequence appends child.before buffers
- Never drops partial output on TIMEOUT
- Handles EOF gracefully
"""

import sys
from pathlib import Path

import pytest

SCRIPT_DIR = Path(__file__).parent.parent.resolve()
sys.path.insert(0, str(SCRIPT_DIR))


class MockChild:
    def __init__(self, outputs):
        self.outputs = outputs
        self.output_index = 0
        self.before = None
        self.after = None

    def expect(self, patterns, timeout):
        if self.output_index >= len(self.outputs):
            self.before = None
            self.after = None
            return 0

        output_type, content = self.outputs[self.output_index]
        self.output_index += 1

        if output_type == "timeout":
            self.before = content
            self.after = None
            return 0
        elif output_type == "eof":
            self.before = content
            self.after = None
            return 1
        elif output_type == "match":
            before_content, after_content = content
            self.before = before_content
            self.after = after_content
            return 2
        else:
            self.before = None
            self.after = None
            return 0


def simulate_capture(child, timeout):
    accumulated = []

    while True:
        try:
            index = child.expect([None, None, r".+"], timeout=timeout)

            if index == 0:
                if child.before:
                    accumulated.append(child.before)
                if child.output_index >= len(child.outputs):
                    break
            elif index == 1:
                if child.before:
                    accumulated.append(child.before)
                break
            else:
                if child.before:
                    accumulated.append(child.before)
                if child.after:
                    accumulated.append(child.after)
        except Exception:
            if child.before:
                accumulated.append(child.before)
            break

    return "".join(accumulated)


class TestCaptureLogic:
    def test_timeout_preserves_before(self):
        child = MockChild(
            [
                ("timeout", "Partial output"),
            ]
        )

        result = simulate_capture(child, timeout=1.0)

        assert result == "Partial output"

    def test_multiple_timeouts_accumulate(self):
        child = MockChild(
            [
                ("timeout", "First chunk"),
                ("timeout", "Second chunk"),
                ("timeout", "Third chunk"),
            ]
        )

        result = simulate_capture(child, timeout=1.0)

        assert result == "First chunkSecond chunkThird chunk"

    def test_eof_preserves_before(self):
        child = MockChild(
            [
                ("eof", "Final output"),
            ]
        )

        result = simulate_capture(child, timeout=1.0)

        assert result == "Final output"

    def test_match_includes_before_and_after(self):
        child = MockChild(
            [
                ("match", ("Before match", "After match")),
            ]
        )

        result = simulate_capture(child, timeout=1.0)

        assert result == "Before matchAfter match"

    def test_mixed_sequence(self):
        child = MockChild(
            [
                ("match", ("Start", ">")),
                ("timeout", " middle"),
                ("match", (" more", "!")),
                ("eof", " end"),
            ]
        )

        result = simulate_capture(child, timeout=1.0)

        assert result == "Start> middle more! end"

    def test_empty_before_not_appended(self):
        child = MockChild(
            [
                ("timeout", ""),
                ("match", ("Content", "!")),
            ]
        )

        result = simulate_capture(child, timeout=1.0)

        assert result == "Content!"

    def test_none_before_not_appended(self):
        child = MockChild(
            [
                ("timeout", None),
            ]
        )

        child.before = None
        result = simulate_capture(child, timeout=1.0)

        assert result == ""


class TestCaptureWithFixtures:
    def test_fixture_simulates_timeout_sequence(self):
        outputs = [
            ("match", ("/help\n", "")),
            ("timeout", "Available commands:\n"),
            ("match", ("  /tla-parse @<spec>\n", "")),
            ("match", ("  /tla-symbols @<spec>\n", "")),
            ("eof", "Ready\n"),
        ]

        child = MockChild(outputs)
        result = simulate_capture(child, timeout=1.0)

        assert "/help" in result
        assert "tla-parse" in result
        assert "tla-symbols" in result

    def test_fixture_simulates_ansi_sequence(self):
        outputs = [
            ("match", ("/tla-parse @test.tla\n", "")),
            ("timeout", "\x1b[2K\x1b[1A\x1b[2KProcessing...\r"),
            ("match", ("Spec path: test.tla\n", "")),
            ("eof", "Done\n"),
        ]

        child = MockChild(outputs)
        result = simulate_capture(child, timeout=1.0)

        assert "/tla-parse" in result
        assert "Spec path:" in result
