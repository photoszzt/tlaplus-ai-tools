# Interactive E2E Test Fixtures

This directory contains versioned transcript fixtures for unit testing the interactive E2E test script.

## Fixtures

### `banner_only.txt`
**Purpose**: Reproduces the "missing marker" bug where only the banner is captured.

**Characteristics**:
- Contains only startup banner
- No `/help` output
- No command markers
- Simulates readiness check failure

**Expected behavior**: Readiness check should fail (missing `tla-parse` and `tla-symbols`)

---

### `ansi_and_cr.txt`
**Purpose**: Tests ANSI escape sequence and carriage return normalization.

**Characteristics**:
- Contains ANSI color codes: `[32m`, `[0m`
- Contains cursor movement: `[2K`, `[1A`
- Contains carriage return sequences for progress indicators
- Includes all expected markers after normalization

**Expected behavior**: 
- After normalization, all markers should be found
- Progress indicators should be cleaned up
- Color codes should be stripped

---

### `wrapped_markers.txt`
**Purpose**: Tests marker detection when lines are wrapped due to narrow PTY width.

**Characteristics**:
- Markers split across lines (e.g., "spe\ncification")
- Simulates narrow terminal width
- Tests robustness of marker matching

**Expected behavior**:
- Marker detection should handle wrapped text
- May require fuzzy matching or line joining
- Current implementation may fail (documents known limitation)

---

## Usage

These fixtures can be used for:

1. **Unit tests**: Test normalization functions in isolation
2. **Regression tests**: Ensure fixes don't break existing behavior
3. **Documentation**: Show examples of real-world output patterns
4. **Debugging**: Compare against actual failures

## Adding New Fixtures

When adding new fixtures:

1. Use descriptive filenames (e.g., `unicode_characters.txt`)
2. Document the purpose and characteristics in this README
3. Include expected behavior
4. Keep fixtures minimal but representative
