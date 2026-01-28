# Changelog

All notable changes to the TLA+ AI Tools plugin will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [1.0.0] - 2026-01-27

### Added
- Complete Claude Code and OpenCode plugin structure
- MCP server for TLA+ tools (SANY, TLC, knowledge base)
- Three foundational skills:
  - `tla-spec-review` - Specification review workflow
  - `tla-debug-violations` - Debug invariant/property violations
  - `tla-create-animations` - Create TLA+ animations
- Six slash commands:
  - `/tla-parse` - Parse and validate TLA+ specifications
  - `/tla-check` - Run model checking with TLC
  - `/tla-smoke` - Quick smoke test
  - `/tla-symbols` - Extract symbols for config generation
  - `/tla-review` - Comprehensive specification review
  - `/tla-setup` - Interactive setup and verification
- Four AI agents:
  - `spec-validator` - Automated specification validation
  - `config-generator` - Generate TLC configuration files
  - `animation-creator` - Create visualization animations
  - `trace-analyzer` - Analyze counterexample traces
- Three event hooks:
  - SessionStart - Verify TLA+ tools on startup
  - PreToolUse - Auto-parse TLA+ files before saving
  - PostToolUse - Suggest config generation
- Installation infrastructure:
  - Automatic TLA+ tools download via post-install
  - Verification script with auto-fix support
  - Cross-platform support (macOS, Linux, Windows)
- Comprehensive documentation and knowledge base
- Support for both Claude Code and OpenCode

### Changed
- Updated plugin metadata and author information
- Enhanced README with marketplace-first installation

### Technical Details
- MCP server with stdio and HTTP transport
- Auto-detection of Java and TLA+ tools
- Portable paths using ${CLAUDE_PLUGIN_ROOT}
- Comprehensive test suite with platform support

## [Unreleased]

### Planned
- Additional skills for TLA+ fundamentals and advanced topics
- Enhanced agents with more sophisticated analysis
- Marketplace icon and screenshots
- Video tutorials and documentation
- Community contributions and feedback integration

---

**Note**: This plugin is derived from and inspired by [vscode-tlaplus](https://github.com/tlaplus/vscode-tlaplus).
