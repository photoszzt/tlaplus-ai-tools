#!/usr/bin/env python3
"""Assemble the Codex plugin from its checked-in sources and shared MCP server."""

from __future__ import annotations

import argparse
import json
import shutil
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
SOURCE = ROOT / "codex" / "tlaplus"


def build(output: Path, package_manager: str) -> None:
    output = output.expanduser().resolve()
    if output in (ROOT, ROOT / "skills", ROOT / "dist", ROOT / "resources"):
        raise ValueError("Output must not replace repository sources")

    required = [
        ROOT / "dist" / "index.js",
        ROOT / "tools" / "tla2tools.jar",
        ROOT / "tools" / "CommunityModules-deps.jar",
    ]
    missing = [path for path in required if not path.is_file()]
    if missing:
        raise FileNotFoundError(
            "Missing build inputs: " + ", ".join(str(path) for path in missing)
            + ". Build the server and download the TLA+ tools before assembling the plugin."
        )

    output.mkdir(parents=True, exist_ok=True)
    (output / ".codex-plugin").mkdir(exist_ok=True)
    shutil.copy2(SOURCE / ".codex-plugin" / "plugin.json", output / ".codex-plugin" / "plugin.json")
    shutil.copy2(SOURCE / "README.md", output / "README.md")

    for folder in ("dist", "resources"):
        shutil.copytree(ROOT / folder, output / folder, dirs_exist_ok=True)
    (output / "tools").mkdir(exist_ok=True)
    for jar in (ROOT / "tools").glob("*.jar"):
        shutil.copy2(jar, output / "tools" / jar.name)
    (output / "scripts").mkdir(exist_ok=True)
    shutil.copy2(SOURCE / "scripts" / "start.js", output / "scripts" / "start.js")

    shutil.copytree(SOURCE / "skills", output / "skills", dirs_exist_ok=True)
    shutil.copytree(SOURCE / "shared", output / "shared", dirs_exist_ok=True)

    original_package = json.loads((ROOT / "package.json").read_text())
    package = {
        key: original_package[key]
        for key in (
            "name", "version", "description", "license", "engines",
            "dependencies", "optionalDependencies",
        )
        if key in original_package
    }
    package["description"] = "TLA+ formal specification and model checking tools for Codex"
    (output / "package.json").write_text(json.dumps(package, indent=2) + "\n")
    mcp = {
        "mcpServers": {
            "tlaplus": {
                "command": "node",
                "args": [str(output / "scripts" / "start.js")],
                "cwd": str(output),
                "startup_timeout_sec": 180,
                "tool_timeout_sec": 3600,
            }
        }
    }
    (output / ".mcp.json").write_text(json.dumps(mcp, indent=2) + "\n")
    # Codex copies the plugin into its cache without preserving pnpm symlinks.
    # A hoisted install gives the cached copy real package directories.
    node_modules = output / "node_modules"
    if node_modules.is_symlink():
        node_modules.unlink()
    elif node_modules.exists():
        shutil.rmtree(node_modules)
    command = (
        ["pnpm", "install", "--prod", "--ignore-scripts", "--config.node-linker=hoisted"]
        if package_manager == "pnpm"
        else ["bun", "install", "--production", "--ignore-scripts"]
    )
    subprocess.run(command, cwd=output, check=True)
    subprocess.run(
        [
            "node", "-e",
            "for (const name of ['@modelcontextprotocol/sdk/server/index.js', 'adm-zip', 'express', 'fast-xml-parser', 'zod']) require.resolve(name)",
        ],
        cwd=output,
        check=True,
    )
    print(f"Built Codex plugin: {output}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "plugins" / "tlaplus")
    parser.add_argument("--package-manager", choices=("pnpm", "bun"), default="pnpm")
    args = parser.parse_args()
    build(args.output, args.package_manager)
