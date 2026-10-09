#!/usr/bin/env python3
"""Merge imported TLA+ knowledge articles and refresh the published tools JARs."""

from __future__ import annotations

import argparse
import re
import subprocess
import tempfile
from pathlib import Path
from urllib.parse import urlparse


ROOT = Path(__file__).resolve().parent.parent
UPSTREAM = "https://github.com/tlaplus/vscode-tlaplus.git"
ARTICLES = "resources/knowledgebase"
REVISION = f"{ARTICLES}/.upstream-revision"


def git(root: Path, *args: str) -> bytes:
    return subprocess.check_output(["git", "-C", str(root), *args])


def format_doc(root: Path, name: str, content: bytes) -> bytes:
    formatter = root / "node_modules/oxfmt/bin/oxfmt"
    if not formatter.is_file():
        raise ValueError("Install development dependencies with npm ci before syncing docs")
    return subprocess.check_output(
        ["node", str(formatter), "--stdin-filepath", name], input=content, cwd=root,
    )


def snapshot(root: Path, revision: str) -> dict[str, bytes]:
    files = {}
    for record in git(root, "ls-tree", "-r", "-z", revision, f"{ARTICLES}/").split(b"\0"):
        if not record:
            continue
        metadata, raw_name = record.split(b"\t", 1)
        name = raw_name.decode("utf8")
        if not name.endswith(".md"):
            continue
        if metadata.split()[0] not in (b"100644", b"100755"):
            raise ValueError(f"Upstream article must be a regular file: {name}")
        if Path(name).parent.as_posix() != ARTICLES:
            raise ValueError(f"Unexpected upstream article path: {name}")
        files[name] = git(root, "show", f"{revision}:{name}")
    if not files:
        raise ValueError(f"No {ARTICLES} articles found in upstream revision {revision}")
    return files


def sync_docs(root: Path, upstream: str, ref: str, dry_run: bool) -> None:
    root = root.resolve()
    revision_file = root / REVISION
    if (root / ARTICLES).resolve() != root / ARTICLES or revision_file.is_symlink():
        raise ValueError("Knowledge directory and revision file must not be symlinks")
    base = revision_file.read_text().strip()
    if not re.fullmatch(r"[0-9a-f]{40}", base):
        raise ValueError(f"Invalid recorded upstream revision: {REVISION}")
    if not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9._/-]*", ref):
        raise ValueError("Upstream ref must be a branch, tag, or commit")
    if Path(upstream).is_dir():
        upstream = str(Path(upstream).resolve())
    elif urlparse(upstream).scheme != "https":
        raise ValueError("Upstream must be an HTTPS Git URL or a local clone directory")
    if not dry_run:
        dirty = git(root, "status", "--porcelain=v1", "-z", "-uall", "--", ARTICLES)
        # The supplied revision marker can be untracked on the first sync.
        if dirty not in (b"", f"?? {REVISION}\0".encode()):
            raise ValueError("Commit or resolve knowledge-base changes before applying a sync")

    with tempfile.TemporaryDirectory(prefix="tlaplus-upstream-") as folder:
        checkout = Path(folder)
        git(checkout, "init", "--quiet")
        git(checkout, "fetch", "--quiet", "--depth=1", "--no-tags", "--", upstream, ref)
        incoming_revision = git(checkout, "rev-parse", "FETCH_HEAD").decode().strip()
        print(f"Upstream: {base[:12]} -> {incoming_revision[:12]}")
        if base == incoming_revision:
            print("Knowledge articles are up to date; local adaptations retained", flush=True)
            return
        incoming = snapshot(checkout, incoming_revision)
        git(checkout, "fetch", "--quiet", "--depth=1", "--no-tags", "--", upstream, base)
        previous = snapshot(checkout, base)
        updates = {}
        conflicts = []
        for name in sorted(previous.keys() | incoming.keys()):
            old, new = previous.get(name), incoming.get(name)
            if old == new:
                continue
            target = root / name
            if target.is_symlink() or target.parent.resolve() != (root / ARTICLES).resolve():
                raise ValueError(f"Refusing to replace a symlink or unexpected path: {name}")
            local = target.read_bytes() if target.exists() else None
            if new is not None:
                new = format_doc(root, name, new)
            if old is not None:
                old = format_doc(root, name, old)
            if local == old or local == new:
                merged = new
            elif old is None or new is None or local is None:
                conflicts.append(name)
                continue
            else:
                for label, content in (("local", local), ("base", old), ("upstream", new)):
                    (checkout / label).write_bytes(content)
                result = subprocess.run(
                    ["git", "merge-file", "-p", "--diff3", "-L", name, "-L", base,
                     "-L", incoming_revision, "local", "base", "upstream"],
                    cwd=checkout, capture_output=True,
                )
                if result.returncode != 0:
                    if not 0 < result.returncode < 128:
                        raise RuntimeError(result.stderr.decode("utf8", errors="replace"))
                    print(result.stdout.decode("utf8", errors="replace"))
                    conflicts.append(name)
                    continue
                merged = result.stdout
            if merged != local:
                updates[name] = merged
                print(f"{'Delete' if merged is None else 'Update'}: {name}")
        if conflicts:
            raise ValueError("No docs or revision were written. Resolve conflicts and rerun: "
                             + ", ".join(conflicts))
        if dry_run:
            print(f"Preview: {len(updates)} article changes; revision would advance")
            return
        for name, content in updates.items():
            target = root / name
            if content is None:
                target.unlink()
            else:
                target.write_bytes(content)
        revision_file.write_text(incoming_revision + "\n")
        print(f"Synced {len(updates)} articles; local skills remain maintained here", flush=True)


def main(argv: list[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", default=UPSTREAM, help="HTTPS Git URL or local vscode-tlaplus clone")
    parser.add_argument("--ref", default="master", help="Upstream branch, tag, or commit")
    parser.add_argument("--dry-run", action="store_true", help="Preview docs; do not change docs or JARs")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--docs-only", action="store_true")
    mode.add_argument("--jars-only", action="store_true")
    args = parser.parse_args(argv)
    if not args.jars_only:
        sync_docs(ROOT, args.upstream, args.ref, args.dry_run)
    if not args.docs_only:
        if args.dry_run:
            print("Preview: would run scripts/setup.js to refresh and verify the pinned JAR releases")
        else:
            subprocess.run(["node", str(ROOT / "scripts/setup.js")], cwd=ROOT, check=True)


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, RuntimeError, subprocess.CalledProcessError) as error:
        raise SystemExit(f"Upstream sync failed: {error}")
