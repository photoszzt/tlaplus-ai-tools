#!/usr/bin/env python3
"""Offline integration check for upstream sync using disposable Git repositories."""

import importlib.util
import subprocess
import tempfile
from pathlib import Path
from unittest.mock import patch


spec = importlib.util.spec_from_file_location("sync_upstream", Path(__file__).with_name("sync_upstream.py"))
sync = importlib.util.module_from_spec(spec)
spec.loader.exec_module(sync)


def git(root, *args):
    return subprocess.check_output(["git", "-C", str(root), *args]).decode().strip()


def commit(root):
    git(root, "add", ".")
    git(root, "commit", "--quiet", "-m", "fixture")
    return git(root, "rev-parse", "HEAD")


def check():
    with tempfile.TemporaryDirectory(prefix="test-upstream-sync-") as folder:
        root = Path(folder)
        upstream, local = root / "upstream", root / "local"
        for repo in (upstream, local):
            repo.mkdir()
            git(repo, "init", "--quiet")
            git(repo, "config", "user.name", "Sync Test")
            git(repo, "config", "user.email", "sync@example.invalid")
            git(repo, "config", "commit.gpgsign", "false")
            git(repo, "config", "core.autocrlf", "input")
            hooks = repo / ".git" / "empty-hooks"
            hooks.mkdir()
            git(repo, "config", "core.hooksPath", str(hooks))
            (repo / sync.ARTICLES).mkdir(parents=True)
        upstream_doc = upstream / sync.ARTICLES / "guide.md"
        upstream_doc.write_text("# Guide\n\nUpstream: old.\n\nMiddle section.\n\nLocal note: original.\n")
        initial = commit(upstream)
        local_doc = local / sync.ARTICLES / "guide.md"
        # Reproduce a Windows checkout against Git's LF-normalized blobs.
        local_doc.write_bytes(upstream_doc.read_text().replace("Local note: original.", "Local note: adapted.").replace("\n", "\r\n").encode())
        revision = local / sync.REVISION
        local_only = local / sync.ARTICLES / "local-only.md"
        local_only.write_text("Locally authored\n")
        commit(local)
        revision.write_text(initial + "\n")

        # Formatting is exercised against the real upstream by --dry-run;
        # these fixtures isolate Git merging and preservation behavior.
        with patch.object(sync, "format_doc", side_effect=lambda root, name, data: data):
            upstream_doc.write_text(upstream_doc.read_text().replace("Upstream: old.", "Upstream: updated."))
            extra = upstream / sync.ARTICLES / "extra.md"
            extra.write_text("New upstream article\n")
            incoming = commit(upstream)
            before = local_doc.read_bytes()
            sync.sync_docs(local, str(upstream), "HEAD", True)
            assert local_doc.read_bytes() == before
            assert revision.read_text().strip() == initial
            assert not (local / sync.ARTICLES / "extra.md").exists()
            sync.sync_docs(local, str(upstream), "HEAD", False)
            assert "Upstream: updated." in local_doc.read_text()
            assert "Local note: adapted." in local_doc.read_text()
            assert (local / sync.ARTICLES / "extra.md").read_text() == extra.read_text()
            assert local_only.read_text() == "Locally authored\n"
            assert revision.read_text().strip() == incoming
            commit(local)
            synced = local_doc.read_bytes()
            sync.sync_docs(local, str(upstream), "HEAD", False)
            assert git(local, "status", "--porcelain") == ""

            local_doc.write_text(local_doc.read_text() + "Uncommitted user edit\n")
            try:
                sync.sync_docs(local, str(upstream), "HEAD", False)
            except ValueError as error:
                assert "Commit or resolve" in str(error)
            else:
                raise AssertionError("Uncommitted docs were overwritten")
            local_doc.write_bytes(synced)

            local_doc.write_text(local_doc.read_text().replace("Upstream: updated.", "Upstream: local edit."))
            commit(local)
            upstream_doc.write_text(upstream_doc.read_text().replace("Upstream: updated.", "Upstream: conflicting edit."))
            extra.write_text("Changed upstream article\n")
            commit(upstream)
            try:
                sync.sync_docs(local, str(upstream), "HEAD", False)
            except ValueError as error:
                assert "Resolve conflicts" in str(error)
            else:
                raise AssertionError("Conflicting edits were overwritten")
            assert "Upstream: local edit." in local_doc.read_text()
            assert (local / sync.ARTICLES / "extra.md").read_text() == "New upstream article\n"
            assert revision.read_text().strip() == incoming

            local_doc.write_text(local_doc.read_text().replace("Upstream: local edit.", "Upstream: conflicting edit."))
            commit(local)
            extra.unlink()
            commit(upstream)
            sync.sync_docs(local, str(upstream), "HEAD", False)
            assert not (local / sync.ARTICLES / "extra.md").exists()
            assert local_only.exists()

        with patch.object(sync, "ROOT", local), patch.object(sync.subprocess, "run") as run:
            sync.main(["--jars-only"])
            run.assert_called_once_with(["node", str(local / "scripts/setup.js")], cwd=local, check=True)
            run.reset_mock()
            sync.main(["--jars-only", "--dry-run"])
            run.assert_not_called()
    print("Upstream sync checks passed: merge, preview, additions, deletions, local edits, conflicts, JAR delegation")


if __name__ == "__main__":
    check()
