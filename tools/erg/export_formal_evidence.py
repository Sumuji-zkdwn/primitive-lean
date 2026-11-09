#!/usr/bin/env python3
"""Export exact-commit source hashes and GitHub Actions provenance for ERG.

This is a *source inventory*, not a Lean checker, an axiom audit, or a
semantic claim that a conversational proposition matches a Lean declaration.
The workflow's final conclusion must be checked separately on GitHub.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

SHA_PATTERN = re.compile(r"[0-9a-f]{40}\Z")
SOURCE_PREFIXES = ("lean/", "linear_input/lean_check/")
SOURCE_SUFFIXES = (".lean", ".inc")
BUILD_METADATA = {"lean/lean-toolchain", "lean/lakefile.toml", "lean/lake-manifest.json"}


class EvidenceError(Exception):
    """Expected source snapshot or Git metadata is unavailable."""


def git(root: Path, *args: str) -> bytes:
    process = subprocess.run(
        ["git", "-C", str(root), *args], capture_output=True, check=False
    )
    if process.returncode:
        raise EvidenceError(
            f"git {args[0]} failed ({process.returncode}): "
            + process.stderr.decode("utf-8", errors="replace").strip()
        )
    return process.stdout


def source_paths(root: Path, commit: str) -> list[str]:
    """Only immutable, regular Git blobs; never generated or dirty worktree files."""
    listed = git(root, "ls-tree", "-r", "-z", "--full-tree", commit)
    paths = []
    for entry in listed.split(b"\0"):
        if not entry:
            continue
        info, raw_path = entry.split(b"\t", 1)
        mode, object_type, _ = info.split(b" ", 2)
        if mode not in (b"100644", b"100755") or object_type != b"blob":
            continue
        path = raw_path.decode("utf-8", errors="strict")
        is_source = path.startswith(SOURCE_PREFIXES) and path.endswith(SOURCE_SUFFIXES)
        if is_source or path in BUILD_METADATA:
            paths.append(path)
    return sorted(paths)


def build_manifest(root: Path, expected_head: str, env: dict[str, str]) -> dict:
    if not SHA_PATTERN.fullmatch(expected_head):
        raise EvidenceError("--expected-head must be a complete 40-hex SHA")
    head = git(root, "rev-parse", "HEAD").decode("ascii").strip()
    if head != expected_head:
        raise EvidenceError(f"checkout HEAD {head} does not match expected head {expected_head}")
    paths = source_paths(root, head)
    if not any(path.endswith(SOURCE_SUFFIXES) for path in paths):
        raise EvidenceError("no tracked Lean proof sources at the pinned commit")
    files = {
        path: hashlib.sha256(git(root, "show", f"{head}:{path}")).hexdigest()
        for path in paths
    }
    repository = env.get("GITHUB_REPOSITORY") or "Sumuji-zkdwn/primitive-lean"
    run_id = env.get("GITHUB_RUN_ID")
    run_attempt = env.get("GITHUB_RUN_ATTEMPT")
    if run_id is not None and not run_id.isdecimal():
        raise EvidenceError("GITHUB_RUN_ID must be numeric")
    if run_attempt is not None and not run_attempt.isdecimal():
        raise EvidenceError("GITHUB_RUN_ATTEMPT must be numeric")
    run_url = f"https://github.com/{repository}/actions/runs/{run_id}" if run_id else None
    return {
        "schema_version": 1,
        "kind": "exact_commit_formal_source_inventory",
        "repository": repository,
        "source_commit": head,
        "source_files": files,
        "source_file_count": len(files),
        "actions": {
            "workflow": env.get("GITHUB_WORKFLOW"),
            "job": env.get("GITHUB_JOB"),
            "event": env.get("GITHUB_EVENT_NAME"),
            "event_sha": env.get("GITHUB_SHA"),
            "run_id": run_id,
            "run_attempt": run_attempt,
            "run_url": run_url,
            "conclusion": "not_asserted_check_run_separately",
        },
        "limitations": [
            "The inventory hashes committed blobs, not mutable worktree files.",
            "The corresponding GitHub Actions run and exact-head verification job must independently conclude success.",
            "This manifest does not run Lean, check axioms, or establish semantic fidelity to ERG nodes.",
            "An ERG formal binding still requires its own fixed-commit declaration and fidelity checks.",
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--expected-head", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    try:
        manifest = build_manifest(args.root.resolve(), args.expected_head, os.environ)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(
            json.dumps(manifest, ensure_ascii=False, sort_keys=True, indent=2) + "\n",
            encoding="utf-8",
        )
    except (EvidenceError, OSError, UnicodeError) as exc:
        print(f"ERG_EVIDENCE_ERROR: {exc}", file=sys.stderr)
        return 1
    print(
        f"ERG_FORMAL_EVIDENCE: commit={manifest['source_commit']} "
        f"files={manifest['source_file_count']} "
        "(CI conclusion and semantic fidelity not asserted)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
