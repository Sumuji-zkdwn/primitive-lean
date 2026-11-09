"""Regression tests for exact-commit ERG source evidence export."""

import hashlib
from pathlib import Path
import subprocess
import tempfile
import unittest

from tools.erg.export_formal_evidence import EvidenceError, build_manifest, source_paths


def git(root, *args):
    return subprocess.check_output(["git", "-C", str(root), *args], text=True).strip()


class FormalEvidenceTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        git(self.root, "init", "-q")
        git(self.root, "config", "user.email", "example@example.invalid")
        git(self.root, "config", "user.name", "Test")
        (self.root / "lean/Research").mkdir(parents=True)
        (self.root / "linear_input/lean_check").mkdir(parents=True)
        (self.root / "lean/Research/Example.lean").write_bytes(b"theorem example : True := by trivial\n")
        (self.root / "linear_input/lean_check/F0.inc").write_bytes(b"theorem f0 : True := by trivial\n")
        (self.root / "lean/lean-toolchain").write_text("leanprover/lean4:v4.30.0-rc2\n")
        (self.root / "README.md").write_text("ignored\n")
        git(self.root, "add", ".")
        git(self.root, "commit", "-qm", "fixture")
        self.head = git(self.root, "rev-parse", "HEAD")

    def tearDown(self):
        self.temp.cleanup()

    def test_exact_commit_hashes_ignore_dirty_and_untracked_files(self):
        original = b"theorem example : True := by trivial\n"
        (self.root / "lean/Research/Example.lean").write_text("a dirty, invalid proof")
        (self.root / "lean/Research/Untracked.lean").write_text("theorem unknown : True := trivial")
        env = {
            "GITHUB_REPOSITORY": "Sumuji-zkdwn/primitive-lean",
            "GITHUB_RUN_ID": "1234",
            "GITHUB_RUN_ATTEMPT": "2",
            "GITHUB_SHA": "a" * 40,
        }
        result = build_manifest(self.root, self.head, env)
        self.assertEqual(result["source_commit"], self.head)
        self.assertEqual(result["source_file_count"], 3)
        self.assertEqual(
            result["source_files"]["lean/Research/Example.lean"], hashlib.sha256(original).hexdigest()
        )
        self.assertNotIn("lean/Research/Untracked.lean", result["source_files"])
        self.assertNotIn("README.md", result["source_files"])
        self.assertEqual(result["actions"]["run_url"], "https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/1234")
        self.assertEqual(result["actions"]["conclusion"], "not_asserted_check_run_separately")
        self.assertEqual(result["actions"]["event_sha"], "a" * 40)

    def test_head_mismatch_fails_closed(self):
        with self.assertRaisesRegex(EvidenceError, "does not match expected head"):
            build_manifest(self.root, "0" * 40, {})
        with self.assertRaisesRegex(EvidenceError, "complete 40-hex"):
            build_manifest(self.root, "HEAD", {})

    def test_symlinks_are_excluded(self):
        (self.root / "lean/Sneaky.lean").symlink_to(self.root / "README.md")
        git(self.root, "add", "lean/Sneaky.lean")
        git(self.root, "commit", "-qm", "symlink")
        head = git(self.root, "rev-parse", "HEAD")
        self.assertNotIn("lean/Sneaky.lean", source_paths(self.root, head))

    def test_missing_source_fails_closed(self):
        for path in ("lean/Research/Example.lean", "linear_input/lean_check/F0.inc"):
            (self.root / path).unlink()
        git(self.root, "add", "-u")
        git(self.root, "commit", "-qm", "remove proof sources")
        head = git(self.root, "rev-parse", "HEAD")
        with self.assertRaisesRegex(EvidenceError, "no tracked Lean proof sources"):
            build_manifest(self.root, head, {})

    def test_invalid_run_metadata_fails_closed(self):
        with self.assertRaisesRegex(EvidenceError, "GITHUB_RUN_ID must be numeric"):
            build_manifest(self.root, self.head, {"GITHUB_RUN_ID": "bad/id"})


if __name__ == "__main__":
    unittest.main()
