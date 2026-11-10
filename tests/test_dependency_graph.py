"""Regression tests for dependency-graph Git provenance; stdlib only."""
import hashlib
import importlib.util
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

SCRIPT = Path(__file__).resolve().parents[1] / "tools/generate_dependency_graph.py"
spec = importlib.util.spec_from_file_location("dependency_graph", SCRIPT)
graph = importlib.util.module_from_spec(spec)
spec.loader.exec_module(graph)


class PinnedSnapshotTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.git("init", "-q")
        self.git("config", "user.email", "test@example.invalid")
        self.git("config", "user.name", "Graph Test")
        self.write("lean/Sample.lean", "namespace Sample\ntheorem original : True := by trivial\n")
        self.write("lean/.lake/Poison.lean", "theorem poison : True := by trivial\n")
        self.write("linear_input/lean_check/Base.inc", "theorem base : True := by trivial\n")
        self.write("linear_input/verify_lean.py", "PARTS = ['Base.inc']\n")
        self.write("tools/verify_main_result.py", "SUPPLEMENTS = [('Extra.inc', 'test')]\n")
        self.write("docs/dependency/pr_snapshot.json",
                   '{"snapshot_date":"2026-11-05","prs":[]}\n')
        self.git("add", "-A")
        self.git("commit", "-qm", "snapshot")
        self.source_sha = self.git("rev-parse", "HEAD").strip()

    def git(self, *args):
        return subprocess.check_output(
            ["git", "-C", str(self.root), *args], stderr=subprocess.STDOUT, text=True
        )

    def write(self, path, data):
        p = self.root / path
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(data, encoding="utf8")

    def test_main_inputs_are_pinned_and_ignore_lake(self):
        expected = "namespace Sample\ntheorem original : True := by trivial\n"
        self.write("lean/Sample.lean", "theorem worktree_only : True := by trivial\n")
        self.write("linear_input/verify_lean.py", "PARTS = ['Changed.inc']\n")
        self.write("lean/Future.lean", "theorem future : True := by trivial\n")
        self.git("add", "-A")
        self.git("commit", "-qm", "post-snapshot")
        with patch.object(graph, "ROOT", self.root):
            self.assertEqual(graph.resolved_commit(self.source_sha[:12]), self.source_sha)
            self.assertEqual(graph.committed_text(self.source_sha, "lean/Sample.lean"), expected)
            self.assertEqual(graph.assignment("linear_input/verify_lean.py",
                                              "PARTS", self.source_sha), ["Base.inc"])
            paths = graph.tracked_source_paths(self.source_sha)
            self.assertEqual(paths, ["lean/Sample.lean", "linear_input/lean_check/Base.inc"])
            nodes = graph.sources(set(), set(), self.source_sha)
        self.assertEqual(len(nodes), 2)
        self.assertEqual(nodes[0]["sha256"], hashlib.sha256(expected.encode()).hexdigest())
        self.assertIn("original", nodes[0]["declarations"])
        self.assertNotIn("worktree_only", nodes[0]["declarations"])
        self.assertTrue(all(".lake" not in n["path"] for n in nodes))

    def test_pr_base_uses_snapshot_sha_not_moved_branch(self):
        self.git("checkout", "-qb", "snapshot-base", self.source_sha)
        self.write("lean/BaseChange.lean", "theorem baseChange : True := by trivial\n")
        self.git("add", "-A")
        self.git("commit", "-qm", "base snapshot")
        base_sha = self.git("rev-parse", "HEAD").strip()
        self.git("checkout", "-qb", "snapshot-head")
        self.write("lean/PRChange.lean", "theorem prChange : True := by trivial\n")
        self.git("add", "-A")
        self.git("commit", "-qm", "head snapshot")
        head_sha = self.git("rev-parse", "HEAD").strip()
        self.git("branch", "-f", "snapshot-base", head_sha)
        snapshot = {"prs": [
            {"number": 3, "head_branch": "snapshot-base", "head_sha": base_sha,
             "base_branch": "main"},
            {"number": 31, "head_branch": "snapshot-head", "head_sha": head_sha,
             "base_branch": "snapshot-base"},
        ]}
        with patch.object(graph, "ROOT", self.root):
            nodes, inputs = graph.branch_sources(snapshot, set(), set(), self.source_sha)
        self.assertEqual([(n["scope"], n["path"]) for n in nodes],
                         [("pr31", "lean/PRChange.lean")])
        self.assertEqual(inputs[0]["base_sha"], base_sha)
        self.assertEqual(inputs[0]["head_sha"], head_sha)
        self.assertEqual(inputs[0]["merge_base_sha"], base_sha)


if __name__ == "__main__":
    unittest.main()
