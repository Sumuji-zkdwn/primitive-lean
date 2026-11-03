"""Conservative regression tests for the on-main autonomy controller.

The tests mock only the Git branch head; they never claim to compile Lean.
"""
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "primitive_auto_growth", ROOT / "tools/autonomy/grow.py"
)
GROW = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(GROW)


class GeneratorTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.write("tools/verify_main_result.py",
                   "SUPPLEMENTS = (\n    ('existing.inc', 'Existing'),\n)\n\n\ndef sha(x):\n    pass\n")
        self.write("tools/verify.py",
                   "    supplemental_scopes = {\n        'Existing': 'example',\n"
                   "    }\n    supplemental_groups = {}\n")
        self.write("docs/integration/manifest.json", json.dumps({
            "schema_version": 1,
            "files": [],
            "post_snapshot_additions": [],
            "baseline_paths": [],
        }))
        patcher = patch.object(GROW, "require_branch", return_value="a" * 40)
        self.addCleanup(patcher.stop)
        patcher.start()

    def write(self, path, content):
        dest = self.root / path
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_text(content, encoding="utf-8")

    def test_all_candidates_have_unique_separating_outputs(self):
        options = list(GROW.candidates())
        self.assertEqual(len(options), 84)
        self.assertEqual(
            len(set((r["states"], r["image_of_zero"], r["image_of_one"])
                    for r in options)), len(options))
        self.assertTrue(all((r["image_of_zero"] < 2) !=
                            (r["image_of_one"] < 2) for r in options))

    def test_prepare_is_additive_and_audited(self):
        self.assertTrue(GROW.prepare(self.root))
        ledger = json.loads((self.root/GROW.LEDGER_PATH).read_text())
        row = ledger["cycles"][0]
        self.assertEqual(row["status"], "candidate")
        self.assertEqual(row["claimed_theorems"], 5)
        self.assertEqual(row["claimed_definitions"], 3)
        source = (self.root/row["source"]).read_text()
        self.assertEqual(GROW.digest(source), row["sha256"])
        m = json.loads((self.root/GROW.MANIFEST_PATH).read_text())
        self.assertEqual(m["files"][0]["sha256"], row["sha256"])
        self.assertIn(row["name"], (self.root/GROW.REGISTRY_PATH).read_text())
        self.assertIn(row["name"], (self.root/GROW.SCOPES_PATH).read_text())
        with self.assertRaisesRegex(RuntimeError, "Unverified cycle"):
            GROW.prepare(self.root)

    def test_unverified_cycle_cannot_be_sealed(self):
        GROW.prepare(self.root)
        with self.assertRaises(FileNotFoundError):
            GROW.seal(self.root)
        ledger = json.loads((self.root/GROW.LEDGER_PATH).read_text())
        self.assertEqual(ledger["cycles"][0]["status"], "candidate")

    def test_fresh_success_is_required_before_a_next_cycle(self):
        GROW.prepare(self.root)
        ledger = json.loads((self.root/GROW.LEDGER_PATH).read_text())
        source = ledger["cycles"][0]["source"]
        for path in ("verification/pr-integration.json",
                     "verification/proof-only.json",
                     "verification/pr-source-audit.json"):
            self.write(path, '{"passed": true}')
        self.write("verification/main-result.json", json.dumps({
            "passed": True,
            "supplemental_sources": [source],
            "total_theorem_count": 1344,
            "total_declaration_count": 1732,
        }))
        GROW.seal(self.root)
        after = json.loads((self.root/GROW.LEDGER_PATH).read_text())
        self.assertEqual(after["cycles"][0]["status"], "verified")
        self.assertTrue(GROW.prepare(self.root))
        new = json.loads((self.root/GROW.LEDGER_PATH).read_text())
        self.assertEqual(new["cycles"][1]["status"], "candidate")
        self.assertNotEqual(new["cycles"][0]["model"], new["cycles"][1]["model"])


if __name__ == "__main__":
    unittest.main()
