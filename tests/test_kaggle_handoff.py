import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
import zipfile


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "audit_kaggle_result", ROOT / "scripts/audit_kaggle_result.py"
)
AUDIT = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(AUDIT)


class KaggleHandoff(unittest.TestCase):
    def test_package_builds_clean_commit_pinned_notebooks(self):
        source = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True
        ).strip()
        with tempfile.TemporaryDirectory() as temp:
            output = Path(temp) / "handoff"
            subprocess.run(
                [sys.executable, "-X", "utf8", "scripts/package_kaggle_handoff.py",
                 "--source-ref", source, "--output-dir", str(output)],
                cwd=ROOT, check=True, capture_output=True, text=True,
            )
            manifest = json.loads((output / "handoff.json").read_text("utf-8"))
            self.assertEqual(manifest["source_commit"], source)
            self.assertFalse(manifest["claims"]["github_writeback"])
            for name, settings in (
                ("primitive_lean_setup_one_cell.ipynb", ("RUN_SETUP = True", "RUN_PROOFS = False")),
                ("primitive_lean_proof_check.ipynb", ("RUN_SETUP = True", "RUN_PROOFS = True")),
            ):
                path = output / name
                self.assertNotIn(b"\r", path.read_bytes())
                self.assertEqual(hashlib.sha256(path.read_bytes()).hexdigest(), manifest["notebooks"][name]["sha256"])
                notebook = json.loads(path.read_text("utf-8"))
                self.assertEqual(notebook["metadata"]["primitive_lean"]["source_commit"], source)
                code = [cell for cell in notebook["cells"] if cell["cell_type"] == "code"]
                self.assertEqual(len(code), 1)
                self.assertIsNone(code[0]["execution_count"])
                self.assertEqual(code[0]["outputs"], [])
                text = "".join(code[0]["source"])
                for setting in settings:
                    self.assertIn(setting, text)
                self.assertNotIn("\r", text)
                self.assertIn("\\n", text)

    def make_result(self, path, source):
        state = {
            "run_id": "fresh-run",
            "source_commit": source,
            "source": {"status": "passed", "source_commit": source,
                       "sha256": {"tools/verify.py": "abc"}, "verified_files": 117},
            "setup": {"status": "passed"},
            "proofs": {"status": "passed",
                       "run": {"exit_code": 0},
                       "result": {"passed": True, "timestamp_utc": "fresh",
                                  "stages": [{"name": "joint", "passed": True}],
                                  "theorem_count": 494, "declaration_count": 538}},
        }
        with zipfile.ZipFile(path, "w", zipfile.ZIP_DEFLATED) as archive:
            archive.writestr("notebook_run.json", json.dumps(state))

    def test_audit_accepts_fresh_passing_result_and_rejects_wrong_commit(self):
        source = "a" * 40
        with tempfile.TemporaryDirectory() as temp:
            result = Path(temp) / "result.zip"
            self.make_result(result, source)
            report = AUDIT.audit(result, source)
            self.assertEqual(report["status"], "PASS")
            self.assertEqual(report["theorem_count"], 494)
            with self.assertRaisesRegex(ValueError, "does not match"):
                AUDIT.audit(result, "b" * 40)

    def test_audit_rejects_not_run_proofs(self):
        source = "c" * 40
        with tempfile.TemporaryDirectory() as temp:
            result = Path(temp) / "result.zip"
            self.make_result(result, source)
            with zipfile.ZipFile(result, "r") as archive:
                state = json.loads(archive.read("notebook_run.json"))
            state["proofs"] = {"status": "not_run"}
            with zipfile.ZipFile(result, "w", zipfile.ZIP_DEFLATED) as archive:
                archive.writestr("notebook_run.json", json.dumps(state))
            with self.assertRaisesRegex(ValueError, "did not record"):
                AUDIT.audit(result, source)


if __name__ == "__main__":
    unittest.main()
