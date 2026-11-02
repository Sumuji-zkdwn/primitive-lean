"""Regression tests for the 717 result auditor using synthetic records, not Lean runs."""
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
import zipfile

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("audit717", ROOT / "scripts/audit_kaggle_result_717.py")
audit717 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit717)
SOURCE = "a" * 40


class AuditorEvidenceTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.handoff_path = self.root / "handoff.json"
        hashes = {f"file{i}": "b" * 64 for i in range(126)}
        deps = [{"name": "mathlib", "revision": "c" * 40}]
        self.handoff_path.write_text(json.dumps({
            "schema": "primitive-lean-kaggle-handoff-717-v1", "proof_source_commit": SOURCE,
            "source_snapshot": {"source_sha256": hashes, "added_proof_sources": ["file0"]},
            "lean": {"toolchain": "lean-test", "dependencies": deps},
            "proof_counts": {"theorems": 717, "declarations": 836},
        }), encoding="utf-8")
        stages = [{"name": name, "passed": True, "fresh_report": True,
                   "run": {"exit_code": 0, "warnings": []}, "warnings": []}
                  for name in ("joint", "supplement")]
        proof = {"passed": True, "theorem_count": 717, "declaration_count": 836, "stages": stages}
        state = {"run_id": "synthetic", "source_commit": SOURCE,
                 "source": {"status": "passed", "source_commit": SOURCE, "verified_files": 126, "sha256": hashes},
                 "setup": {"status": "passed", "toolchain": "lean-test", "dependencies": [
                     {"name": "mathlib", "actual": "c" * 40, "match": True}]},
                 "proofs": {"status": "passed", "run": {"exit_code": 0}, "result": proof}}
        main = {"passed": True, "total_theorem_count": 717, "total_declaration_count": 836,
                "joint_axiom_audit": True, "baseline_axioms_match": True, "compile": {"exit_code": 0},
                "all_declarations": [{"name": f"d{i}"} for i in range(836)],
                "axioms": {f"d{i}": [] for i in range(836)}, "source_hashes": {"file0": hashes["file0"]}}
        self.files = {"notebook_run.json": json.dumps(state),
                      "proofs/verification/main-result.json": json.dumps(main),
                      "proofs/verification/proof-only.json": json.dumps(proof),
                      "proofs/linear_input/lean_results.json": json.dumps({"passed": True})}
        for name in ("proof-run.log", "proofs/verification/main-result.log",
                     "proofs/verification/proof-only-joint.log", "proofs/verification/proof-only-supplement.log",
                     "proofs/linear_input/lean_check/build.log", "proofs/linear_input/lean_check/elastica-build.log"):
            self.files[name] = "synthetic"

    def audit(self):
        path = self.root / "result.zip"
        with zipfile.ZipFile(path, "w") as z:
            for name, content in self.files.items():
                z.writestr(name, content)
        return audit717.audit(path, SOURCE, self.handoff_path)

    def test_consistent_records_pass(self):
        self.assertEqual(self.audit()["status"], "PASS")

    def test_missing_evidence_rejected(self):
        del self.files["proofs/verification/proof-only.json"]
        with self.assertRaisesRegex(ValueError, "lacks"):
            self.audit()

    def test_contradictory_proof_report_rejected(self):
        self.files["proofs/verification/proof-only.json"] = "{}"
        with self.assertRaisesRegex(ValueError, "differs"):
            self.audit()

    def test_declaration_axiom_names_must_match(self):
        path = "proofs/verification/main-result.json"
        main = json.loads(self.files[path])
        main["all_declarations"][0]["name"] = "different"
        self.files[path] = json.dumps(main)
        with self.assertRaisesRegex(ValueError, "names"):
            self.audit()


if __name__ == "__main__":
    unittest.main()
