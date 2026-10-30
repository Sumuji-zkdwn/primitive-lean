"""Regression tests for the supplemental audit; all inputs here are synthetic."""
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest
import zipfile

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
spec = importlib.util.spec_from_file_location("audit_records", ROOT / "scripts/audit_kaggle_result_records.py")
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
SOURCE = "a" * 40


class RecordAuditTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.path = Path(self.temp.name) / "result.zip"
        self.deps = [{"name": str(i), "expected": "rev", "actual": "rev", "match": True} for i in range(9)]
        stages = [{"name": name, "passed": True, "fresh_report": True,
                   "run": {"exit_code": 0, "warnings": []}, "warnings": []}
                  for name in ("joint", "supplement")]
        proof = {"timestamp_utc": "synthetic", "passed": True, "stages": stages,
                 "theorem_count": 494, "declaration_count": 538, "errors": []}
        hashes = {f"source{i}": "b" * 64 for i in range(117)}
        state = {"source_commit": SOURCE, "run_id": "synthetic",
                 "source": {"status": "passed", "source_commit": SOURCE, "verified_files": 117, "sha256": hashes},
                 "setup": {"status": "passed", "dependencies": self.deps},
                 "proofs": {"status": "passed", "run": {"exit_code": 0}, "result": proof}}
        names = [f"declaration{i}" for i in range(538)]
        main = {"passed": True, "total_theorem_count": 494, "total_declaration_count": 538,
                "joint_axiom_audit": True, "baseline_axioms_match": True, "compile": {"exit_code": 0},
                "all_declarations": [{"name": n} for n in names], "axioms": {n: [] for n in names},
                "source_hashes": {"source0": hashes["source0"]},
                "dependencies": self.deps, "dependencies_after_compile": self.deps,
                "log_sha256": hashlib.sha256(b"synthetic log").hexdigest()}
        joint = {"passed": True, "joint_axiom_audit": True, "compile": {"exit_code": 0}, "dependencies": self.deps}
        self.files = {"notebook_run.json": json.dumps(state), "proofs/verification/proof-only.json": json.dumps(proof),
                      "proofs/verification/main-result.json": json.dumps(main),
                      "proofs/linear_input/lean_results.json": json.dumps(joint)}
        self.files.update({name: "synthetic log" for name in module.LOGS})

    def audit(self):
        with zipfile.ZipFile(self.path, "w") as z:
            for name, data in self.files.items():
                z.writestr(name, data)
        return module.audit_records(self.path, SOURCE)

    def test_internally_consistent_records_pass(self):
        self.assertEqual(self.audit()["status"], "PASS")

    def test_notebook_record_alone_is_insufficient(self):
        self.files = {"notebook_run.json": self.files["notebook_run.json"]}
        with self.assertRaisesRegex(ValueError, "lacks"):
            self.audit()

    def test_proof_report_must_match_state(self):
        self.files["proofs/verification/proof-only.json"] = "{}"
        with self.assertRaisesRegex(ValueError, "differs"):
            self.audit()

    def test_log_hash_must_match(self):
        self.files["proofs/verification/main-result.log"] = "changed"
        with self.assertRaisesRegex(ValueError, "log hash"):
            self.audit()

    def test_declaration_names_must_match_axioms(self):
        path = "proofs/verification/main-result.json"
        main = json.loads(self.files[path])
        main["all_declarations"][0]["name"] = "other"
        self.files[path] = json.dumps(main)
        with self.assertRaisesRegex(ValueError, "Declaration"):
            self.audit()

    def test_stage_must_be_fresh(self):
        path = "notebook_run.json"
        state = json.loads(self.files[path])
        state["proofs"]["result"]["stages"][0]["fresh_report"] = False
        self.files[path] = json.dumps(state)
        self.files["proofs/verification/proof-only.json"] = json.dumps(state["proofs"]["result"])
        with self.assertRaisesRegex(ValueError, "fresh"):
            self.audit()

    def test_source_hash_mismatch_rejected(self):
        path = "proofs/verification/main-result.json"
        main = json.loads(self.files[path])
        main["source_hashes"]["source0"] = "c" * 64
        self.files[path] = json.dumps(main)
        with self.assertRaisesRegex(ValueError, "hashes disagree"):
            self.audit()

    def test_dependencies_must_agree_across_reports(self):
        path = "proofs/linear_input/lean_results.json"
        joint = json.loads(self.files[path])
        joint["dependencies"][0]["actual"] = "different"
        self.files[path] = json.dumps(joint)
        with self.assertRaisesRegex(ValueError, "Dependency"):
            self.audit()

    def test_unknown_axiom_is_rejected(self):
        path = "proofs/verification/main-result.json"
        main = json.loads(self.files[path])
        main["axioms"]["declaration0"] = ["unapproved.axiom"]
        self.files[path] = json.dumps(main)
        with self.assertRaisesRegex(ValueError, "allowed axioms"):
            self.audit()


if __name__ == "__main__":
    unittest.main()
