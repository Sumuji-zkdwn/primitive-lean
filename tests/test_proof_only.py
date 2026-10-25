"""Orchestration tests. No test here simulates a successful Lean proof."""
from pathlib import Path
import importlib.util
import json
import tempfile
import unittest

SPEC = importlib.util.spec_from_file_location("proof_only", Path(__file__).parents[1] / "tools/proof_only.py")
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class FreshReports(unittest.TestCase):
    def test_stale_success_is_retired_and_cannot_pass(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / "linear_input").mkdir()
            old = root / "linear_input/lean_results.json"
            old.write_text('{"passed": true}')
            calls = []

            def failed(args, name, cwd):
                calls.append(name)
                return {"exit_code": 1, "warnings": []}

            report = MODULE.run_proof_only(root, failed)
            self.assertFalse(report["passed"])
            self.assertFalse(report["stages"][0]["fresh_report"])
            self.assertEqual(calls, ["proof-only-joint"])
            self.assertTrue(list((root / "verification/proof-history").glob("lean_results-*.json")))

    def test_nonzero_exit_rejects_even_a_fresh_success_report(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / "linear_input").mkdir()

            def failed(args, name, cwd):
                (root / "linear_input/lean_results.json").write_text('{"passed": true}')
                return {"exit_code": 2, "warnings": []}

            report = MODULE.run_proof_only(root, failed)
            self.assertFalse(report["passed"])
            self.assertEqual(len(report["stages"]), 1)

    def test_supplement_failure_does_not_inherit_baseline_success(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / "linear_input").mkdir()

            def check(args, name, cwd):
                path = (root / "linear_input/lean_results.json" if name.endswith("joint")
                        else root / "verification/main-result.json")
                path.write_text(json.dumps({"passed": name.endswith("joint")}))
                return {"exit_code": 0, "warnings": []}

            report = MODULE.run_proof_only(root, check)
            self.assertFalse(report["passed"])
            self.assertEqual(len(report["stages"]), 2)
            self.assertIsNone(report["declaration_count"])
            self.assertEqual(report["historical_preservation"], "not_checked")


if __name__ == "__main__":
    unittest.main()
