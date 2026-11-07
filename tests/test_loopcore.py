"""Portable loop tests, independent of Lean and Kaggle."""
import json
from pathlib import Path
import tempfile
import unittest

from loopcore.adapters import finite
from loopcore.engine import audit, run_one


class LoopTests(unittest.TestCase):
    def test_candidates_match_original_cardinality(self):
        rows = list(finite.candidates())
        self.assertEqual(len(rows), 84)
        self.assertEqual(rows[0], {"states": 3, "image_of_zero": 0, "image_of_one": 2})

    def test_all_finite_semantics(self):
        for i, model in enumerate(finite.candidates(), 1):
            self.assertTrue(finite.check(model, finite.build(model, i), i)["passed"])

    def test_feedback_and_provenance(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            self.assertEqual(run_one(root, "finite")["cycle"], 1)
            self.assertEqual(run_one(root, "finite")["cycle"], 2)
            self.assertTrue(audit(root, "finite", rerun_checks=True)["passed"])
            ledger = json.loads((root / "ledger.json").read_text())
            self.assertEqual(ledger["cycles"][1]["previous_sha256"], ledger["cycles"][0]["record_sha256"])

    def test_tampering_blocks_future_generation(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            run_one(root, "finite")
            target = root / "cycles" / "00001" / "witness.lean"
            target.write_bytes(target.read_bytes() + b"-- tampered\n")
            with self.assertRaisesRegex(ValueError, "hash mismatch"):
                audit(root, "finite")
            with self.assertRaisesRegex(ValueError, "hash mismatch"):
                run_one(root, "finite")

    def test_cross_domain_ledger_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            run_one(root, "finite")
            with self.assertRaisesRegex(ValueError, "domain mismatch"):
                audit(root, "wfs")

    def test_model_falsification_rejected(self):
        wrong = {"states": 3, "image_of_zero": 0, "image_of_one": 1}
        self.assertFalse(finite.check(wrong, finite.build(wrong, 1), 1)["passed"])

    def test_rebuilt_generated_lean_bytes(self):
        model = next(finite.candidates())
        files = finite.build(model, 1)
        files["witness.lean"] += b"-- hidden change\n"
        self.assertFalse(finite.check(model, files, 1)["passed"])


if __name__ == "__main__":
    unittest.main()
