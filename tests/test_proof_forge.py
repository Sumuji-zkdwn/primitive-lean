"""Offline tests for the bounded observer certificate generator.

These do not claim Lean validation; the separate pinned CI compiles every
generated theorem with --trust=0 and audits its axioms.
"""
import json
from pathlib import Path
import tempfile
import unittest

from tools.autonomy import proof_forge as forge


def model(name="delayed_split"):
    return {
        "schema_version": 1,
        "name": name,
        "observations": [0, 0, 0, 1],
        "transitions": [[1, 2, 3, 3], [0, 1, 2, 3]],
        "pair": [0, 1],
    }


class ProofForgeTests(unittest.TestCase):
    def test_exact_shortest_word(self):
        spec = model()
        got = forge.solve(spec)
        self.assertEqual(got["kind"], "DISTINGUISHABLE")
        self.assertEqual(got["word"], [0, 0])
        self.assertEqual(got["states_at_witness"], [2, 3])
        forge.validate_result(spec, got)
        source, names = forge.lean_source(spec, got)
        self.assertIn("theorem no_shorter_word", source)
        self.assertIn("have checked : agreeUpTo 1", source)
        self.assertIn("simp [agreeUpTo, readout, step, originLeft, originRight]", source)
        self.assertEqual(len(names), 3)

    def test_unbounded_equivalence_certificate(self):
        spec = {
            "schema_version": 1, "name": "invisible_histories",
            "observations": [0, 0, 1, 1],
            "transitions": [[2, 3, 2, 3], [0, 1, 0, 1]],
            "pair": [0, 1],
        }
        got = forge.solve(spec)
        self.assertEqual(got["kind"], "EQUIVALENT")
        self.assertEqual({tuple(p) for p in got["pairs"]},
                         {(0, 1), (2, 3)})
        forge.validate_result(spec, got)
        source, names = forge.lean_source(spec, got)
        self.assertIn("theorem all_words_same", source)
        self.assertIn("theorem safe_step", source)
        self.assertEqual(len(names), 5)

    def test_zero_length_distinguishes(self):
        spec = model()
        spec["pair"] = [0, 3]
        got = forge.solve(spec)
        self.assertEqual(got["word"], [])
        source, _ = forge.lean_source(spec, got)
        self.assertIn("def witness : List Action := []", source)
        self.assertIn("  omega", source)

    def test_identical_states_never_distinguish(self):
        spec = model()
        spec["pair"] = [1, 1]
        got = forge.solve(spec)
        self.assertEqual(got["kind"], "EQUIVALENT")
        forge.validate_result(spec, got)

    def test_cannot_smuggle_code_or_large_instances(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            path = root / "delayed_split.json"
            spec = model()
            spec["name"] = "bad; import System"
            path.write_text(json.dumps(spec), encoding="utf-8")
            with self.assertRaises(ValueError):
                forge.read_request(path)
            spec = model()
            spec["observations"][1] = True
            path.write_text(json.dumps(spec), encoding="utf-8")
            with self.assertRaises(ValueError):
                forge.read_request(path)
            spec = model()
            spec["observations"] = [0] * 13
            path.write_text(json.dumps(spec), encoding="utf-8")
            with self.assertRaises(ValueError):
                forge.read_request(path)
            path.write_text('{"schema_version":1,"name":"delayed_split",'
                            '"name":"delayed_split"}', encoding="utf-8")
            with self.assertRaises(ValueError):
                forge.read_request(path)

    def test_generation_is_deterministic_and_fails_closed(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            req = root / "requests"
            req.mkdir()
            (req / "delayed_split.json").write_text(
                json.dumps(model()), encoding="utf-8")
            out = root / "output"
            self.assertEqual(forge.generate(req, out, "a" * 40), 0)
            record = json.loads((out / "delayed_split.json").read_text())
            self.assertFalse(record["kernel_verified"])
            self.assertEqual(record["status"], "PENDING_KERNEL_VERIFICATION")
            self.assertEqual(record["checkout_sha"], "a" * 40)
            original = (out / "delayed_split.lean").read_bytes()
            with self.assertRaises(ValueError):
                forge.generate(req, out, "b" * 40)
            # A missing Lean log is never mistaken for a successful proof.
            self.assertEqual(forge.audit(out), 1)
            result = json.loads((out / "delayed_split.json").read_text())
            self.assertEqual(result["status"], "KERNEL_CHECK_FAILED")
            self.assertEqual(original, (out / "delayed_split.lean").read_bytes())

    def test_audit_requires_one_axiom_record_per_theorem(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            req = root / "requests"
            req.mkdir()
            (req / "delayed_split.json").write_text(
                json.dumps(model()), encoding="utf-8")
            out = root / "output"
            forge.generate(req, out, "a" * 40)
            record = json.loads((out / "delayed_split.json").read_text())
            (out / "delayed_split.exit").write_text("0\n")
            (out / "delayed_split.log").write_text(
                "\n".join(f"'{name}' does not depend on any axioms"
                          for name in record["theorems"]) + "\n")
            self.assertEqual(forge.audit(out), 0)
            verified = json.loads((out / "delayed_split.json").read_text())
            self.assertTrue(verified["kernel_verified"])
            (out / "delayed_split.log").write_text(
                "ProofForge_delayed_split.word_separates depends on axioms: [sorryAx]\n")
            self.assertEqual(forge.audit(out), 1)


if __name__ == "__main__":
    unittest.main()
