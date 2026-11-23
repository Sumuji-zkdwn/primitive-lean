"""Offline regression for Primitive Autonomy V2 (not a Lean proof)."""
import copy
import json
from pathlib import Path
import tempfile
import unittest

from tools.autonomy import primitive_v2 as v2
from tools.autonomy import proof_forge as pf


ROOT = Path(__file__).resolve().parents[1]
HEAD = "a" * 40
DAY = "2026-11-23"


class PrimitiveV2Tests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.folder = Path(self.tmp.name)
        self.state = self.folder / "state.json"
        v2.save(self.state, v2.empty_state())

    def test_legacy_seed_is_unchanged_and_all_witnesses_unique(self):
        sha, seed = v2.legacy(ROOT)
        self.assertEqual(len(sha), 64)
        self.assertEqual(len(seed), 3)
        pool = v2.catalog(seed)
        self.assertEqual(len(pool), 123)
        self.assertEqual(len({v2.spec_id(spec) for spec in pool}), len(pool))
        self.assertEqual(sum(s["family"] == "legacy_split" for s in pool), 81)
        self.assertEqual(sum(s["family"] == "delayed_split" for s in pool), 36)
        self.assertEqual(sum(s["family"] == "inert_swap" for s in pool), 6)
        self.assertTrue(all(s["family"] != "legacy_split" or
                            (s["states"], s["a"], s["b"]) not in seed
                            for s in pool))

    def test_finite_semantics_of_three_families(self):
        specs = [
            {"family": "legacy_split", "states": 3, "a": 0, "b": 2},
            {"family": "legacy_split", "states": 8, "a": 7, "b": 0},
            {"family": "delayed_split", "states": 5, "depth": 2},
            {"family": "delayed_split", "states": 7, "depth": 4},
            {"family": "delayed_split", "states": 12, "depth": 9},
            {"family": "inert_swap", "states": 3},
            {"family": "inert_swap", "states": 8},
        ]
        for spec in specs:
            with self.subTest(spec=spec):
                old, new, before, after = v2.model_pair(spec)
                self.assertEqual(before["kind"], "EQUIVALENT")
                self.assertEqual(old["transitions"], [list(range(spec["states"]))])
                self.assertEqual(new["transitions"][0], list(range(spec["states"])))
                if spec["family"] == "inert_swap":
                    self.assertEqual(after["kind"], "EQUIVALENT")
                else:
                    self.assertEqual(after["kind"], "DISTINGUISHABLE")
                    expected = spec.get("depth", 1)
                    self.assertEqual(len(after["word"]), expected)
                    self.assertEqual(after["word"], [1] * expected)

    def test_refuse_bad_specs(self):
        bad = [
            {"family": "legacy_split", "states": 3, "a": 0, "b": 1},
            {"family": "legacy_split", "states": 3, "a": False, "b": 2},
            {"family": "delayed_split", "states": 5, "depth": 3},
            {"family": "delayed_split", "states": 13, "depth": 2},
            {"family": "inert_swap", "states": 12},
            {"family": "shell", "states": 3},
        ]
        for spec in bad:
            with self.subTest(spec=spec), self.assertRaises(ValueError):
                v2.model_pair(spec)

    def test_prepare_makes_two_unverified_lean_sources(self):
        plan = v2.prepare(ROOT, self.state, DAY, HEAD, self.folder / "cycle")
        self.assertTrue(plan["candidate"])
        names = {plan["baseline"]["model"]["name"],
                 plan["candidate_model"]["model"]["name"]}
        self.assertEqual(len(list((self.folder / "cycle/requests").glob("*.json"))), 2)
        manifest = v2.read(self.folder / "cycle/proof/manifest.json")
        self.assertEqual(set(manifest["models"]), names)
        self.assertFalse(manifest["passed"])
        for name in names:
            record = v2.read(self.folder / f"cycle/proof/{name}.json")
            self.assertFalse(record["kernel_verified"])
            self.assertEqual(record["status"], "PENDING_KERNEL_VERIFICATION")
        with self.assertRaises(ValueError):
            v2.receipt(ROOT, self.state, DAY, HEAD, self.folder / "cycle",
                       self.folder / "updated.json")

    def test_plan_needs_valid_date_and_exact_source(self):
        with self.assertRaises(ValueError):
            v2.plan(ROOT, v2.empty_state(), "2026-02-30", HEAD)
        with self.assertRaises(ValueError):
            v2.plan(ROOT, v2.empty_state(), DAY, "short")

    def test_untrusted_state_cannot_self_assert_verification(self):
        v2.validate_state(ROOT, v2.empty_state())
        forged = v2.empty_state()
        forged["legacy_sha256"] = v2.legacy(ROOT)[0]
        forged["last_utc_day"] = DAY
        forged["cycles"] = [{"status": v2.STATUS}]
        with self.assertRaises(ValueError):
            v2.validate_state(ROOT, forged)

    def test_legacy_source_hash_must_match(self):
        target = self.folder / "repo"
        (target / "docs/autonomy").mkdir(parents=True)
        (target / "linear_input/lean_check").mkdir(parents=True)
        src = ROOT / "docs/autonomy/ledger.json"
        (target / "docs/autonomy/ledger.json").write_bytes(src.read_bytes())
        data = json.loads(src.read_text())
        for row in data["cycles"]:
            p = row["source"]
            (target / p).write_bytes((ROOT / p).read_bytes())
        self.assertEqual(v2.legacy(target)[0], v2.legacy(ROOT)[0])
        p = target / data["cycles"][0]["source"]
        p.write_text(p.read_text() + "\n-- modified", encoding="utf-8")
        with self.assertRaises(ValueError):
            v2.legacy(target)

    def test_feedback_policy_reacts_to_verified_outcomes(self):
        seed_sha, seen = v2.legacy(ROOT)
        options = v2.catalog(seen)
        first, first_reward = v2.choose(options, [])
        _, _, _, result = v2.model_pair(first)
        record = {"spec": first, "outcome": result["kind"], "word": result.get("word")}
        next_spec, next_reward = v2.choose(options, [record])
        self.assertNotEqual(v2.spec_id(first), v2.spec_id(next_spec))
        self.assertGreaterEqual(first_reward, 0)
        self.assertGreaterEqual(next_reward, 0)
        self.assertIn(next_spec, options)

    def test_state_and_receipt_reject_tampered_plan(self):
        v2.prepare(ROOT, self.state, DAY, HEAD, self.folder / "cycle")
        planfile = self.folder / "cycle/plan.json"
        plan = v2.read(planfile)
        plan["novelty"] += 999
        v2.save(planfile, plan)
        with self.assertRaisesRegex(ValueError, "tampered proposal"):
            v2.receipt(ROOT, self.state, DAY, HEAD, self.folder / "cycle",
                       self.folder / "verified.json")

    def test_no_same_day_duplicate_after_verified_feedback(self):
        evidence = self.folder / "cycle"
        plan = v2.prepare(ROOT, self.state, DAY, HEAD, evidence)
        # An injected "success" flag is NOT accepted without a full audited
        # source/axiom record. Do not pretend to run Lean in unit tests.
        record = {"schema_version": 1, "checkout_sha": HEAD,
                  "models": [plan["baseline"]["model"]["name"],
                             plan["candidate_model"]["model"]["name"]],
                  "passed": True}
        v2.save(evidence / "proof/manifest.json", record)
        with self.assertRaises(ValueError):
            v2.receipt(ROOT, self.state, DAY, HEAD, evidence,
                       self.folder / "result.json")

    def test_duplicate_json_fields_fail_closed(self):
        self.state.write_text(
            '{"schema_version":1,"schema_version":2}', encoding="utf-8")
        with self.assertRaises(ValueError):
            v2.plan(ROOT, v2.read(self.state), DAY, HEAD)


if __name__ == "__main__":
    unittest.main()
