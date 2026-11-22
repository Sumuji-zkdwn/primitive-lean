"""Bounded self-directed finite discovery, provenance, and fail-closed tests.

Some tests supply synthetic Lean logs to test *receipt validation logic*.
Only the separately executed Actions job compiles real Lean with --trust=0.
"""
from __future__ import annotations

from copy import deepcopy
from datetime import date, timedelta
from pathlib import Path
import tempfile
import unittest

from tools.autonomy import finite_discovery as engine
from tools.autonomy import proof_forge as pf
from tools.autonomy import research_conveyor_routes as routes

ROOT = Path(__file__).resolve().parents[1]
HEAD = "b" * 40


def simulate_kernel_receipt(root, working, state_file, day):
    """Controlled test stub for state transitions, never a proof claim."""
    trial = root / ("trial_" + day)
    plan = engine.prepare(working, state_file, HEAD, day, trial)
    if not plan["candidate"]:
        return None
    proof = trial / "proof"
    record = engine.load(proof / (plan["model"]["name"] + ".json"))
    name = plan["model"]["name"]
    (proof / (name + ".exit")).write_text("0\n", encoding="utf-8")
    (proof / (name + ".log")).write_text(
        "\n".join("'" + theorem + "' does not depend on any axioms"
                  for theorem in record["theorems"]) + "\n", encoding="utf-8")
    assert pf.audit(proof) == 0
    next_file = root / ("state_" + day + ".json")
    entry = engine.receipt(working, state_file, HEAD, trial, next_file)
    return entry, next_file, plan


class DiscoveryTests(unittest.TestCase):
    def test_four_reviewed_seeds_are_pinned_to_real_repo_sources(self):
        catalog, cases = engine.seeds(ROOT)
        self.assertRegex(catalog, r"^[0-9a-f]{64}$")
        self.assertEqual([x["seed"] for x in cases], list(engine.SEED_ORDER))
        self.assertEqual(len({x["model"]["name"] for x in cases}), 4)
        for item in cases:
            engine.validate_model(item["model"])
            solved = pf.solve(item["model"])
            pf.validate_result(item["model"], solved)
        self.assertEqual(pf.solve(cases[0]["model"])["word"], [0, 0])
        self.assertEqual(pf.solve(cases[2]["model"])["kind"], "EQUIVALENT")
        self.assertEqual(pf.solve(cases[3]["model"])["kind"], "EQUIVALENT")

    def test_first_plan_and_replay_are_deterministic(self):
        state = engine.empty_state()
        obj = engine.plan(ROOT, state, HEAD, "2026-11-23")
        self.assertTrue(obj["candidate"])
        self.assertEqual(obj["seed"], "observer")
        self.assertEqual(obj["mutation"], "reviewed_seed")
        self.assertEqual(obj["depth"], 0)
        self.assertEqual(obj["python_observation"]["proof_status"],
                         "PENDING_KERNEL_VERIFICATION")
        self.assertEqual(obj, engine.plan(ROOT, state, HEAD, "2026-11-23"))

    def test_automatically_evolves_models_from_certified_result(self):
        old, _ = engine.seeds(ROOT)
        self.assertRegex(old, r"^[a-f0-9]{64}$")
        model = routes.observer_model(ROOT, "observer_primitive")
        model = engine.rename_model(model)
        edits = list(engine.mutate(model, "DISTINGUISHABLE"))
        names = [name for name, _ in edits]
        self.assertIn("compose_first_action", names)
        self.assertIn("forget_last_observation", names)
        self.assertIn("perturb_one_transition", names)
        candidate = dict(edits)["compose_first_action"]
        candidate = engine.rename_model(candidate)
        engine.validate_model(candidate)
        self.assertEqual(pf.solve(candidate)["word"], [1])

    def test_an_equivalent_pair_generates_refutation_and_new_observation(self):
        seed = routes.observer_model(ROOT, "observer_hidden")
        seed = engine.rename_model(seed)
        self.assertEqual(pf.solve(seed)["kind"], "EQUIVALENT")
        proposals = dict(engine.mutate(seed, "EQUIVALENT"))
        self.assertIn("split_hidden_readout", proposals)
        self.assertIn("append_distinguishing_probe", proposals)
        self.assertIn("adjoin_absorbing_state", proposals)
        update = engine.rename_model(proposals["split_hidden_readout"])
        self.assertEqual(pf.solve(update)["word"], [])
        for name, m in proposals.items():
            m = engine.rename_model(m)
            engine.validate_model(m)
            pf.validate_result(m, pf.solve(m))

    def test_predictive_bisimulation_quotient_is_a_proper_machine(self):
        model = engine.rename_model(routes.observer_model(ROOT, "observer_hidden"))
        classes = engine.observational_partition(model)
        self.assertEqual(len(classes), 8)
        self.assertEqual(classes, [0, 1, 2, 3, 0, 1, 2, 3])
        q = engine.quotient(model)
        self.assertEqual(len(q["observations"]), 4)
        self.assertEqual(q["pair"], [0, 0])
        q = engine.rename_model(q)
        engine.validate_model(q)
        self.assertEqual(pf.solve(q)["kind"], "EQUIVALENT")
        for i in range(8):
            for j in range(8):
                a = dict(model, pair=[i, j])
                self.assertEqual(pf.solve(a)["kind"] == "EQUIVALENT",
                                 classes[i] == classes[j])

    def test_ledger_is_append_only_and_chained(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            original = root / "original.json"
            engine.save(original, engine.empty_state())
            first = simulate_kernel_receipt(root, ROOT, original, "2026-11-23")
            self.assertIsNotNone(first)
            entry, state_file, obj = first
            self.assertEqual(obj["seed"], "observer")
            self.assertEqual(entry["status"], engine.STATUS)
            self.assertEqual(entry["outcome"], "DISTINGUISHABLE")
            self.assertEqual(entry["word"], [0, 0])
            updated = engine.validate_state(ROOT, engine.load(state_file))
            self.assertEqual(len(updated["receipts"]), 1)
            self.assertEqual(updated["receipts"][0]["previous_sha256"], "0" * 64)
            second = simulate_kernel_receipt(root, ROOT, state_file, "2026-11-24")
            self.assertIsNotNone(second)
            second_entry, second_state, plan = second
            self.assertEqual(plan["seed"], "laakso")
            self.assertEqual(len(engine.load(second_state)["receipts"]), 2)
            tampered = engine.load(second_state)
            tampered["receipts"][0]["outcome"] = "EQUIVALENT"
            with self.assertRaises(ValueError):
                engine.validate_state(ROOT, tampered)

    def test_state_never_advances_without_real_kernel_audit(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            state_file = base / "empty.json"
            engine.save(state_file, engine.empty_state())
            out = base / "prepared"
            engine.prepare(ROOT, state_file, HEAD, "2026-11-23", out)
            with self.assertRaisesRegex(ValueError, "kernel evidence|manifest"):
                engine.receipt(ROOT, state_file, HEAD, out, base / "not-saved.json")
            self.assertEqual(engine.load(state_file), engine.empty_state())

    def test_duplicate_day_or_expired_budget_does_not_create_another_proof(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            state_file = base / "empty.json"
            engine.save(state_file, engine.empty_state())
            first = simulate_kernel_receipt(base, ROOT, state_file, "2026-11-23")
            state = engine.load(first[1])
            result = engine.plan(ROOT, state, HEAD, "2026-11-23")
            self.assertFalse(result["candidate"])
            self.assertEqual(result["reason"], "ALREADY_VERIFIED_TODAY")
            with self.assertRaisesRegex(ValueError, "older"):
                engine.plan(ROOT, state, HEAD, "2026-11-22")

    def test_untrusted_state_or_unsupported_claim_fails_closed(self):
        actual = engine.empty_state()
        actual["catalog_sha256"] = "d"*64
        with self.assertRaisesRegex(ValueError, "catalog"):
            engine.validate_state(ROOT, actual)
        with self.assertRaises(ValueError):
            engine.validate_model({"schema_version":1,
                                   "name":"arbitrary_python_code",
                                   "observations":[0,0],
                                   "transitions":[[0,1]],
                                   "pair":[0,1]})
        with self.assertRaisesRegex(ValueError, "input bound|regular file"):
            engine.load(Path("/nonexistent/discovery-state.json"))
        with self.assertRaises(ValueError):
            engine.utc_day("2026-02-30")

    def test_output_is_replayable_and_mutations_are_bounded(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            state = base / "seed.json"
            engine.save(state, engine.empty_state())
            a = engine.prepare(ROOT, state, HEAD, "2026-11-23", base / "a")
            b = engine.prepare(ROOT, state, HEAD, "2026-11-23", base / "b")
            self.assertEqual(a, b)
            name = a["model"]["name"]
            self.assertEqual((base/"a/requests"/(name+".json")).read_bytes(),
                             (base/"b/requests"/(name+".json")).read_bytes())
            self.assertEqual((base/"a/proof"/(name+".lean")).read_bytes(),
                             (base/"b/proof"/(name+".lean")).read_bytes())
            variants = list(engine.mutate(a["model"], "DISTINGUISHABLE"))
            self.assertLessEqual(len(variants), 8)


if __name__ == "__main__":
    unittest.main()
