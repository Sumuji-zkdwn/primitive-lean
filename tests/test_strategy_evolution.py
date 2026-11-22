"""Untrusted strategy state, finite DSL and dual-certificate feedback tests.

Synthetic compiler logs below check controller plumbing only. The separate
GitHub Actions job performs real --trust=0 Lean compilation before publishing.
"""
from __future__ import annotations

from copy import deepcopy
from datetime import date, timedelta
import json
from pathlib import Path
import tempfile
import unittest

from tools.autonomy import finite_discovery as fd
from tools.autonomy import proof_forge as pf
from tools.autonomy import research_conveyor_routes as routes
from tools.autonomy import strategy_evolution as meta

ROOT = Path(__file__).resolve().parents[1]
UPSTREAM = ROOT / "tests/fixtures/strategy_evolution_upstream.json"
HEAD = "d" * 40


def synthetic_dual_compiler(proof):
    """Only for test inputs; actual pipeline never manufactures fake logs."""
    manifest = meta.load(proof / "manifest.json")
    for name in manifest["models"]:
        report = meta.load(proof / (name + ".json"))
        (proof / (name + ".exit")).write_text("0\n", encoding="utf-8")
        (proof / (name + ".log")).write_text(
            "\n".join("'" + theorem + "' does not depend on any axioms"
                      for theorem in report["theorems"]) + "\n",
            encoding="utf-8")
    assert pf.audit(proof) == 0


class StrategyEvolutionTests(unittest.TestCase):
    def test_real_verified_upstream_is_replayable(self):
        upstream = meta.load(UPSTREAM)
        meta.validate_upstream(ROOT, upstream)
        self.assertEqual(len(upstream["receipts"]), 1)
        self.assertEqual(upstream["receipts"][0]["status"],
                         "LEAN_VERIFIED_FINITE_ONLY")
        self.assertEqual(upstream["receipts"][0]["word"], [0,0])
        self.assertRegex(meta.digest(upstream), r"^[0-9a-f]{64}$")
        catalog, available = meta.roots(ROOT, upstream)
        self.assertEqual(len(available), 5)
        self.assertEqual(catalog, upstream["catalog_sha256"])
        self.assertIn("finite-discovery:" + upstream["receipts"][0]["name"],
                      [x["source_id"] for x in available])

    def test_data_only_grammar_rejects_arbitrary_python(self):
        with self.assertRaisesRegex(ValueError, "unreviewed executable"):
            meta.validate_program(["import os; os.system('x')"])
        with self.assertRaisesRegex(ValueError, "length"):
            meta.validate_program(["compose_first_action"] * 4)
        with self.assertRaisesRegex(ValueError, "unreviewed executable"):
            meta.validate_program(["eval"])
        with self.assertRaisesRegex(ValueError, "length"):
            meta.validate_program([])

    def test_composition_generates_a_new_strategy_program(self):
        base = fd.rename_model(routes.observer_model(ROOT, "observer_primitive"))
        first = meta.apply_program(base, ["compose_first_action"])
        second = meta.apply_program(
            base, ["compose_first_action", "forget_last_observation"])
        self.assertEqual(pf.solve(base)["word"], [0,0])
        self.assertEqual(pf.solve(first)["word"], [1])
        self.assertEqual(pf.solve(second)["kind"], "EQUIVALENT")
        self.assertNotEqual(base["name"], second["name"])
        self.assertEqual(meta.score_models(base, first),
                         (7, "MINIMUM_NAMED_WORD_DEPTH_CHANGED"))
        self.assertEqual(meta.score_models(base, second),
                         (12, "PAIR_DISTINGUISHABILITY_FLIPPED"))
        meta.validate_program(["compose_first_action", "forget_last_observation"])

    def test_first_plan_is_deterministic_and_has_two_models(self):
        upstream = meta.load(UPSTREAM)
        state = meta.empty_state()
        plan = meta.plan(ROOT, upstream, state, HEAD, "2026-11-23")
        self.assertTrue(plan["candidate"])
        self.assertEqual(plan["proof_status"], "PENDING_KERNEL_VERIFICATION")
        self.assertEqual(len(plan["program"]), 1)
        self.assertIsNone(plan["parent_rule"])
        self.assertNotEqual(plan["root_model"]["name"], plan["model"]["name"])
        self.assertEqual(plan, meta.plan(ROOT, upstream, state, HEAD, "2026-11-23"))
        meta.solve_checked(plan["root_model"])
        meta.solve_checked(plan["model"])
        self.assertIn(plan["objective"], {
            "PAIR_DISTINGUISHABILITY_FLIPPED",
            "MINIMUM_NAMED_WORD_DEPTH_CHANGED",
            "STATE_SPACE_SIZE_CHANGED",
            "ACTION_VOCABULARY_CHANGED_NO_PAIR_FLIP",
            "PAIR_EQUIVALENCE_PRESERVED_IN_FINITE_MODEL",
            "PAIR_DISTINCTION_PRESERVED_IN_FINITE_MODEL",
        })

    def test_exact_source_and_dual_model_receipt_chain(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            original = root / "state.json"
            meta.save(original, meta.empty_state())
            evidence = root / "run"
            plan = meta.prepare(ROOT, UPSTREAM, original, HEAD, "2026-11-23", evidence)
            with self.assertRaisesRegex(ValueError, "kernel"):
                meta.receipt(ROOT, UPSTREAM, original, HEAD, evidence,
                             root / "refuse.json")
            self.assertFalse((root / "refuse.json").exists())
            manifest = meta.load(evidence / "proof/manifest.json")
            self.assertEqual(len(manifest["models"]), 2)
            synthetic_dual_compiler(evidence / "proof")
            entry = meta.receipt(ROOT, UPSTREAM, original, HEAD, evidence,
                                 root / "accepted.json")
            state = meta.validate_state(ROOT, meta.load(root / "accepted.json"))
            self.assertEqual(len(state["receipts"]), 1)
            self.assertEqual(entry["status"], meta.STATUS)
            self.assertEqual(entry["previous_sha256"], "0" * 64)
            self.assertEqual(entry["chain_sha256"], meta.digest({
                k:v for k,v in entry.items() if k != "chain_sha256"}))
            next_day = "2026-11-24"
            future = meta.plan(ROOT, meta.load(UPSTREAM), state, HEAD, next_day)
            self.assertTrue(future["candidate"])
            self.assertNotEqual(future["id"], plan["id"])
            self.assertFalse(meta.plan(ROOT, meta.load(UPSTREAM), state, HEAD,
                                       "2026-11-23")["candidate"])
            with self.assertRaisesRegex(ValueError, "older"):
                meta.plan(ROOT, meta.load(UPSTREAM), state, HEAD, "2026-11-22")

    def test_verified_parent_rule_required_for_composite(self):
        root_model = fd.rename_model(routes.observer_model(ROOT, "observer_primitive"))
        derived = meta.apply_program(
            root_model, ["compose_first_action", "forget_last_observation"])
        state = meta.empty_state()
        _, sources = meta.roots(ROOT, meta.load(UPSTREAM))
        first = sources[0]
        receipt = {
            "id": meta.strategy_id(first["source_id"],
                                   ["compose_first_action", "forget_last_observation"],
                                   fd.model_fingerprint(root_model)),
            "program": ["compose_first_action", "forget_last_observation"],
            "root_model": root_model, "model": derived,
            "parent_rule": None,
        }
        with self.assertRaises(ValueError):
            # A direct path to a composite without a previously accepted
            # single-operation proof is disallowed in the state ledger.
            meta.validate_state(ROOT, {
                "schema_version": 1,
                "catalog_sha256": meta.seeds(ROOT)[0] if hasattr(meta,"seeds") else fd.seeds(ROOT)[0],
                "last_utc_day": "2026-11-23",
                "receipts": [receipt],
            })

    def test_changed_upstream_blocks_stale_proof(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            original = base / "state.json"
            meta.save(original, meta.empty_state())
            evidence = base / "run"
            meta.prepare(ROOT, UPSTREAM, original, HEAD, "2026-11-23", evidence)
            synthetic_dual_compiler(evidence / "proof")
            upstream = meta.load(UPSTREAM)
            # Extra verified observations in a downstream branch might
            # supersede an in-flight experiment. Do not use stale ordering.
            changed = base / "changed.json"
            upstream["last_utc_day"] = "2026-11-23"
            upstream["receipts"][0]["word"] = [0]
            fd_source = upstream["receipts"][0]
            upstream["receipts"][0]["chain_sha256"] = fd.digest({
                k:v for k,v in fd_source.items() if k != "chain_sha256"})
            fd.save(changed, upstream)
            with self.assertRaises(ValueError):
                meta.receipt(ROOT, changed, original, HEAD, evidence,
                             base / "rejected.json")

    def test_file_and_hash_tampering_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            original = base / "state.json"
            meta.save(original, meta.empty_state())
            evidence = base / "run"
            plan = meta.prepare(ROOT, UPSTREAM, original, HEAD, "2026-11-23", evidence)
            synthetic_dual_compiler(evidence / "proof")
            modified = meta.load(evidence / "plan.json")
            modified["program"][0] = "execute_shell"
            meta.save(evidence / "plan.json", modified)
            with self.assertRaisesRegex(ValueError, "stale or altered"):
                meta.receipt(ROOT, UPSTREAM, original, HEAD, evidence,
                             base / "rejected.json")
            meta.save(evidence / "plan.json", plan)
            p = evidence / "proof" / (plan["model"]["name"] + ".lean")
            p.write_bytes(p.read_bytes() + b"\n-- modified after compilation\n")
            with self.assertRaisesRegex(ValueError, "kernel|Lean"):
                meta.receipt(ROOT, UPSTREAM, original, HEAD, evidence,
                             base / "rejected-again.json")

    def test_grammar_is_finite_and_quotient_has_no_false_equivalence(self):
        root = fd.rename_model(routes.observer_model(ROOT, "observer_hidden"))
        q = fd.quotient(root)
        self.assertIsNotNone(q)
        quotient = fd.rename_model(q)
        self.assertEqual(meta.solve_checked(quotient)["kind"], "EQUIVALENT")
        options = dict(fd.mutate(root, "EQUIVALENT"))
        self.assertLessEqual(len(options), len(meta.PROGRAM_OPS))
        self.assertIn("bisimulation_quotient", options)

    def test_policy_rewards_are_calculated_from_actual_pair_behavior(self):
        root = fd.rename_model(routes.observer_model(ROOT, "observer_hidden"))
        split = meta.apply_program(root, ["split_hidden_readout"])
        self.assertEqual(meta.score_models(root, split),
                         (12, "PAIR_DISTINGUISHABILITY_FLIPPED"))
        altered = meta.apply_program(root, ["adjoin_absorbing_state"])
        self.assertEqual(meta.score_models(root, altered),
                         (3, "STATE_SPACE_SIZE_CHANGED"))


if __name__ == "__main__":
    unittest.main()
