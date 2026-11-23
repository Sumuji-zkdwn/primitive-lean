"""Adversarial finite definition synthesis and source-bound feedback tests.

Synthetic Lean logs here exercise receipt *plumbing* only. The real GitHub
workflow compiles the actual generated semantic and finite Lean theorems.
"""
from __future__ import annotations

from copy import deepcopy
from pathlib import Path
import tempfile
import unittest

from tools.autonomy import definition_foundry as foundry
from tools.autonomy import finite_discovery as fd
from tools.autonomy import proof_forge as pf
from tools.autonomy import research_conveyor_routes as routes

ROOT = Path(__file__).resolve().parents[1]
HEAD = "e" * 40
FINITE = ROOT / "tests/fixtures/definition_foundry_finite.json"
STRATEGY = ROOT / "tests/fixtures/definition_foundry_strategy.json"


def synthetic_logs(cycle):
    """Unit-test dummy; this cannot be substituted for actual kernel success."""
    proof = cycle / "proof"
    manifest = foundry.load(proof / "manifest.json")
    for name in manifest["models"]:
        record = foundry.load(proof / (name + ".json"))
        (proof / (name + ".log")).write_text(
            "\n".join("'" + t + "' does not depend on any axioms"
                      for t in record["theorems"]) + "\n", "utf-8")
        (proof / (name + ".exit")).write_text("0\n", "utf-8")
    (cycle / "semantics.log").write_text(
        "'DefinitionFoundry.expression_matches_entire_table' "
        "does not depend on any axioms\n", "utf-8")
    (cycle / "semantics.exit").write_text("0\n", "utf-8")
    assert pf.audit(proof) == 0


class DefinitionFoundryTests(unittest.TestCase):
    def test_actual_parent_ledgers_are_verified(self):
        finite = foundry.load(FINITE)
        strategy = foundry.load(STRATEGY)
        fd.validate_state(ROOT, finite)
        foundry.strategies.validate_state(ROOT, strategy)
        catalog, roots = foundry.active_roots(
            ROOT, finite, strategy, foundry.empty_state())
        self.assertEqual(catalog, finite["catalog_sha256"])
        self.assertGreaterEqual(len(roots), 6)
        self.assertTrue(any(x["source_id"].startswith("finite:") for x in roots))
        self.assertTrue(any(x["source_id"].startswith("strategy:") for x in roots))

    def test_expression_type_checker_rejects_user_programs(self):
        base = fd.rename_model(routes.observer_model(ROOT, "observer_primitive"))
        bad = [
            {"op": "__import__", "arg": {"op": "read"}},
            {"op": "read", "execute": "rm -rf /"},
            {"op": "after", "action": 99, "arg": {"op": "read"}},
            {"op": "after", "action": True, "arg": {"op": "read"}},
            {"op": "xor", "left": {"op": "read"}, "right": {"op": "read"}},
            {"op": "pair", "left": {"op": "read"}, "right": {"op": "read"}},
            {"op": "bit", "label": -1, "arg": {"op": "read"}},
            {"op": "after", "action": 0,
             "arg": {"op": "after", "action": 0,
                     "arg": {"op": "after", "action": 0,
                             "arg": {"op": "after", "action": 0,
                                     "arg": {"op": "read"}}}}},
        ]
        for example in bad:
            with self.subTest(example=example):
                with self.assertRaises(ValueError):
                    foundry.derived_model(base, example)

    def test_semantic_lookahead_can_change_shortest_distinction(self):
        base = fd.rename_model(routes.observer_model(ROOT, "observer_primitive"))
        expression = {"op": "after", "action": 0,
                      "arg": {"op": "after", "action": 0,
                              "arg": {"op": "read"}}}
        target = foundry.derived_model(base, expression)
        self.assertEqual(base["observations"], [0, 0, 0, 1])
        self.assertEqual(target["observations"], [0, 1, 1, 1])
        self.assertEqual(foundry.checked(base)["word"], [0,0])
        self.assertEqual(foundry.checked(target)["word"], [])
        self.assertIn("expression_matches_entire_table",
                      foundry.semantics_source(base, expression, target))
        criterion = {"metric": "minimum_depth", "direction": "decrease"}
        info = foundry.objective_result(base, target, criterion)
        self.assertEqual(info["value"], -2)
        self.assertEqual(info["score"], 8)

    def test_boolean_and_pair_observations_have_explicit_integer_meaning(self):
        base = fd.rename_model(routes.observer_model(ROOT, "observer_primitive"))
        first = {"op": "bit", "label": 1, "arg": {"op": "read"}}
        shifted = {"op": "bit", "label": 1,
                   "arg": {"op": "after", "action": 0, "arg": {"op": "read"}}}
        expr = {"op": "pair", "left": first, "right": shifted}
        target = foundry.derived_model(base, expr)
        self.assertEqual(target["observations"], [0,0,2,3])
        self.assertEqual(foundry.expr_shape(expr, 1)[0], "color")
        self.assertTrue(all(0 <= x <= 3 for x in target["observations"]))
        xor = {"op": "xor", "left": first, "right": shifted}
        self.assertEqual(foundry.derived_model(base, xor)["observations"],
                         [0,0,1,0])

    def test_global_partition_agrees_with_all_pair_product_search(self):
        models = [
            fd.rename_model(routes.observer_model(ROOT, "observer_hidden")),
            fd.rename_model(routes.laakso_model("laakso_w1_advance")),
            fd.rename_model(routes.observer_model(ROOT, "observer_primitive")),
        ]
        for model in models:
            self.assertEqual(foundry.global_pairs(model),
                             foundry.verify_global_pairs(model))

    def test_planning_is_reproducible_and_criterion_is_typed(self):
        state = foundry.empty_state()
        finite = foundry.load(FINITE)
        strategy = foundry.load(STRATEGY)
        a = foundry.plan(ROOT, finite, strategy, state, HEAD, "2026-11-23")
        b = foundry.plan(ROOT, finite, strategy, state, HEAD, "2026-11-23")
        self.assertEqual(a, b)
        self.assertTrue(a["candidate"])
        self.assertGreater(a["score"], 0)
        self.assertEqual(a["proof_status"], "PENDING_KERNEL_VERIFICATION")
        self.assertIn((a["criterion"]["metric"], a["criterion"]["direction"]),
                      foundry.CRITERIA)
        self.assertNotEqual(a["base_model"]["name"], a["derived_model"]["name"])
        with self.assertRaisesRegex(ValueError, "criterion"):
            foundry.objective_result(a["base_model"], a["derived_model"],
                                     {"metric": "eval", "direction": "arbitrary"})

    def test_receipt_requires_three_real_proofs_and_binds_upstream(self):
        with tempfile.TemporaryDirectory() as temp:
            folder = Path(temp)
            state = folder / "state.json"
            foundry.save(state, foundry.empty_state())
            evidence = folder / "cycle"
            obj = foundry.prepare(ROOT, FINITE, STRATEGY, state,
                                  HEAD, "2026-11-23", evidence)
            with self.assertRaises(ValueError):
                foundry.receipt(ROOT, FINITE, STRATEGY, state, HEAD,
                                evidence, folder / "not-accepted.json")
            self.assertFalse((folder / "not-accepted.json").exists())
            synthetic_logs(evidence)
            entry = foundry.receipt(ROOT, FINITE, STRATEGY, state, HEAD,
                                    evidence, folder / "accepted.json")
            verified = foundry.validate_state(
                ROOT, foundry.load(folder / "accepted.json"))
            self.assertEqual(len(verified["receipts"]), 1)
            self.assertEqual(verified["receipts"][0]["id"], entry["id"])
            self.assertEqual(entry["status"], foundry.STATUS)
            self.assertFalse(foundry.plan(ROOT, foundry.load(FINITE),
                             foundry.load(STRATEGY), verified,
                             HEAD, "2026-11-23")["candidate"])
            second = foundry.plan(ROOT, foundry.load(FINITE),
                                  foundry.load(STRATEGY), verified,
                                  HEAD, "2026-11-24")
            self.assertTrue(second["candidate"])
            self.assertNotEqual(obj["id"], second["id"])

    def test_semantics_or_criterion_tampering_fails_closed(self):
        with tempfile.TemporaryDirectory() as temp:
            folder = Path(temp)
            state = folder / "state.json"
            foundry.save(state, foundry.empty_state())
            cycle = folder / "cycle"
            original = foundry.prepare(ROOT, FINITE, STRATEGY, state,
                                       HEAD, "2026-11-23", cycle)
            synthetic_logs(cycle)
            wrong = deepcopy(original)
            wrong["criterion"] = {"metric": "readout_colors",
                                  "direction": "decrease"}
            foundry.save(cycle / "plan.json", wrong)
            with self.assertRaisesRegex(ValueError, "plan|upstream"):
                foundry.receipt(ROOT, FINITE, STRATEGY, state, HEAD,
                                cycle, folder / "wrong.json")
            foundry.save(cycle / "plan.json", original)
            lean = cycle / "semantics.lean"
            lean.write_bytes(lean.read_bytes() + b"\n-- unexpected edit\n")
            with self.assertRaisesRegex(ValueError, "semantics source"):
                foundry.receipt(ROOT, FINITE, STRATEGY, state, HEAD,
                                cycle, folder / "wrong2.json")

    def test_source_ledger_and_date_controls(self):
        with tempfile.TemporaryDirectory() as temp:
            state = Path(temp) / "empty.json"
            foundry.save(state, foundry.empty_state())
            obj = foundry.load(STRATEGY)
            obj["receipts"][0]["score"] = 10000
            modified = Path(temp) / "strategy.json"
            foundry.save(modified, obj)
            with self.assertRaises(ValueError):
                foundry.prepare(ROOT, FINITE, modified, state,
                                HEAD, "2026-11-23", Path(temp) / "trial")
        with self.assertRaises(ValueError):
            foundry.check_day("2026-02-30")

    def test_bounded_candidate_grammar(self):
        model = fd.rename_model(routes.observer_model(ROOT, "observer_primitive"))
        xs = foundry.expression_candidates(model)
        self.assertTrue(xs)
        self.assertLess(len(xs), 50)
        for expr in xs:
            foundry.expr_shape(expr, 1)
            target = foundry.derived_model(model, expr)
            self.assertEqual(target["name"], fd.rename_model(target)["name"])


if __name__ == "__main__":
    unittest.main()
