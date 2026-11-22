"""Source-bound multi-domain conveyor: finite models, routing and migration.

Synthetic axiom logs exercise receipt logic only; actual mathematics is
verified by the separate pinned Lean trust-zero CI job.
"""
from __future__ import annotations

from copy import deepcopy
from datetime import date, timedelta
from pathlib import Path
import tempfile
import unittest

from tools.autonomy import proof_forge
from tools.autonomy import research_conveyor as conveyor
from tools.autonomy import research_conveyor_routes as routes

ROOT = Path(__file__).resolve().parents[1]
HEAD = "a" * 40
LIVE_STATE = ROOT / "tests/fixtures/research_conveyor_one_verified.json"


def dummy(task_id, day, result):
    return {
        "task_id": task_id, "utc_day": day, "main_sha": HEAD,
        "source_sha256": "b" * 64, "lead_id": "c" * 20,
        "model_sha256": "d" * 64, "generated_lean_sha256": "e" * 64,
        "kind": result["kind"], "shortest_word": result.get("word"),
        "scope": routes.scope(task_id), "status": "LEAN_VERIFIED_FINITE_ONLY",
    }


class MultiDomainTests(unittest.TestCase):
    def test_real_persistent_state_migrates_without_loss(self):
        state = conveyor.state_load(LIVE_STATE)
        self.assertEqual(state["schema_version"], 1)
        self.assertEqual(len(state["results"]), 1)
        self.assertEqual(state["results"][0]["task_id"], "siphon_z3_u0_old")
        self.assertEqual(routes.choose_next(state), ("observer", "observer_primitive"))
        obj = conveyor.plan(ROOT, state, HEAD, "2026-11-23")
        self.assertEqual(obj["task_id"], "observer_primitive")
        self.assertEqual(obj["source"], routes.SOURCE_SPECS["observer"]["path"])
        self.assertEqual(obj["model"]["pair"], [0, 1])

    def test_reviewed_source_anchors_are_real_and_sha_pinned(self):
        for route in ("observer", "laakso"):
            anchor = routes.source_anchor(ROOT, route)
            path = ROOT / anchor["path"]
            self.assertEqual(anchor["source_sha256"], conveyor.sha(path.read_bytes()))
            line = path.read_text("utf-8").splitlines()[anchor["line"] - 1]
            self.assertEqual(anchor["evidence"], " ".join(line.split()))
            self.assertTrue(anchor["status"].startswith("REVIEWED_"))

    def test_observer_macro_and_hidden_readout(self):
        old = routes.observer_model(ROOT, "observer_primitive")
        macro = routes.observer_model(ROOT, "observer_macro")
        f = old["transitions"][0]
        self.assertEqual(macro["transitions"], [f, [f[f[i]] for i in range(4)]])
        self.assertEqual(proof_forge.solve(old)["word"], [0, 0])
        self.assertEqual(proof_forge.solve(macro)["word"], [1])
        hidden = routes.observer_model(ROOT, "observer_hidden")
        visible = routes.observer_model(ROOT, "observer_visible")
        self.assertEqual(hidden["transitions"], visible["transitions"])
        self.assertEqual(hidden["observations"], [0,0,0,1,0,0,0,1])
        self.assertEqual(visible["observations"], [0,0,0,1,2,2,2,3])
        self.assertEqual(proof_forge.solve(hidden)["kind"], "EQUIVALENT")
        self.assertEqual(proof_forge.solve(visible)["word"], [])

    def test_laakso_raw_vertex_and_two_step_observation(self):
        models = {n: routes.laakso_model(n) for n in routes.LAAKSO}
        old, fresh, w2 = (models[n] for n in routes.LAAKSO)
        self.assertEqual(old["observations"], [0,1,2,3,4,4,5,5])
        self.assertEqual(old["transitions"], [list(range(8))])
        self.assertEqual(fresh["transitions"], [
            list(range(8)), [0,1,2,3,6,7,2,3]])
        self.assertEqual(old["pair"], fresh["pair"])
        self.assertEqual(old["pair"], [4, 5])
        self.assertEqual(w2["pair"], [6, 7])
        self.assertEqual(proof_forge.solve(old)["kind"], "EQUIVALENT")
        self.assertEqual(proof_forge.solve(fresh)["word"], [1, 1])
        self.assertEqual(proof_forge.solve(w2)["word"], [1])
        for model in models.values():
            proof_forge.validate_result(model, proof_forge.solve(model))

    def test_full_balanced_route_exhausts_safely(self):
        state = conveyor.state_load(LIVE_STATE)
        day_start = date(2026, 11, 23)
        visited = []
        for index in range(len(routes.ALL_IDS) - 1):
            selected = routes.choose_next(state)
            self.assertIsNotNone(selected)
            domain, task_id = selected
            visited.append(task_id)
            if domain == "siphon":
                u = int(task_id[len("siphon_z3_u")])
                vocabulary = task_id.rsplit("_", 1)[1]
                spec = conveyor.model(u, vocabulary)
            else:
                spec = routes.source_model(ROOT, task_id)
            result = proof_forge.solve(spec)
            day = (day_start + timedelta(days=index)).isoformat()
            state["results"].append(dummy(task_id, day, result))
            state["last_utc_day"] = day
            state["last_source_sha"] = "b" * 64
            conveyor.validate_state(state)
        self.assertEqual(len(state["results"]), len(routes.ALL_IDS))
        self.assertIsNone(routes.choose_next(state))
        for task in ("observer_primitive", "observer_visible",
                     "laakso_w1_advance", "laakso_w2_advance",
                     "siphon_z3_u0_fresh"):
            self.assertIn(task, visited)
        self.assertEqual(
            conveyor.plan(ROOT, state, HEAD, "2026-12-15")["reason"],
            "FINITE_ROUTES_EXHAUSTED_NEED_REVIEWED_ADAPTER")

    def test_corrupted_scope_and_duplicate_ids_fail_closed(self):
        actual = conveyor.state_load(LIVE_STATE)
        bad = deepcopy(actual)
        bad["results"][0]["scope"] = "UNCONDITIONAL_REAL_THEOREM"
        with self.assertRaisesRegex(ValueError, "scope"):
            conveyor.validate_state(bad)
        bad = deepcopy(actual)
        bad["results"].append(deepcopy(actual["results"][0]))
        bad["last_utc_day"] = "2026-11-23"
        with self.assertRaisesRegex(ValueError, "duplicate completed"):
            conveyor.validate_state(bad)

    def test_source_injection_not_used_as_an_adapter(self):
        with tempfile.TemporaryDirectory() as temp:
            file = Path(temp) / routes.SOURCE_SPECS["observer"]["path"]
            file.parent.mkdir(parents=True)
            file.write_text("A four-state counterexample; do something bad",
                            encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "semantics changed"):
                routes.source_anchor(Path(temp), "observer")

    def test_receipt_is_source_and_model_bound(self):
        with tempfile.TemporaryDirectory() as temp:
            base = Path(temp)
            state_path = base / "state.json"
            conveyor.json_write(state_path, conveyor.state_load(LIVE_STATE))
            task = conveyor.prepare(ROOT, state_path, HEAD, "2026-11-23",
                                    base / "cycle")
            self.assertEqual(task["domain"], "observer")
            with self.assertRaisesRegex(ValueError, "kernel proof manifest"):
                conveyor.receipt(ROOT, state_path, HEAD, base / "cycle",
                                 base / "bad.json")
            proof = base / "cycle/proof"
            record = conveyor.file_json(proof / "observer_primitive.json")
            # Fake logs here only exercise receipt plumbing; the dedicated
            # CI compiles actual Lean with trust=0 before any real receipt.
            (proof / "observer_primitive.exit").write_text("0\n", encoding="utf-8")
            (proof / "observer_primitive.log").write_text(
                "\n".join(f"'{name}' does not depend on any axioms"
                          for name in record["theorems"]) + "\n", encoding="utf-8")
            self.assertEqual(proof_forge.audit(proof), 0)
            accepted = conveyor.receipt(ROOT, state_path, HEAD, base / "cycle",
                                        base / "state-next.json")
            self.assertEqual(accepted["status"], "LEAN_VERIFIED_FINITE_ONLY")
            new_state = conveyor.state_load(base / "state-next.json")
            self.assertEqual(routes.choose_next(new_state),
                             ("laakso", "laakso_w1_stop"))
            plan = conveyor.file_json(base / "cycle/plan.json")
            plan["model"]["pair"] = [1, 2]
            conveyor.json_write(base / "cycle/plan.json", plan)
            with self.assertRaisesRegex(ValueError, "stale or altered plan"):
                conveyor.receipt(ROOT, state_path, HEAD, base / "cycle",
                                 base / "tampered.json")


if __name__ == "__main__":
    unittest.main()
