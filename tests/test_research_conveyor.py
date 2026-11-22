"""Offline regression for Research Conveyor, finite task feedback, and safety.

All "certified" results in in-memory tests are synthetic; only the separate
pinned GitHub Actions Lean job is allowed to publish a real certified receipt.
"""
from __future__ import annotations

from copy import deepcopy
from datetime import date, timedelta
import json
from pathlib import Path
import tempfile
import unittest

from tools.autonomy import research_conveyor as conveyor
from tools.autonomy import proof_forge

ROOT = Path(__file__).resolve().parents[1]
HEAD = "a" * 40


def dummy_record(name, kind, index, source_sha):
    return {
        "task_id": name, "utc_day": (date(2026, 11, 1) + timedelta(days=index)).isoformat(),
        "main_sha": HEAD, "source_sha256": source_sha, "lead_id": "0" * 20,
        "model_sha256": "b" * 64, "generated_lean_sha256": "c" * 64,
        "kind": kind, "shortest_word": None if kind == "EQUIVALENT" else [1,0],
        "scope": "FINITE_Z3_MODEL_ONLY", "status": "LEAN_VERIFIED_FINITE_ONLY",
    }


class ResearchConveyorTests(unittest.TestCase):
    def test_actual_siphon_source_is_discovered_by_existing_scout(self):
        lead = conveyor.discover_lead(ROOT)
        self.assertEqual(lead["path"], conveyor.SOURCE)
        self.assertIn("未検証", lead["evidence"])
        self.assertEqual(lead["source_sha256"],
                         conveyor.sha((ROOT / conveyor.SOURCE).read_bytes()))

    def test_finite_polynomial_model_matches_equations_mod_three(self):
        for u in range(3):
            for kind in ("old", "fresh"):
                m = conveyor.model(u, kind)
                self.assertEqual(len(m["observations"]), 9)
                self.assertEqual(len(m["transitions"]), 1 if kind == "old" else 2)
                for s in range(9):
                    x, v = s % 3, s // 3
                    r = (v + x**3) % 3
                    xx = (x + r*r) % 3
                    new_v = (r - xx**3) % 3
                    self.assertEqual(m["transitions"][0][s], xx + 3*new_v)
                    self.assertEqual(m["observations"][s], x)
                    if kind == "fresh":
                        self.assertEqual(m["transitions"][1][s], x + 3*((v+1)%3))

    def test_feedback_changes_the_allowed_vocabulary(self):
        for u in range(3):
            old = conveyor.model(u, "old")
            fresh = conveyor.model(u, "fresh")
            before = proof_forge.solve(old)
            after = proof_forge.solve(fresh)
            self.assertEqual(before["kind"], "EQUIVALENT")
            self.assertEqual(after["kind"], "DISTINGUISHABLE")
            self.assertEqual(after["word"], [1, 0])
            proof_forge.validate_result(old, before)
            proof_forge.validate_result(fresh, after)

    def test_six_step_closed_feedback_loop_exhausts_safely(self):
        state = conveyor.empty_state()
        source_sha = conveyor.discover_lead(ROOT)["source_sha256"]
        for i, (u, kind) in enumerate(
            ( (0,"old"), (0,"fresh"), (1,"old"), (1,"fresh"), (2,"old"), (2,"fresh") )
        ):
            expected = f"siphon_z3_u{u}_{kind}"
            self.assertEqual(conveyor.task_sequence(state), (u, kind))
            outcome = proof_forge.solve(conveyor.model(u, kind))
            state["results"].append(dummy_record(expected, outcome["kind"], i, source_sha))
            state["last_utc_day"] = state["results"][-1]["utc_day"]
            state["last_source_sha"] = source_sha
            conveyor.validate_state(state)
        self.assertIsNone(conveyor.task_sequence(state))
        self.assertEqual(conveyor.plan(ROOT, state, HEAD, "2026-11-15")["reason"],
                         "FINITE_ROUTE_EXHAUSTED_NEEDS_NEW_REVIEWED_ADAPTER")

    def test_failure_of_old_conjecture_skips_unjustified_fresh_branch(self):
        state = conveyor.empty_state()
        source_sha = conveyor.discover_lead(ROOT)["source_sha256"]
        state["results"] = [dummy_record("siphon_z3_u0_old",
                                         "DISTINGUISHABLE", 0, source_sha)]
        state["last_utc_day"] = state["results"][0]["utc_day"]
        state["last_source_sha"] = source_sha
        self.assertEqual(conveyor.task_sequence(state), (1, "old"))

    def test_nonproof_is_not_persisted_and_same_day_restarts_are_bounded(self):
        with tempfile.TemporaryDirectory() as temp:
            folder = Path(temp)
            state_path = folder / "state.json"
            conveyor.json_write(state_path, conveyor.empty_state())
            out = folder / "first"
            task = conveyor.prepare(ROOT, state_path, HEAD, "2026-11-23", out)
            self.assertTrue(task["candidate"])
            self.assertEqual(task["python_observation"]["kind"], "EQUIVALENT")
            self.assertEqual(task["python_observation"]["proof_status"],
                             "PENDING_KERNEL_VERIFICATION")
            self.assertEqual(proof_forge.read_request(
                out / "requests" / (task["task_id"]+".json")), task["model"])
            with self.assertRaisesRegex(ValueError, "kernel proof manifest"):
                conveyor.receipt(ROOT, state_path, HEAD, out, folder / "receipt.json")
            self.assertEqual(conveyor.state_load(state_path), conveyor.empty_state())
            with self.assertRaisesRegex(ValueError, "initially empty"):
                conveyor.prepare(ROOT, state_path, HEAD, "2026-11-23", out)

    def test_rejects_tampering_old_source_and_fake_verification(self):
        with tempfile.TemporaryDirectory() as temp:
            folder = Path(temp)
            (folder / "docs/research").mkdir(parents=True)
            (folder / conveyor.SOURCE).write_text("未検証: arbitrary instruction", "utf-8")
            with self.assertRaisesRegex(ValueError, "semantics changed"):
                conveyor.discover_lead(folder)
            state = conveyor.empty_state()
            with self.assertRaisesRegex(ValueError, "invalid result id"):
                bad = deepcopy(state)
                bad["results"] = [dummy_record("cat", "EQUIVALENT", 0, "a"*64)]
                conveyor.validate_state(bad)

    def test_utc_day_and_unverified_state_rejected(self):
        for bad in ("2026-02-30", "2026/11/23", "2026-11-23Z"):
            with self.assertRaises(ValueError):
                conveyor.validate_day(bad)
        state = conveyor.empty_state()
        state["last_utc_day"] = "2026-11-23"
        with self.assertRaisesRegex(ValueError, "empty state"):
            conveyor.validate_state(state)

    def test_generated_models_are_repeatable_for_identical_source(self):
        with tempfile.TemporaryDirectory() as temp:
            folder = Path(temp)
            state = folder / "state.json"
            conveyor.json_write(state, conveyor.empty_state())
            a = conveyor.prepare(ROOT, state, HEAD, "2026-11-23", folder / "a")
            b = conveyor.prepare(ROOT, state, HEAD, "2026-11-23", folder / "b")
            self.assertEqual(a, b)
            self.assertEqual(
                (folder / "a/requests/siphon_z3_u0_old.json").read_bytes(),
                (folder / "b/requests/siphon_z3_u0_old.json").read_bytes())
            self.assertEqual(
                (folder / "a/proof/siphon_z3_u0_old.lean").read_bytes(),
                (folder / "b/proof/siphon_z3_u0_old.lean").read_bytes())


if __name__ == "__main__":
    unittest.main()
