"""Regression against actual certified input snapshots and independent interpreters."""
import copy
from pathlib import Path
import unittest
from unittest.mock import patch

from tools.autonomy import forge_bridge as bridge
from tools.autonomy import generic_forge as gf
from tools.autonomy import meta_forge as mf

FIXTURES = Path(__file__).parent / "fixtures"
HEAD = "a" * 40


class BridgeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.generic = gf.read(FIXTURES / "forge_bridge_generic.json")
        cls.meta = mf.load(FIXTURES / "forge_bridge_meta.json")
        cls.report = bridge.experiment(cls.generic, cls.meta, HEAD)

    def test_actual_certified_history_is_not_mutated_and_replay_is_exact(self):
        generic, meta = copy.deepcopy(self.generic), copy.deepcopy(self.meta)
        self.assertEqual(self.report, bridge.experiment(generic, meta, HEAD))
        self.assertEqual(generic, self.generic)
        self.assertEqual(meta, self.meta)
        self.assertEqual(self.report["generic_state_sha256"], gf.digest(generic))
        self.assertEqual(self.report["meta_state_sha256"], gf.digest(meta))

    def test_each_selected_operator_is_new_against_exact_pair_frontier(self):
        history = list(self.generic["receipts"])
        for result in self.report["rounds"]:
            self.assertLessEqual(result["examined"], bridge.MAX_CANDIDATES_PER_ROUND)
            row = result["selected"]
            if row is None:
                self.assertEqual(result["distinct_outside_pair_frontier"], 0)
                continue
            domain = row["domain"]
            seed = next(r for r in history if r["id"] == row["seed_id"])
            rule = next(r for r in self.meta["rules"] if r["id"] == row["rule_id"])
            self.assertEqual(row["program"], bridge.checked_rewrite(domain, rule["steps"], seed["program"]))
            self.assertEqual(row["behavior"], gf.audit(domain, tuple(row["program"])))
            self.assertNotIn(row["behavior"]["fingerprint"], bridge.pair_frontier(domain, history))
            self.assertNotIn((domain, row["behavior"]["fingerprint"]),
                             {(r["domain"], r["behavior"]["fingerprint"]) for r in history})
            history.append(row)
        self.assertLessEqual(self.report["shadow_operators"], bridge.MAX_ROUNDS)

    def test_no_inputs_no_invented_discovery(self):
        report = bridge.experiment(gf.empty_state(), mf.empty_state(), HEAD)
        self.assertEqual(report["shadow_operators"], 0)
        self.assertEqual(report["rounds"][0]["examined"], 0)

    def test_capacity_rejection_and_disagreement(self):
        domain = "grid3"
        seed = ["invert"] * gf.MAX_PROGRAM
        self.assertIsNone(bridge.checked_rewrite(domain, [{"op": "duplicate_head"}], seed))
        with patch.object(mf, "rewrite_independent", return_value=["invert"]):
            with self.assertRaisesRegex(ValueError, "disagreement"):
                bridge.checked_rewrite(domain, [{"op": "append", "slot": 0}], ["invert"])

    def test_tampered_source_and_invalid_budget_fail_closed(self):
        invalid = copy.deepcopy(self.meta)
        invalid["rules"][0]["chain_sha256"] = "0" * 64
        with self.assertRaises(ValueError):
            bridge.experiment(self.generic, invalid, HEAD)
        with self.assertRaises(ValueError):
            bridge.experiment(self.generic, self.meta, HEAD, bridge.MAX_ROUNDS + 1)


if __name__ == "__main__":
    unittest.main()
