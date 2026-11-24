"""Production promotion, historic compatibility and exact replay tests."""
import copy
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest
from unittest.mock import patch

from tools.autonomy import forge_promotion as p
from tools.autonomy import forge_bridge as fb
from tools.autonomy import generic_forge as gf
from tools.autonomy import meta_forge as mf

FIXTURES = Path(__file__).parent / "fixtures"
HEAD = "a" * 40
DAY = "2026-11-24T03:30Z"


class PromotionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.state = gf.read(FIXTURES / "forge_bridge_generic.json")
        cls.meta = mf.load(FIXTURES / "forge_bridge_meta.json")
        cls.plan = p.plan(cls.state, cls.meta, DAY, HEAD)
        cls.updated = p.accept(cls.state, cls.meta, cls.plan, HEAD)

    def test_promoted_operator_enters_production_library(self):
        self.assertEqual(self.plan["route"], "meta_rule")
        row = self.updated["receipts"][-1]
        self.assertEqual(self.updated["receipts"][:-1], self.state["receipts"])
        self.assertEqual(row["origin"]["kind"], "verified_meta_rule_v1")
        self.assertNotIn(row["behavior"]["fingerprint"],
                         fb.pair_frontier(row["domain"], self.state["receipts"]))
        self.assertIn("m:" + row["id"], gf.token_lookup(row["domain"], self.updated["receipts"]))
        self.assertEqual(gf.validate_state(self.updated), self.updated)
        self.assertEqual(gf.use_operator(self.updated, row["id"], 1)["operator_id"], row["id"])

    def test_ordinary_composition_can_use_promoted_macro(self):
        row = self.updated["receipts"][-1]
        domain = row["domain"]
        registry = gf.token_lookup(domain, self.updated["receipts"], all_parents=True)
        left = "m:" + row["id"]
        known = {r["behavior"]["fingerprint"] for r in self.updated["receipts"] if r["domain"] == domain}
        candidate = None
        for right, ops in registry.items():
            program = row["program"] + ops
            if len(program) > gf.MAX_PROGRAM:
                continue
            behavior = gf.audit(domain, tuple(program))
            if behavior["fingerprint"] not in known and behavior["changed_inputs"]:
                candidate = {"domain": domain, "left": left, "right": right,
                             "program": program, "behavior": behavior,
                             "score": gf.score_candidate(domain, left, right, program,
                                                         behavior, self.updated["receipts"]),
                             "id": gf.make_id(domain, left, right, program)}
                break
        self.assertIsNotNone(candidate)
        with TemporaryDirectory() as root:
            root = Path(root)
            gf.save(root / "state.json", self.updated)
            with patch.object(gf, "choose", return_value=(candidate, 1)):
                gf.prepare(root / "state.json", "2026-11-24T04:00Z", HEAD, root / "plan")
                next_state = gf.receipt(root / "state.json", HEAD, root / "plan", root / "next.json")
            self.assertEqual(next_state["receipts"][-1]["left"], left)
            self.assertEqual(next_state["meta_snapshot"], self.meta)
            self.assertEqual(gf.validate_state(next_state), next_state)

    def test_next_slot_ordinary_and_duplicate_slot_blocked(self):
        self.assertFalse(p.plan(self.updated, self.meta, DAY, HEAD)["candidate"])
        next_plan = p.plan(self.updated, self.meta, "2026-11-24T04:00Z", HEAD)
        self.assertEqual(next_plan["route"], "composition")
        self.assertTrue(next_plan["candidate"])
        self.assertEqual(p.accept(self.updated, self.meta, next_plan, HEAD)["meta_snapshot"], self.meta)

    def test_changed_plan_rejected_and_sources_are_unchanged(self):
        before = copy.deepcopy(self.state), copy.deepcopy(self.meta)
        altered = copy.deepcopy(self.plan)
        altered["operator"]["origin"]["rule_chain_sha256"] = "0" * 64
        with self.assertRaises(ValueError):
            p.accept(self.state, self.meta, altered, HEAD)
        self.assertEqual((self.state, self.meta), before)

    def test_tampered_ancestry_rejected_even_with_rehashed_row(self):
        for field, value in (("rule_id", "mf_0000000000000000"),
                             ("rule_chain_sha256", "0" * 64)):
            corrupted = copy.deepcopy(self.updated)
            row = corrupted["receipts"][-1]
            row["origin"][field] = value
            row["chain_sha256"] = gf.digest({k: v for k, v in row.items() if k != "chain_sha256"})
            with self.subTest(field=field), self.assertRaises(ValueError):
                gf.validate_state(corrupted)

    def test_upstream_rollback_rejected(self):
        prior = {"schema_version": self.meta["schema_version"],
                 "rules": self.meta["rules"][:-1],
                 "last_utc_day": self.meta["rules"][-2]["day"]}
        mf.validate_state(prior)
        with self.assertRaisesRegex(ValueError, "not an extension"):
            p.plan(self.updated, prior, "2026-11-24T04:00Z", HEAD)

    def test_empty_and_cap_stay_bounded(self):
        self.assertEqual(p.plan(gf.empty_state(), mf.empty_state(), DAY, HEAD)["route"], "composition")
        with patch.object(gf, "MAX_RECORDS", len(self.state["receipts"])):
            self.assertEqual(p.plan(self.state, self.meta, DAY, HEAD)["reason"], "SAFETY_BUDGET_REACHED")


if __name__ == "__main__":
    unittest.main()
