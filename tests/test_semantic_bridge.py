"""Independent bridge regression: actual stored Generic/Semantic proofs and reuse."""
from pathlib import Path
from tempfile import TemporaryDirectory
import copy
import json
import unittest

from tools.autonomy import generic_forge as gf
from tools.autonomy import semantic_forge as sf
from tools.autonomy import semantic_bridge as bridge

ROOT = Path(__file__).resolve().parents[1]
G = ROOT / "tests/fixtures/semantic_bridge_generic.json"
S = ROOT / "tests/fixtures/semantic_bridge_semantic.json"
HEAD = "a" * 40


class SemanticBridgeTests(unittest.TestCase):
    def setUp(self):
        self.folder = TemporaryDirectory()
        self.addCleanup(self.folder.cleanup)
        self.root = Path(self.folder.name)
        self.g = bridge.read(G)
        self.s = bridge.read(S)
        self.state = self.root / "state.json"
        bridge.write(self.state, bridge.empty_state())

    def one(self, day, count):
        evidence = self.root / f"cycle-{count}"
        proposal = bridge.prepare(G, S, self.state, HEAD, day, evidence)
        self.assertTrue(proposal["candidate"])
        updated = bridge.seal(G, S, self.state, HEAD, evidence,
                              self.root / f"verified-{count}.json")
        bridge.write(self.state, updated)
        return proposal, updated

    def test_both_upstream_ancestries_are_actually_certified(self):
        gmap, smap = bridge.checked_upstream(self.g, self.s)
        self.assertEqual(len(gmap), 3)
        self.assertEqual(len(smap), 1)
        self.assertIn("gf_198afad7a91bc9a2", gmap)
        self.assertIn("sf_43ed97b6ef1909a1", smap)
        self.assertTrue(sf.primitive_closure_invariant()["independent_base_checks"] == 24)

    def test_hybrid_operators_reuse_real_verified_ancestry(self):
        gmap, smap = bridge.checked_upstream(self.g, self.s)
        g = {"kind": "generic", "id": "gf_198afad7a91bc9a2"}
        s = {"kind": "semantic", "id": "sf_43ed97b6ef1909a1"}
        for flat in ([g, s], [s, g]):
            with self.subTest(flat=flat):
                behavior = bridge.evaluate(flat, gmap, smap)
                self.assertIsNotNone(behavior)
                self.assertEqual(behavior["exhaustive_inputs"], 256)
                self.assertTrue(behavior["old_primitive_closure_excluded"])
                self.assertEqual(len(set(behavior["four_position_outputs"])), 4)
                witness = behavior["constant_counterexample"]
                self.assertEqual(len(set(witness["input_values"])), 1)
                self.assertGreater(len(set(witness["output_values"])), 1)
                for value in range(256):
                    a = bridge.execute(flat, value, "readable", gmap, smap)
                    b = bridge.execute(flat, value, "packed", gmap, smap)
                    self.assertEqual(a, b)

    def test_multiple_generations_and_parented_hybrid_reentry(self):
        first, state1 = self.one("2026-11-24", 1)
        self.assertIsNone(first["proposal"]["parent"])
        self.assertEqual(len(state1["receipts"]), 1)
        second, state2 = self.one("2026-11-25", 2)
        self.assertEqual(second["proposal"]["parent"], first["proposal"]["id"])
        self.assertIn("bridge", [token["kind"] for token in
                                 second["proposal"]["recipe"]])
        self.assertEqual(len(state2["receipts"]), 2)
        self.assertEqual(bridge.validate_state(state2, self.g, self.s), state2)
        self.assertEqual(len({r["behavior"]["behavior_sha256"]
                              for r in state2["receipts"]}), 2)

    def test_verified_hybrid_is_an_actual_runnable_tool(self):
        _, state = self.one("2026-11-24", 1)
        name = state["receipts"][0]["id"]
        result = bridge.use(self.g, self.s, state, name, [0, 3, 1, 2])
        self.assertEqual(result["operator_id"], name)
        self.assertEqual(len(result["output"]), 4)
        self.assertTrue(result["old_primitive_closure_excluded"])
        with self.assertRaises(ValueError):
            bridge.use(self.g, self.s, state,
                       "sb_0000000000000000", [0, 3, 1, 2])
        with self.assertRaises(ValueError):
            bridge.use(self.g, self.s, state, name, [0, 0, 0, 4])

    def test_upstream_tampering_refused(self):
        fake_g = copy.deepcopy(self.g)
        fake_g["receipts"][1]["program"] = ["clip_top"]
        with self.assertRaises(ValueError):
            bridge.checked_upstream(fake_g, self.s)
        fake_s = copy.deepcopy(self.s)
        fake_s["receipts"][0]["observation"]["behavior_sha256"] = "0" * 64
        with self.assertRaises(ValueError):
            bridge.checked_upstream(self.g, fake_s)

    def test_duplicate_and_unverified_token_fail_closed(self):
        gmap, smap = bridge.checked_upstream(self.g, self.s)
        cases = [
            [{"kind": "generic", "id": "gf_fake"},
             {"kind": "semantic", "id": "sf_43ed97b6ef1909a1"}],
            [{"kind": "generic", "id": "gf_198afad7a91bc9a2"},
             {"kind": "python", "id": "eval"}],
            [{"kind": "generic", "id": "gf_198afad7a91bc9a2"},
             {"kind": "generic", "id": "gf_3ea0ae0d3af2c7b0"}],
            [{"kind": "bridge", "id": "sb_unverified"},
             {"kind": "semantic", "id": "sf_43ed97b6ef1909a1"}],
        ]
        for recipe in cases:
            with self.subTest(recipe=recipe), self.assertRaises(ValueError):
                bridge.flatten(recipe, gmap, smap, {})

    def test_tamper_receipt_and_source_anchor_rejected(self):
        _, state = self.one("2026-11-24", 1)
        for name in ("parent", "behavior", "source", "hash", "flattened"):
            fake = copy.deepcopy(state)
            row = fake["receipts"][0]
            if name == "parent":
                row["parent"] = "sb_0000000000000000"
            elif name == "behavior":
                row["behavior"]["behavior_sha256"] = "0" * 64
            elif name == "source":
                row["source_semantic"] = "0" * 64
            elif name == "hash":
                row["chain_sha256"] = "0" * 64
            else:
                row["flattened"] = []
            with self.subTest(name=name), self.assertRaises(ValueError):
                bridge.validate_state(fake, self.g, self.s)

    def test_stale_proposal_is_not_a_verified_record(self):
        result = bridge.prepare(G, S, self.state, HEAD, "2026-11-24",
                                self.root / "proposal")
        self.assertTrue(result["candidate"])
        self.assertEqual(bridge.read(self.state)["receipts"], [])
        proposed = bridge.read(self.root / "proposal/plan.json")
        proposed["proposal"]["score"] += 3
        bridge.write(self.root / "proposal/plan.json", proposed)
        with self.assertRaisesRegex(ValueError, "stale/tampered"):
            bridge.seal(G, S, self.state, HEAD, self.root / "proposal",
                        self.root / "saved.json")

    def test_daily_limit_and_invalid_json(self):
        _, state = self.one("2026-11-24", 1)
        repeated = bridge.plan(state, self.g, self.s, "2026-11-24", HEAD)
        self.assertFalse(repeated["candidate"])
        self.assertEqual(repeated["reason"], "ALREADY_VERIFIED_TODAY")
        with self.assertRaises(ValueError):
            bridge.plan(bridge.empty_state(), self.g, self.s,
                        "2026-02-30", HEAD)
        self.state.write_text('{"schema_version":1,"schema_version":1}', "utf-8")
        with self.assertRaises(ValueError):
            bridge.read(self.state)


if __name__ == "__main__":
    unittest.main()
