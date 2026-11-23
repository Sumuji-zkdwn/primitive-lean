"""Cross-domain self-extension tests. These never claim a Lean theorem."""
from pathlib import Path
from tempfile import TemporaryDirectory
import copy
import json
import unittest

from tools.autonomy import generic_forge as forge

HEAD = "a" * 40


class GenericForgeTests(unittest.TestCase):
    def setUp(self):
        self.tmp = TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.path = self.root / "state.json"
        forge.save(self.path, forge.empty_state())

    def run_cycle(self, day, index):
        folder = self.root / f"cycle-{index}"
        candidate = forge.prepare(self.path, day, HEAD, folder)
        self.assertTrue(candidate["candidate"])
        updated = forge.receipt(self.path, HEAD, folder,
                                self.root / f"updated-{index}.json")
        forge.save(self.path, updated)
        return updated, candidate

    def test_primitive_reference_and_bitpacked_agree_everywhere(self):
        for domain, ops in forge.DOMAINS.items():
            with self.subTest(domain=domain):
                n = forge.DOMAIN_SIZE[domain]
                for name in ops:
                    report = forge.audit(domain, (name,))
                    self.assertEqual(report["inputs_exhaustively_checked"], n)
                    self.assertGreater(report["distinct_outputs"], 0)
                    self.assertEqual(len(report["fingerprint"]), 64)

    def test_image_transform_and_signal_samples(self):
        self.assertEqual(forge.reference_primitive("grid3", "rotate_cw", 1), 4)
        self.assertEqual(forge.reference_primitive("grid3", "invert", 0), 511)
        self.assertEqual(forge.reference_primitive("grid3", "shift_right", 1), 2)
        signal = forge.encoded("signal4", [0, 1, 2, 3])
        self.assertEqual(forge.digits("signal4", signal), [0, 1, 2, 3])
        self.assertEqual(forge.digits("signal4", forge.reference_primitive(
            "signal4", "reverse", signal)), [3, 2, 1, 0])
        self.assertEqual(forge.digits("signal4", forge.reference_primitive(
            "signal4", "add_one", signal)), [1, 2, 3, 0])

    def test_end_to_end_two_domains_and_verified_reuse(self):
        first, plan_a = self.run_cycle("2026-11-24", 1)
        second, plan_b = self.run_cycle("2026-11-25", 2)
        self.assertEqual(len(first["receipts"]), 1)
        self.assertEqual(len(second["receipts"]), 2)
        self.assertNotEqual(plan_a["operator"]["domain"], plan_b["operator"]["domain"])
        self.assertEqual({r["domain"] for r in second["receipts"]},
                         set(forge.DOMAINS))
        self.assertEqual(forge.validate_state(second), second)
        domain = plan_a["operator"]["domain"]
        registry = forge.token_lookup(domain, second["receipts"])
        self.assertIn("m:" + first["receipts"][0]["id"], registry)
        macro = registry["m:" + first["receipts"][0]["id"]]
        self.assertGreater(len(macro), 1)
        # Third run can select new operators using previous verified macros.
        third, plan_c = self.run_cycle("2026-11-26", 3)
        self.assertIn(plan_c["operator"]["domain"], forge.DOMAINS)
        self.assertTrue(plan_c["operator"]["left"].startswith("m:")
                        or plan_c["operator"]["right"].startswith("m:"))
        self.assertEqual(len(third["receipts"]), 3)
        self.assertEqual(forge.validate_state(third), third)

    def test_certified_operator_is_a_usable_image_or_signal_tool(self):
        state, _ = self.run_cycle("2026-11-24", 1)
        row = state["receipts"][0]
        output = forge.use_operator(state, row["id"], 1)
        self.assertEqual(output["operator_id"], row["id"])
        self.assertEqual(output["domain"], row["domain"])
        self.assertEqual(output["verified_by"], forge.EVALUATOR)
        self.assertEqual(output["output"],
                         forge.apply_program(row["domain"], row["program"],
                                             1, forge.independent_primitive))
        if row["domain"] == "grid3":
            self.assertEqual(len(output["output_view"]), 3)
            self.assertTrue(all(len(line) == 3 for line in output["output_view"]))
        with self.assertRaises(ValueError):
            forge.use_operator(state, "gf_0000000000000000", 1)
        with self.assertRaises(ValueError):
            forge.use_operator(state, row["id"], 9999)

    def test_only_daily_verified_receipt_and_source_bound(self):
        state, _ = self.run_cycle("2026-11-24", 1)
        duplicate = forge.plan(state, "2026-11-24", HEAD)
        self.assertFalse(duplicate["candidate"])
        self.assertEqual(duplicate["reason"], "ALREADY_CERTIFIED_TODAY")
        with self.assertRaises(ValueError):
            forge.receipt(self.path, HEAD, self.root / "cycle-1",
                          self.root / "replay.json")

    def test_no_candidate_is_ever_called_verified_during_prepare(self):
        proposal = forge.prepare(self.path, "2026-11-24", HEAD,
                                 self.root / "proposal")
        self.assertEqual(proposal["status"],
                         "CANDIDATE_AWAITING_INDEPENDENT_VERIFICATION")
        obj = forge.read(self.root / "proposal/plan.json")
        self.assertEqual(obj, proposal)
        self.assertEqual(forge.read(self.path)["receipts"], [])

    def test_tampered_candidate_never_accepted(self):
        forge.prepare(self.path, "2026-11-24", HEAD, self.root / "cycle")
        plan_path = self.root / "cycle/plan.json"
        proposed = forge.read(plan_path)
        proposed["operator"]["score"] += 1000
        forge.save(plan_path, proposed)
        with self.assertRaisesRegex(ValueError, "stale or altered plan"):
            forge.receipt(self.path, HEAD, self.root / "cycle",
                          self.root / "result.json")

    def test_state_history_and_output_hash_guard(self):
        state, _ = self.run_cycle("2026-11-24", 1)
        for change in ("hash", "status", "program", "parent", "evaluator"):
            t = copy.deepcopy(state)
            row = t["receipts"][0]
            if change == "hash":
                row["chain_sha256"] = "0" * 64
            elif change == "status":
                row["status"] = "SELF_ASSERTED"
            elif change == "program":
                row["program"].append("fake")
            elif change == "parent":
                row["left"] = "m:unverified"
            else:
                row["evaluator"] = "untrusted-evaluator"
            with self.subTest(change=change), self.assertRaises(ValueError):
                forge.validate_state(t)

    def test_operator_data_cannot_be_python_or_new_host_commands(self):
        for domain, ops in forge.DOMAINS.items():
            for unsafe in ("__import__('os')", "eval", "/bin/sh", "axiom"):
                with self.subTest(domain=domain, op=unsafe), self.assertRaises(ValueError):
                    forge.check_program(domain, [ops[0], unsafe])
            with self.assertRaises(ValueError):
                forge.check_program(domain, [ops[0]] * 100)
        with self.assertRaises(ValueError):
            forge.reference_primitive("grid3", "undefined", 0)

    def test_short_trial_slots_preserve_old_daily_history_and_bound_runs(self):
        from unittest.mock import patch
        original, _ = self.run_cycle("2026-11-23", 1)
        self.assertEqual(original["last_utc_day"], "2026-11-23")
        next_state, _ = self.run_cycle("2026-11-23T08:00Z", 2)
        self.assertEqual(next_state["last_utc_day"], "2026-11-23T08:00Z")
        self.assertEqual(len(next_state["receipts"]), 2)
        same_slot = forge.plan(next_state, "2026-11-23T08:00Z", HEAD)
        self.assertFalse(same_slot["candidate"])
        self.assertEqual(same_slot["reason"], "ALREADY_CERTIFIED_TODAY")
        with patch.object(forge, "TRIAL_RECEIPT_CAP", 2):
            blocked = forge.plan(next_state, "2026-11-23T08:10Z", HEAD)
            self.assertEqual(blocked["reason"], "TRIAL_CAP_REACHED")
        self.assertEqual(
            forge.plan(next_state, "2026-11-24T08:00Z", HEAD)["reason"],
            "TRIAL_WINDOW_CLOSED")
        for invalid in ("2026-11-23T08:05Z", "2026-11-23T25:00Z",
                        "2026-11-23T08:00+09:00"):
            with self.subTest(invalid=invalid), self.assertRaises(ValueError):
                forge.check_day(invalid)

    def test_duplicate_json_fields_and_bad_dates_fail_closed(self):
        self.path.write_text('{"schema_version":1,"schema_version":2}', "utf-8")
        with self.assertRaises(ValueError):
            forge.read(self.path)
        for day in ("2026-02-30", "2026/11/24"):
            with self.assertRaises(ValueError):
                forge.plan(forge.empty_state(), day, HEAD)
        with self.assertRaises(ValueError):
            forge.plan(forge.empty_state(), "2026-11-24", "not-a-sha")

    def test_behavioral_duplicate_detection(self):
        state, first = self.run_cycle("2026-11-24", 1)
        second = forge.plan(state, "2026-11-25", HEAD)
        self.assertTrue(second["candidate"])
        self.assertNotEqual(first["operator"]["id"], second["operator"]["id"])
        seen = {(r["domain"], r["behavior"]["fingerprint"])
                for r in state["receipts"]}
        fp = (second["operator"]["domain"],
              second["operator"]["behavior"]["fingerprint"])
        self.assertNotIn(fp, seen)


if __name__ == "__main__":
    unittest.main()
