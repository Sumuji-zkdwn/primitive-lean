"""Meta Forge tests: higher-order rule synthesis, verified feedback and safety."""
from pathlib import Path
from tempfile import TemporaryDirectory
import copy
import unittest

from tools.autonomy import generic_forge as gf
from tools.autonomy import meta_forge as mf

HEAD = "a" * 40


class MetaForgeTests(unittest.TestCase):
    def setUp(self):
        self.tmp = TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.state_path = self.root / "state.json"
        mf.save(self.state_path, mf.empty_state())

    def one_cycle(self, day, number):
        evidence = self.root / f"cycle-{number}"
        candidate = mf.prepare(self.state_path, day, HEAD, evidence)
        self.assertTrue(candidate["candidate"])
        updated = mf.receipt(self.state_path, HEAD, evidence,
                             self.root / f"next-{number}.json")
        mf.save(self.state_path, updated)
        return candidate, updated

    def test_each_meta_primitive_has_independent_transformer(self):
        for domain in gf.DOMAINS:
            for atom in mf.step_atoms():
                for indices in mf.TRAIN + mf.HOLDOUT:
                    seed = mf.seed_program(domain, indices)
                    try:
                        a = mf.rewrite_reference(domain, [atom], seed)
                    except ValueError:
                        with self.assertRaises(ValueError):
                            mf.rewrite_independent(domain, [atom], seed)
                        continue
                    b = mf.rewrite_independent(domain, [atom], seed)
                    self.assertEqual(a, b)
                    gf.check_program(domain, a)

    def test_generated_rule_changes_runnable_images_and_signals(self):
        rule = [{"op": "reverse"}]
        outcome = mf.fingerprint_for(rule)
        self.assertGreaterEqual(outcome["train_changed"], 2)
        self.assertGreaterEqual(outcome["holdout_changed"], 2)
        self.assertEqual(outcome["total_source_programs"], 12)
        self.assertEqual(outcome["data_inputs_exhaustively_checked"],
                         6 * (512 + 256))
        for domain in gf.DOMAINS:
            seed = mf.seed_program(domain, (2, 4, 5))
            output = mf.rewrite_reference(domain, rule, seed)
            self.assertEqual(output, list(reversed(seed)))
            result = gf.audit(domain, tuple(output))
            self.assertEqual(result["inputs_exhaustively_checked"],
                             gf.DOMAIN_SIZE[domain])

    def test_generated_rules_can_be_composed_not_just_selected_from_list(self):
        state = mf.empty_state()
        self.assertEqual(mf.validate_state(state), state)
        first, verified = self.one_cycle("2026-11-24", 1)
        self.assertEqual(len(verified["rules"]), 1)
        self.assertIsNone(first["rule"]["parent"])
        next_one, next_state = self.one_cycle("2026-11-25", 2)
        self.assertEqual(len(next_state["rules"]), 2)
        self.assertEqual(next_one["rule"]["parent"], first["rule"]["id"])
        self.assertEqual(next_one["rule"]["steps"][:-1],
                         first["rule"]["steps"])
        self.assertEqual(len(next_one["rule"]["steps"]), 2)
        self.assertNotEqual(first["rule"]["fingerprint"],
                            next_one["rule"]["fingerprint"])
        self.assertEqual(mf.validate_state(next_state), next_state)

    def test_generated_rule_is_callable_on_unseen_operator_program(self):
        _, state = self.one_cycle("2026-11-24", 1)
        name = state["rules"][0]["id"]
        for domain in gf.DOMAINS:
            unseen = mf.seed_program(domain, (0, 4, 1, 5))
            output = mf.use_rule(state, name, domain, unseen)
            self.assertEqual(output["rule_id"], name)
            self.assertEqual(output["domain"], domain)
            self.assertEqual(output["full_domain_inputs_checked"],
                             gf.DOMAIN_SIZE[domain])
            self.assertEqual(output["generated_program"],
                             mf.rewrite_independent(domain, state["rules"][0]["steps"],
                                                    unseen))
        with self.assertRaises(ValueError):
            mf.use_rule(state, "mf_0000000000000000", "grid3",
                        ["rotate_cw"])

    def test_unverified_candidate_cannot_save_state(self):
        candidate = mf.prepare(self.state_path, "2026-11-24", HEAD,
                               self.root / "cycle")
        self.assertTrue(candidate["candidate"])
        self.assertEqual(candidate["status"], "UNVERIFIED_META_RULE_CANDIDATE")
        self.assertEqual(mf.load(self.state_path)["rules"], [])
        candidate["rule"]["score"] += 9999
        mf.save(self.root / "cycle/proposal.json", candidate)
        with self.assertRaisesRegex(ValueError, "modified candidate"):
            mf.receipt(self.state_path, HEAD, self.root / "cycle",
                       self.root / "result.json")

    def test_same_utc_day_cannot_create_duplicate(self):
        _, state = self.one_cycle("2026-11-24", 1)
        result = mf.plan(state, "2026-11-24", HEAD)
        self.assertFalse(result["candidate"])
        self.assertEqual(result["reason"], "ALREADY_EVALUATED_TODAY")

    def test_tampered_or_unknown_meta_rules_fail_closed(self):
        _, original = self.one_cycle("2026-11-24", 1)
        for field in ("fingerprint", "steps", "parent", "status",
                      "score", "evaluator", "chain_sha256"):
            bad = copy.deepcopy(original)
            row = bad["rules"][0]
            if field == "steps":
                row["steps"].append({"op": "__import__", "slot": 0})
            elif field == "score":
                row[field] += 1
            elif field == "parent":
                row[field] = "mf_" + ("0" * 16)
            elif field == "status":
                row[field] = "SELF_ATTESTED"
            elif field == "evaluator":
                row[field] = "untrusted-code"
            else:
                row[field] = "0" * 64
            with self.subTest(field=field), self.assertRaises(ValueError):
                mf.validate_state(bad)

    def test_reject_unknown_code_and_unsafe_dimensions(self):
        for steps in (
            [{"op": "eval"}],
            [{"op": "append", "slot": True}],
            [{"op": "append", "slot": -1}],
            [{"op": "append", "slot": 999}],
            [{"op": "reverse", "python": "import os"}],
            [{"op": "reverse"}] * (mf.MAX_RULE_STEPS + 1),
        ):
            with self.subTest(steps=steps), self.assertRaises(ValueError):
                mf.check_steps(steps)
        for day in ("2026-02-30", "2026/11/24"):
            with self.assertRaises(ValueError):
                mf.plan(mf.empty_state(), day, HEAD)

    def test_short_trial_slots_preserve_verified_history_and_bounded_cost(self):
        from unittest.mock import patch
        first, old = self.one_cycle("2026-11-23", 1)
        second, state = self.one_cycle("2026-11-23T08:00Z", 2)
        self.assertEqual(state["last_utc_day"], "2026-11-23T08:00Z")
        self.assertEqual(len(state["rules"]), 2)
        self.assertEqual(second["rule"]["parent"], first["rule"]["id"])
        same = mf.plan(state, "2026-11-23T08:00Z", HEAD)
        self.assertFalse(same["candidate"])
        self.assertEqual(same["reason"], "ALREADY_EVALUATED_TODAY")
        with patch.object(mf, "TRIAL_RECEIPT_CAP", 2):
            blocked = mf.plan(state, "2026-11-23T08:10Z", HEAD)
            self.assertEqual(blocked["reason"], "TRIAL_CAP_REACHED")
        self.assertEqual(mf.plan(state, "2026-11-24T08:00Z", HEAD)["reason"],
                         "TRIAL_WINDOW_CLOSED")
        with self.assertRaises(ValueError):
            mf.check_day("2026-11-23T08:05Z")

    def test_duplicate_json_keys_or_broken_source_refused(self):
        self.state_path.write_text(
            '{"schema_version":1,"schema_version":2}', encoding="utf-8")
        with self.assertRaises(ValueError):
            mf.load(self.state_path)
        with self.assertRaises(ValueError):
            mf.plan(mf.empty_state(), "2026-11-24", "short")


if __name__ == "__main__":
    unittest.main()
