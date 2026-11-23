"""Semantic Foundry regression: old-closure impossibility, verified new semantics."""
from pathlib import Path
from tempfile import TemporaryDirectory
import copy
import itertools
import json
import unittest

from tools.autonomy import generic_forge as gf
from tools.autonomy import semantic_forge as sf

HEAD = "a" * 40


class SemanticFoundryTests(unittest.TestCase):
    def setUp(self):
        self.temp = TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.state = self.root / "verified.json"
        sf.write(self.state, sf.empty_state())

    def run_cycle(self, day, count):
        output = self.root / f"proposal-{count}"
        candidate = sf.prepare(self.state, day, HEAD, output)
        self.assertTrue(candidate["candidate"])
        self.assertEqual(candidate["status"],
                         "AWAITING_INDEPENDENT_EVALUATION")
        updated = sf.receipt(self.state, HEAD, output,
                             self.root / f"next-{count}.json")
        sf.write(self.state, updated)
        return candidate, updated

    def test_every_original_primitive_preserves_constant_sequences(self):
        evidence = sf.primitive_closure_invariant()
        self.assertEqual(evidence["old_primitive_count"], 6)
        self.assertEqual(evidence["independent_base_checks"], 24)
        # Independent sanity test on all primitive words up to three steps.
        # The mathematical induction covers arbitrary finite word lengths.
        for length in (1, 2, 3):
            for word in itertools.product(gf.DOMAINS["signal4"], repeat=length):
                for value in range(4):
                    original = gf.encoded("signal4", [value] * 4)
                    result = gf.apply_program(
                        "signal4", word, original, gf.independent_primitive)
                    cells = gf.digits("signal4", result)
                    self.assertEqual(len(set(cells)), 1)

    def test_parametric_peak_separates_from_all_old_compositions(self):
        recipe = [{"kind": "peak", "order": "max",
                   "tie": "first", "level": 1}]
        result = sf.certify(recipe)
        self.assertEqual(result["exhaustive_inputs"], 256)
        self.assertEqual(result["independent_implementations"], 2)
        self.assertGreater(result["number_of_violating_constant_inputs"], 0)
        witness = result["constant_counterexample"]
        self.assertEqual(len(set(witness["input_values"])), 1)
        self.assertGreater(len(set(witness["output_values"])), 1)
        self.assertEqual(result["four_single_peak_outputs"], [1, 4, 16, 64])
        for x in range(256):
            self.assertEqual(sf.apply_recipe(recipe, x, sf.reference_step),
                             sf.apply_recipe(recipe, x, sf.independent_step))
        # This is a global context-dependent operation, not a fixed stamp.
        self.assertEqual(sf.apply_recipe(
            recipe, gf.encoded("signal4", [0, 3, 1, 2]), sf.reference_step), 4)

    def test_rules_are_generated_from_verified_semantic_ancestors(self):
        first, state1 = self.run_cycle("2026-11-24", 1)
        self.assertIsNone(first["proposal"]["parent"])
        second, state2 = self.run_cycle("2026-11-25", 2)
        self.assertEqual(len(state2["receipts"]), 2)
        self.assertEqual(second["proposal"]["parent"],
                         first["proposal"]["id"])
        self.assertEqual(len(second["proposal"]["recipe"]), 2)
        self.assertNotEqual(
            first["proposal"]["observation"]["behavior_sha256"],
            second["proposal"]["observation"]["behavior_sha256"])
        self.assertEqual(sf.validate_state(state2), state2)
        third, state3 = self.run_cycle("2026-11-26", 3)
        self.assertEqual(len(state3["receipts"]), 3)
        self.assertEqual(sf.validate_state(state3), state3)
        self.assertEqual(len({
            r["observation"]["behavior_sha256"] for r in state3["receipts"]
        }), 3)

    def test_certified_semantic_operator_is_executable(self):
        _, state = self.run_cycle("2026-11-24", 1)
        name = state["receipts"][0]["id"]
        output = sf.use(state, name, [0, 3, 1, 2])
        self.assertEqual(output["operator_id"], name)
        self.assertTrue(output["outside_original_primitive_closure"])
        self.assertEqual(len(output["output"]), 4)
        self.assertEqual(output["scope"], "FOUR_SAMPLES_2_BITS_ONLY")
        with self.assertRaises(ValueError):
            sf.use(state, "sf_0000000000000000", [0, 3, 1, 2])
        with self.assertRaises(ValueError):
            sf.use(state, name, [0, 3, 1, 99])

    def test_only_certified_rows_can_become_parents(self):
        first = sf.prepare(self.state, "2026-11-24", HEAD,
                           self.root / "proposal")
        self.assertEqual(sf.read(self.state)["receipts"], [])
        submitted = sf.read(self.root / "proposal/proposal.json")
        submitted["proposal"]["observation"]["changed_inputs"] += 1
        sf.write(self.root / "proposal/proposal.json", submitted)
        with self.assertRaisesRegex(ValueError, "stale/tampered"):
            sf.receipt(self.state, HEAD, self.root / "proposal",
                       self.root / "corrupted.json")
        self.assertTrue(first["candidate"])

    def test_duplicate_day_fails_without_adding_a_receipt(self):
        _, state = self.run_cycle("2026-11-24", 1)
        following = sf.plan(state, "2026-11-24", HEAD)
        self.assertFalse(following["candidate"])
        self.assertEqual(following["reason"], "ALREADY_VERIFIED_TODAY")
        self.assertEqual(len(state["receipts"]), 1)

    def test_untrusted_new_code_and_malformed_dsl_are_refused(self):
        invalid = [
            [{"kind": "python", "source": "exec('x')"}],
            [{"kind": "peak", "order": "argmax", "tie": "first", "level": 1}],
            [{"kind": "peak", "order": "max", "tie": "first", "level": True}],
            [{"kind": "peak", "order": "max", "tie": "first", "level": 0}],
            [{"kind": "peak", "order": "max", "tie": "first", "level": 1,
              "extra": "shell"}],
            [{"kind": "existing", "name": "malware"}],
            [{"kind": "peak", "order": "max", "tie": "first", "level": 1}] * 2,
            [{"kind": "peak", "order": "max", "tie": "first", "level": 1}] * 6,
        ]
        for recipe in invalid:
            with self.subTest(recipe=recipe), self.assertRaises(ValueError):
                sf.validate_recipe(recipe)

    def test_tampering_with_receipt_or_invariant_is_rejected(self):
        _, state = self.run_cycle("2026-11-24", 1)
        for name in ("invariant", "behavior", "score", "parent",
                     "status", "chain_sha256", "recipe"):
            fake = copy.deepcopy(state)
            record = fake["receipts"][0]
            if name == "invariant":
                record["invariant"]["independent_base_checks"] = 0
            elif name == "behavior":
                record["observation"]["behavior_sha256"] = "0" * 64
            elif name == "score":
                record["score"] += 1
            elif name == "parent":
                record["parent"] = "sf_fake"
            elif name == "status":
                record["status"] = "SELF_ASSERTED"
            elif name == "chain_sha256":
                record["chain_sha256"] = "0" * 64
            else:
                record["recipe"] = [{"kind": "existing", "name": "reverse"}]
            with self.subTest(name=name), self.assertRaises(ValueError):
                sf.validate_state(fake)

    def test_duplicate_json_fields_and_invalid_dates(self):
        self.state.write_text('{"schema_version":1,"schema_version":2}', "utf-8")
        with self.assertRaises(ValueError):
            sf.read(self.state)
        for day in ("2026-02-30", "2026/11/24"):
            with self.assertRaises(ValueError):
                sf.plan(sf.empty_state(), day, HEAD)
        with self.assertRaises(ValueError):
            sf.plan(sf.empty_state(), "2026-11-24", "short")

    def test_nonvarying_peak_stamp_is_not_a_verified_new_capability(self):
        # "min" applied to one-hot basis inputs will choose zero-valued
        # positions, so it fails the required four-way positional response.
        recipe = [{"kind": "peak", "order": "min",
                   "tie": "first", "level": 1}]
        self.assertIsNone(sf.evaluate(sf.canonical(recipe).decode("utf-8")))


if __name__ == "__main__":
    unittest.main()
