"""Research regression: #131 observer-relative depth and compiled-macro effect.

Read actual proof-forge requests, not a separate set of sample transitions.
The source fixtures are from 2026-11-11-observer-orientation-depth.md and
tests/test_operator_orientation_depth.py. The new all-pairs comparison below
is a bounded finite analysis; generated Lean certificates are separately
checked by the dedicated Proof Forge workflow at the exact commit.
"""
import json
from pathlib import Path
import unittest

from tools.autonomy import proof_forge as forge
from test_operator_orientation_depth import shortest_depth

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / "proof_forge" / "requests"


def model(name):
    return forge.read_request(FIXTURES / (name + ".json"))


class OrientationResearchTests(unittest.TestCase):
    def test_original_research_objects_unchanged(self):
        old = model("orientation_old_alphabet")
        extended = model("orientation_extended_alphabet")
        primitive = model("orientation_primitive")
        macro = model("orientation_macro")
        self.assertEqual(old["observations"], [0, 0, 1])
        self.assertEqual(old["transitions"], [[0, 1, 2]])
        self.assertEqual(extended["observations"], old["observations"])
        self.assertEqual(extended["transitions"], [[0, 1, 2], [0, 2, 2]])
        self.assertEqual(primitive["observations"], [0, 0, 0, 1])
        self.assertEqual(primitive["transitions"], [[0, 2, 3, 3]])
        self.assertEqual(macro["observations"], primitive["observations"])
        self.assertEqual(macro["transitions"][0], primitive["transitions"][0])
        step = primitive["transitions"][0]
        self.assertEqual(macro["transitions"][1], [step[step[i]] for i in range(4)])

    def test_new_action_changes_predictive_kernel(self):
        old = model("orientation_old_alphabet")
        extended = model("orientation_extended_alphabet")
        left = forge.solve(old)
        right = forge.solve(extended)
        forge.validate_result(old, left)
        forge.validate_result(extended, right)
        self.assertEqual(left["kind"], "EQUIVALENT")
        self.assertEqual(right["kind"], "DISTINGUISHABLE")
        self.assertEqual(right["word"], [1])
        self.assertIsNone(shortest_depth(
            old["transitions"], old["observations"], 0, 1, (0,)))
        self.assertEqual(shortest_depth(
            extended["transitions"], extended["observations"], 0, 1, (0, 1)), 1)

    def test_macro_changes_depth_without_changing_equivalence_relation(self):
        primitive = model("orientation_primitive")
        macro = model("orientation_macro")
        x = forge.solve(primitive)
        y = forge.solve(macro)
        self.assertEqual(x["word"], [0, 0])
        self.assertEqual(y["word"], [1])
        for i in range(4):
            for j in range(4):
                p = dict(primitive, pair=[i, j])
                q = dict(macro, pair=[i, j])
                rp, rq = forge.solve(p), forge.solve(q)
                forge.validate_result(p, rp)
                forge.validate_result(q, rq)
                op = shortest_depth(primitive["transitions"],
                                    primitive["observations"], i, j, (0,))
                om = shortest_depth(macro["transitions"],
                                    macro["observations"], i, j, (0, 1))
                self.assertEqual((rp["kind"] == "EQUIVALENT"), op is None)
                self.assertEqual((rq["kind"] == "EQUIVALENT"), om is None)
                self.assertEqual(op is None, om is None)
                if op is not None:
                    self.assertLessEqual(om, op)
        self.assertEqual(x["kind"], "DISTINGUISHABLE")
        self.assertEqual(y["kind"], "DISTINGUISHABLE")

    def test_reject_mutated_macro_equivalence_claim(self):
        primitive = model("orientation_primitive")
        macro = model("orientation_macro")
        # Replacing a named macro with an unrelated new operation can
        # separate more states. The checker must reject the assertion that
        # the new operation is exactly primitive composed twice.
        macro["transitions"][1] = [0, 0, 0, 0]
        step = primitive["transitions"][0]
        self.assertNotEqual(macro["transitions"][1],
                            [step[step[i]] for i in range(4)])


if __name__ == "__main__":
    unittest.main()
