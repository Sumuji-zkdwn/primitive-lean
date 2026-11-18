"""Independent finite regression checks for the A/B splice regularity audit."""

from fractions import Fraction
from itertools import product
import unittest

from tools.check_curve_word_reentry import TURN_OVER_PI, audit, splice_data


class CurveWordReentryTest(unittest.TestCase):
    def test_arc_curvature_units_are_exact(self):
        self.assertEqual(TURN_OVER_PI, {"A": Fraction(1, 2), "B": Fraction(3, 2)})

    def test_ab_ba_have_opposite_nonzero_jumps(self):
        ab = splice_data("AB")["joins"][0]
        ba = splice_data("BA")["joins"][0]
        self.assertEqual(ab["signed_jump_over_pi_per_h"], "1")
        self.assertEqual(ba["signed_jump_over_pi_per_h"], "-1")
        self.assertEqual(ab["angle_over_pi"], "1/2")
        self.assertEqual(ba["angle_over_pi"], "3/2")
        self.assertFalse(ab["C2_at_join"])
        self.assertFalse(ba["C2_at_join"])

    def test_same_letter_splices_match(self):
        for word in ("A", "B", "AAAA", "BBBB"):
            result = splice_data(word)
            self.assertTrue(result["all_splices_C2"])
            self.assertFalse(result["has_mixed_adjacent_letters"])
            self.assertTrue(all(j["signed_jump_over_pi_per_h"] == "0" for j in result["joins"]))

    def test_only_mixed_splices_fail(self):
        result = splice_data("AABBA")
        self.assertEqual([j["signed_jump_over_pi_per_h"] for j in result["joins"]],
                         ["0", "1", "0", "-1"])
        self.assertEqual([j["position_over_h"] for j in result["joins"]], [1, 2, 3, 4])
        self.assertFalse(result["all_splices_C2"])

    def test_exhaustive_length_counts(self):
        self.assertTrue(audit(8)["passed"])
        for n in range(1, 9):
            words = ["".join(w) for w in product("AB", repeat=n)]
            self.assertEqual(sum(splice_data(w)["all_splices_C2"] for w in words), 2)
            self.assertEqual(sum(not splice_data(w)["all_splices_C2"] for w in words), 2**n - 2)

    def test_invalid_inputs(self):
        for word in ("", "a", "AC", "AB ", None):
            with self.assertRaises(ValueError):
                splice_data(word)
        for n in (0, -1, 1.5):
            with self.assertRaises(ValueError):
                audit(n)


if __name__ == "__main__":
    unittest.main()
