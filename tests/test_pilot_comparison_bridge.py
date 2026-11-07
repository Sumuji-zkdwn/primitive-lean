"""Independent finite/numeric oracle for the pilot-selection bridge.

These tests do not check Lean proof terms and do not establish IUT arithmetic.
"""
from fractions import Fraction
import unittest


def candidates(out, observation, choices):
    return {out(observation, choice) for choice in choices}


def fibers(forget, target, states):
    return {
        b: {target(x) for x in states if forget(x) == b}
        for b in {forget(x) for x in states}
    }


class PilotComparisonBridgeTests(unittest.TestCase):
    def test_choice_range_covers_nonconstant_fiber(self):
        states = (0, 1)
        choices = (0, 1)
        forget = lambda x: 0
        target = lambda x: x
        out = lambda b, s: s
        target_fibers = fibers(forget, target, states)
        self.assertEqual(target_fibers, {0: {0, 1}})
        self.assertTrue(all(
            values <= candidates(out, b, choices)
            for b, values in target_fibers.items()
        ))
        self.assertFalse(all(
            target(x) == target(y)
            for x in states for y in states if forget(x) == forget(y)
        ))

    def test_numerical_bound_necessary_and_sufficient_in_truncated_window(self):
        scale, a = Fraction(14, 3), Fraction(1)
        target = -a
        for cap in (Fraction(1), Fraction(4)):
            required = (scale - 1) * a
            feasible_by_bound = required <= cap
            volume = lambda t: min(t, cap)
            if feasible_by_bound:
                self.assertEqual(-scale * a + volume(required), target)
            else:
                self.assertLess(-scale * a + cap, target)
            self.assertEqual(feasible_by_bound, cap == 4)

    def test_descent_alone_does_not_force_numerical_wall(self):
        states = (0, 1)
        forget = lambda _: 0
        update = lambda x: x
        self.assertTrue(all(
            forget(update(forget(x))) == forget(update(x)) for x in states
        ))
        scale = Fraction(14, 3)
        cap = Fraction(1)
        self.assertLess(-scale + cap, -1)


if __name__ == "__main__":
    unittest.main()
