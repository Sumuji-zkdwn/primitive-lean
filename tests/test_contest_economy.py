"""Independent exact-arithmetic checks for the conditional contest-economy model."""
from fractions import Fraction as F
import unittest


def participation(d: F, e: F) -> F:
    assert d > 0
    assert e >= 0
    return max(F(0), F(1) - e / d)


def delayed(a: F, gamma: F, z0: F, steps: int) -> list[F]:
    z = [z0, a * z0]
    for _ in range(2, steps + 1):
        z.append(a * z[-1] - gamma * z[-2])
    return z


class ContestEconomyExactTests(unittest.TestCase):
    def test_weighted_selection_gain_le_gap(self):
        q = [F(1), F(3), F(2)]
        w = [F(1, 4), F(1, 4), F(1, 2)]
        baseline = sum((wi * qi for wi, qi in zip(w, q)), F(0))
        self.assertEqual(sum(w), 1)
        self.assertLessEqual(max(q) - baseline, max(q) - min(q))

    def test_delayed_negative_discriminant_crosses_on_step_seven(self):
        a, gamma = F(7, 10), F(3, 20)
        self.assertLess(a * a, 4 * gamma)
        z = delayed(a, gamma, F(9), 7)
        self.assertEqual(z[6], F(3141, 1000000))
        self.assertEqual(z[7], F(-106533, 10000000))
        self.assertGreater(z[6], 0)
        self.assertLessEqual(z[7], 0)

    def test_stronger_three_step_condition(self):
        a, gamma = F(7, 10), F(3, 10)
        self.assertLessEqual(a * a, 2 * gamma)
        self.assertLessEqual(delayed(a, gamma, F(9), 3)[3], 0)

    def test_arbitrarily_near_origin_disagree(self):
        for epsilon in [F(1, 10), F(1, 10000), F(1, 10000000)]:
            d = epsilon / 2
            self.assertEqual(participation(d, F(0)), 1)
            self.assertEqual(participation(d, d), 0)

    def test_entry_threshold(self):
        self.assertEqual(participation(F(1), F(1)), 0)
        self.assertEqual(participation(F(1, 4), F(1)), 0)
        self.assertEqual(participation(F(10), F(1)), F(9, 10))


if __name__ == "__main__":
    unittest.main()
