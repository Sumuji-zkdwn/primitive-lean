"""Exact instability checks for five tangent-probability observations."""
from fractions import Fraction
import unittest


def p(q):
    return Fraction(1, 1) / (1 + 9*q**4)


def last_probe_gap(t):
    assert t > 0
    C = t**2 * (1 + t**2 + t**8)**2
    return p(C-t**3) - p(C+t**3)


class DistributionInstabilityChecks(unittest.TestCase):
    def test_exact_gap_positive_and_vanishes_far_away(self):
        for n in [1,2,3,4,5,10,100]:
            self.assertGreater(last_probe_gap(Fraction(n)), 0)
        self.assertLess(last_probe_gap(Fraction(10)), Fraction(1,10**80))
        # Distance squared between z_t=(t,-t^3) and -z_t is 4(t^2+t^6).
        self.assertGreater(4*(10**2+10**6), 2000**2)

    def test_exact_asymptotic_coefficients(self):
        # g(t) ~ 72*t^9 near zero, g(t) ~ (8/9)*t^-87 at infinity.
        near = last_probe_gap(Fraction(1,100)) * 100**9
        far = last_probe_gap(Fraction(100)) * 100**87
        self.assertTrue(Fraction(72) < near < Fraction(73))
        self.assertTrue(Fraction(88,100) < far < Fraction(9,10))


if __name__ == '__main__':
    unittest.main()
