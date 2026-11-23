"""Exact finite tests for probabilistic tangent observations of siphon E and L.

The full real-plane injectivity claim is proved algebraically in
docs/research/2026-11-23-siphon-tangent-distribution-observability.md.
Finite checks do not stand in for a Lean kernel proof.
"""
from collections import defaultdict
from fractions import Fraction
from itertools import product
from math import isqrt
import unittest


def E(state):
    u, v = state
    r = v + u**3
    U = u + r**2
    return U, r - U**3


def L(state):
    u, v = state
    return v, v-u


def p1(state):
    """First squared-minor weight of the tangent to I(u,v)=v+u^3."""
    u, _ = state
    return Fraction(1, 1) / (1 + 9*u**4)


def readings(state):
    """P1 at the five ordered observation words: 1,E,E²,L,E∘L."""
    return (p1(state), p1(E(state)), p1(E(E(state))),
            p1(L(state)), p1(E(L(state))))


def sqrt_rational(q):
    """Return exact nonnegative rational square root, if it exists."""
    if q < 0:
        raise ValueError('negative rational')
    p, r = isqrt(q.numerator), isqrt(q.denominator)
    if p*p != q.numerator or r*r != q.denominator:
        raise ValueError('not a rational square')
    return Fraction(p, r)


def reconstruct(reads):
    """Invert five exact P1 readings on rational states.

    For general real states the formula uses ordinary nonnegative real roots.
    """
    if len(reads) != 5:
        raise ValueError('expected five readings')
    b0, b1, b2 = [sqrt_rational((1/p-1)/9) for p in reads[:3]]
    a = sqrt_rational((b2-2*b1+b0)/2)   # a = r^2 >= 0
    if a:
        u_candidates = ((b1-b0-a*a)/(2*a),)
        signed_r = sqrt_rational(a)
        r_candidates = (signed_r, -signed_r)
    else:
        signed_u = sqrt_rational(b0)
        u_candidates = (signed_u, -signed_u)
        r_candidates = (Fraction(0),)
    possible = {(u, r-u**3) for u in u_candidates for r in r_candidates}
    matches = [z for z in possible if readings(z) == reads]
    if len(matches) != 1:
        raise ValueError(f'expected unique inverse, found {len(matches)}')
    return matches[0]


class DistributionObservabilityChecks(unittest.TestCase):
    def test_probabilities_and_odds(self):
        for u in [Fraction(k,2) for k in range(-8,9)]:
            p = p1((u,Fraction(0)))
            self.assertTrue(0 < p <= 1)
            self.assertEqual((1-p)/p, 9*u**4)

    def test_exhaustive_integer_grid(self):
        states = [(Fraction(u), Fraction(v)) for u,v in
                  product(range(-3,4), repeat=2)]
        expected_classes = [4, 41, 41, 45, 49]
        for length, expected in enumerate(expected_classes, 1):
            classes = defaultdict(list)
            for z in states:
                classes[readings(z)[:length]].append(z)
            self.assertEqual(len(classes), expected)
        for z in states:
            self.assertEqual(reconstruct(readings(z)), z)

    def test_exhaustive_half_integer_grid(self):
        vals = [Fraction(k,2) for k in range(-6,7)]
        states = list(product(vals, repeat=2))
        expected_classes = [7, 152, 154, 162, 169]
        for length, expected in enumerate(expected_classes, 1):
            classes = {readings(z)[:length] for z in states}
            self.assertEqual(len(classes), expected)
        for z in states:
            self.assertEqual(reconstruct(readings(z)), z)

    def test_required_last_probe_on_two_degenerate_fibres(self):
        z, mirror = (Fraction(0), Fraction(1)), (Fraction(0), Fraction(-1))
        self.assertEqual(readings(z)[:4], readings(mirror)[:4])
        self.assertNotEqual(readings(z)[4], readings(mirror)[4])
        z, mirror = (Fraction(1), Fraction(-1)), (Fraction(-1), Fraction(1))
        self.assertEqual(readings(z)[:4], readings(mirror)[:4])
        self.assertNotEqual(readings(z)[4], readings(mirror)[4])

    def test_symbolic_separation_identities_on_rationals(self):
        for a in [Fraction(k,3) for k in range(-9,10)]:
            v = a + (a+a**3)**2
            w = -a + (-a+(-a)**3)**2
            self.assertEqual(v**2-w**2, 4*a**3*(1+a*a)**2)
            C = a**2*(1+a*a+a**8)**2
            self.assertEqual((-a**3+C)**2 - (a**3+C)**2,
                             -4*a**5*(1+a*a+a**8)**2)


if __name__ == '__main__':
    unittest.main()
