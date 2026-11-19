"""Independent numerical checks for lean/OrbitTraceGlasser.lean.

Python standard library only (floating point, so these are numerical checks,
not proofs). For Glasser maps G(x) = x + c - sum_j b_j / (x - a_j) with
distinct poles a_j and positive residues b_j:

* on each gap between consecutive poles G is increasing and reaches any level t
  (found by bisection), and the n + 1 preimages sum to t - c + sum_j a_j;
* the weights 1 / G'(r_k(t)) sum to 1;
* int g(G(x)) dx agrees with int g(x) dx for a Gaussian and a Cauchy density,
  with the quadrature split at the poles;
* the maps of OrbitTraceBoole.lean are the instances named in the Lean file.
"""
from __future__ import annotations

import math
import random
import re
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / 'lean' / 'OrbitTraceGlasser.lean'


def glasser(a, b, c, x):
    return x + c - sum(bj / (x - aj) for aj, bj in zip(a, b))


def glasser_deriv(a, b, x):
    return 1 + sum(bj / (x - aj) ** 2 for aj, bj in zip(a, b))


def preimages(a, b, c, t):
    """The n + 1 preimages of t, one per gap, by bisection."""
    poles = sorted(a)
    big = abs(t) + abs(c) + sum(abs(p) for p in poles) + sum(b) + 10
    ends = [-big * 10] + poles + [big * 10]
    roots = []
    for lo, hi in zip(ends, ends[1:]):
        eps = 1e-12 * max(1.0, abs(hi - lo))
        lo, hi = lo + eps, hi - eps
        f = lambda x: glasser(a, b, c, x) - t
        assert f(lo) < 0 < f(hi), (lo, hi, f(lo), f(hi))
        for _ in range(300):
            mid = (lo + hi) / 2
            if f(mid) < 0:
                lo = mid
            else:
                hi = mid
        roots.append((lo + hi) / 2)
    return roots


def simpson(f, lo, hi, n=4000):
    h = (hi - lo) / n
    total = f(lo) + f(hi)
    for k in range(1, n):
        total += (4 if k % 2 else 2) * f(lo + k * h)
    return total * h / 3


def integral_split(f, poles):
    """Integral over R of f, splitting at the poles with tanh/exp substitutions."""
    poles = sorted(poles)
    total = 0.0
    if not poles:
        return simpson(lambda u: f(math.sinh(u)) * math.cosh(u), -12, 12, n=40000)
    # left half-line (-inf, p0) and right half-line (p_last, inf)
    total += simpson(lambda u: f(poles[0] - math.exp(u)) * math.exp(u), -30, 9, n=40000)
    total += simpson(lambda u: f(poles[-1] + math.exp(u)) * math.exp(u), -30, 9, n=40000)
    for lo, hi in zip(poles, poles[1:]):
        def g(u, lo=lo, hi=hi):
            w = (1 + math.tanh(u)) / 2
            x = lo + (hi - lo) * w
            if x <= lo or x >= hi:
                return 0.0
            return f(x) * (hi - lo) / (2 * math.cosh(u) ** 2)
        total += simpson(g, -18, 18, n=40000)
    return total


CASES = [
    ([], [], 0.0),
    ([0.0], [1.0], 0.0),
    ([0.0, 1.0], [1.0, 1.0], 1.0),
    ([-2.0, 0.5, 3.0], [0.3, 2.0, 1.1], -0.7),
    ([1.5, -1.0, 4.0, 0.0], [1.0, 0.25, 3.0, 0.6], 2.0),
]


class Branches(unittest.TestCase):
    def test_branch_sum_and_weights(self):
        rng = random.Random(20261119)
        cases = list(CASES)
        for _ in range(5):
            n = rng.randint(1, 5)
            a = rng.sample(range(-20, 21), n)
            a = [x / 3 for x in a]
            b = [rng.uniform(0.1, 3.0) for _ in range(n)]
            cases.append((a, b, rng.uniform(-2, 2)))
        for a, b, c in cases:
            for t in (-40.0, -2.5, 0.0, 0.3, 7.0, 100.0):
                r = preimages(a, b, c, t)
                self.assertEqual(len(r), len(a) + 1)
                for x in r:
                    self.assertAlmostEqual(glasser(a, b, c, x), t,
                                           delta=1e-7 * max(1.0, abs(t)))
                self.assertAlmostEqual(sum(r), t - c + sum(a), delta=1e-7 * max(1.0, abs(t)))
                self.assertAlmostEqual(sum(1 / glasser_deriv(a, b, x) for x in r), 1.0,
                                       places=7)


class Integrals(unittest.TestCase):
    def test_measure_preservation(self):
        for a, b, c in CASES:
            for g, exact in ((lambda x: math.exp(-x * x), math.sqrt(math.pi)),
                             (lambda x: 1 / (1 + x * x), math.pi)):
                lhs = integral_split(lambda x: g(glasser(a, b, c, x)), a)
                self.assertAlmostEqual(lhs, exact, delta=2e-3 * exact, msg=(a, b, c))


class LeanSource(unittest.TestCase):
    def test_no_holes_and_main_declarations_present(self):
        source = LEAN.read_text(encoding='utf-8')
        self.assertIsNone(re.search(r'^\s*(axiom|sorry)\b', source, re.M))
        self.assertNotIn('sorry', source)
        self.assertNotIn('native_decide', source)
        for name in ('glasser_surj_gap', 'sum_eq_of_roots', 'glasser_root', 'glasser_branch_sum',
                     'glasser_branches', 'glasser_measurePreserving', 'glasser_integral',
                     'glasser_measurePreserving_of_injective', 'glasser_integral_of_injective',
                     'S3_eq_glasser', 'boole_eq_glasser',
                     'not_measurePreserving_negative_residue'):
            self.assertIsNotNone(re.search(r'^theorem ' + name + r'\b', source, re.M), name)

    def test_negative_residue_misses_interval(self):
        # x + 1/x never lands in (-2, 2) for x != 0, so (-2, 2) has a null preimage
        for k in range(-4000, 4001):
            x = k / 37.0
            if x != 0:
                self.assertGreaterEqual(abs(glasser([0.0], [-1.0], 0.0, x)), 2 - 1e-12)

    def test_instances_match(self):
        for x in (-3.2, -0.4, 0.37, 0.81, 1.6, 9.0):
            self.assertAlmostEqual(glasser([0.0, 1.0], [1.0, 1.0], 1.0, x),
                                   x + 1 - 1 / x - 1 / (x - 1), places=12)
            self.assertAlmostEqual(glasser([0.0], [1.0], 0.0, x), x - 1 / x, places=12)


if __name__ == '__main__':
    unittest.main()
