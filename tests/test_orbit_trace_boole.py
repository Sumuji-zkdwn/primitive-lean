"""Independent numerical checks for lean/OrbitTraceBoole.lean.

Python standard library only (floating point, so these are numerical checks,
not proofs). For Boole's map S(x) = x - 1/x:

* the explicit branches (t +- sqrt(t^2 + 4))/2 invert S, lie on opposite sides
  of 0, and have derivatives (checked by central differences) summing to 1;
* int g(S(x)) dx agrees with int g(x) dx for several integrable g, using the
  substitution x = sinh(u) style quadrature on a wide interval.

For the three-branch map S3(x) = x + 1 - 1/x - 1/(x - 1) of section 1:

* the inverse branches on (-inf, 0), (0, 1), (1, inf), found by bisection, are
  roots of X^3 - tX^2 + (t - 3)X + 1, sum to t, and the reciprocals of
  S3' at them sum to 1;
* the bounding values used for the intermediate value theorem in Lean hold;
* int g(S3(x)) dx agrees with int g(x) dx (quadrature split at the poles);
* the preimage of [3/2, 19/6] is [-1,-1/2] u [1/2,2/3] u [2,3] on a sample grid;
* sum_J int_J ((x^2-x)/(x^3-3x+1))^n dx = ((2/3)^(n-1) - (6/19)^(n-1))/(n-1)
  for n = 2..7 by Simpson's rule on the three intervals;
* int over A_n of (S3^n(x))^(-2) dx = 20/57 for n = 0..3, where the 3^n
  intervals of A_n are built from compositions of the bisected branches.
"""
from __future__ import annotations

import math
import re
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / 'lean' / 'OrbitTraceBoole.lean'


def branch(sign, t):
    return (t + sign * math.sqrt(t * t + 4)) / 2


def boole(x):
    return x - 1 / x


def integrate(f, a, b, n=400000):
    """Composite Simpson rule on [a, b] (n even)."""
    h = (b - a) / n
    total = f(a) + f(b)
    for k in range(1, n):
        total += (4 if k % 2 else 2) * f(a + k * h)
    return total * h / 3


def integrate_line(f, lim=60.0):
    """Integral over R via x = sinh(u), skipping x = 0 exactly."""
    def g(u):
        x = math.sinh(u)
        return f(x) * math.cosh(u) if x != 0 else 0.0
    return integrate(g, -math.asinh(lim * 50), math.asinh(lim * 50), n=200000)


class Branches(unittest.TestCase):
    def test_inverse_and_derivative_sum(self):
        for t in [-50, -3.5, -1, -0.1, 0, 0.3, 1, 2.5, 40]:
            plus, minus = branch(1, t), branch(-1, t)
            self.assertGreater(plus, 0)
            self.assertLess(minus, 0)
            self.assertAlmostEqual(boole(plus), t, places=9)
            self.assertAlmostEqual(boole(minus), t, places=9)
            h = 1e-6
            d = sum((branch(s, t + h) - branch(s, t - h)) / (2 * h) for s in (1, -1))
            self.assertAlmostEqual(d, 1.0, places=6)


def s3(x):
    return x + 1 - 1 / x - 1 / (x - 1)


def s3_deriv(x):
    return 1 + 1 / x ** 2 + 1 / (x - 1) ** 2


def bisect(f, lo, hi, t, steps=200):
    for _ in range(steps):
        mid = (lo + hi) / 2
        if f(mid) < t:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def s3_branches(t):
    big = abs(t) + 4
    return (bisect(s3, -big, -1 / big, t), bisect(s3, 1 / big, 1 - 1 / big, t),
            bisect(s3, 1 + 1 / big, big, t))


class ThreeBranches(unittest.TestCase):
    def test_bounds_used_in_lean(self):
        for m in [4, 4.5, 7, 20, 1000]:
            self.assertLess(s3(1 + 1 / m), -m + 3)
            self.assertLess(m - 1, s3(m))
            self.assertLess(s3(-m), -m + 2)
            self.assertLess(m, s3(-1 / m))
            self.assertLess(s3(1 / m), -m + 3)
            self.assertLess(m - 1, s3(1 - 1 / m))

    def test_roots_sum_and_weights(self):
        for t in [-80, -5, -1.5, 0, 0.7, 1.5, 19 / 6, 12, 300]:
            a, b, c = s3_branches(t)
            self.assertLess(a, 0)
            self.assertTrue(0 < b < 1)
            self.assertGreater(c, 1)
            for x in (a, b, c):
                self.assertAlmostEqual(s3(x), t, delta=1e-7 * max(1, abs(t)))
                self.assertAlmostEqual(x ** 3 - t * x ** 2 + (t - 3) * x + 1, 0,
                                       delta=1e-6 * max(1, abs(t)) ** 2)
            self.assertAlmostEqual(a + b + c, t, delta=1e-8 * max(1, abs(t)))
            self.assertAlmostEqual(sum(1 / s3_deriv(x) for x in (a, b, c)), 1.0, places=9)


class ThreeBranchIntegrals(unittest.TestCase):
    def test_three_branch_measure_preservation(self):
        def piece(f, a, b):
            # integral over (a, b) via x = a + (b - a) * (1 + tanh(u)) / 2
            def g(u):
                w = (1 + math.tanh(u)) / 2
                x = a + (b - a) * w
                if x <= a or x >= b:
                    return 0.0
                return f(x) * (b - a) / (2 * math.cosh(u) ** 2)
            return integrate(g, -20.0, 20.0, n=200000)

        def whole(f):
            def neg(u):
                x = -math.exp(u)
                return f(x) * math.exp(u)
            def pos(u):
                x = 1 + math.exp(u)
                return f(x) * math.exp(u)
            return (integrate(neg, -40.0, 12.0, n=200000) + piece(f, 0.0, 1.0)
                    + integrate(pos, -25.0, 12.0, n=200000))

        for g in (lambda x: math.exp(-x * x), lambda x: 1 / (1 + x * x)):
            lhs = whole(lambda x: g(s3(x)))
            rhs = integrate_line(g)
            self.assertAlmostEqual(lhs, rhs, delta=2e-3 * abs(rhs))


class SectionOneIntegrals(unittest.TestCase):
    INTERVALS = ((-1.0, -0.5), (0.5, 2 / 3), (2.0, 3.0))

    def test_preimage_of_icc(self):
        for k in range(-3000, 3001):
            x = k / 997
            if x in (0.0, 1.0):
                continue
            inside = 1.5 <= s3(x) <= 19 / 6
            in_union = any(a <= x <= b for a, b in self.INTERVALS)
            # skip points within rounding distance of the interval endpoints
            if min(abs(x - e) for iv in self.INTERVALS for e in iv) < 1e-9:
                continue
            self.assertEqual(inside, in_union, x)

    def test_sum_formula(self):
        for n in range(2, 8):
            lhs = sum(integrate(lambda x: ((x * x - x) / (x ** 3 - 3 * x + 1)) ** n, a, b,
                                n=20000) for a, b in self.INTERVALS)
            rhs = ((2 / 3) ** (n - 1) - (6 / 19) ** (n - 1)) / (n - 1)
            self.assertAlmostEqual(lhs, rhs, places=10)

    def test_iterate_inverse_square(self):
        def iterate(x, n):
            for _ in range(n):
                x = s3(x)
            return x

        def branch(i, t):
            return s3_branches(t)[i]

        for n in range(0, 4):
            pieces = [(1.5, 19 / 6)]
            for _ in range(n):
                pieces = [(branch(i, a), branch(i, b)) for a, b in pieces for i in range(3)]
            self.assertEqual(len(pieces), 3 ** n)
            total = sum(integrate(lambda x: iterate(x, n) ** -2, a, b, n=2000)
                        for a, b in pieces)
            self.assertAlmostEqual(total, 20 / 57, places=6)


class Integrals(unittest.TestCase):
    def test_measure_preservation(self):
        tests = [
            lambda x: math.exp(-x * x),
            lambda x: 1 / (1 + x * x),
            lambda x: math.exp(-abs(x - 1)),
        ]
        for g in tests:
            lhs = integrate_line(lambda x: g(boole(x)))
            rhs = integrate_line(g)
            self.assertAlmostEqual(lhs, rhs, delta=2e-3 * abs(rhs))


class LeanSource(unittest.TestCase):
    def test_no_holes_and_main_declarations_present(self):
        source = LEAN.read_text(encoding='utf-8')
        self.assertIsNone(re.search(r'^\s*(axiom|sorry)\b', source, re.M))
        self.assertNotIn('sorry', source)
        self.assertNotIn('native_decide', source)
        for name in ('integral_comp_eq_of_branches', 'boole_integral', 'booleBranch_inv',
                     'booleBranchDeriv_sum', 'booleBranch_surj', 'exists_inverse_branch',
                     'S3_cubic', 'root_sum', 'S3_bounds', 'S3_integral',
                     'measurePreserving_of_branches', 'S3_measurePreserving',
                     'S3_preimage_Icc', 'three_interval_integral', 'iterate_integral_inv_sq'):
            self.assertIsNotNone(
                re.search(r'^theorem ' + name + r'\b', source, re.M), name)


if __name__ == '__main__':
    unittest.main()
