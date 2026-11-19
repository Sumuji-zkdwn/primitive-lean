"""Independent numerical checks for lean/OrbitTraceBoole.lean.

Python standard library only (floating point, so these are numerical checks,
not proofs). For Boole's map S(x) = x - 1/x:

* the explicit branches (t +- sqrt(t^2 + 4))/2 invert S, lie on opposite sides
  of 0, and have derivatives (checked by central differences) summing to 1;
* int g(S(x)) dx agrees with int g(x) dx for several integrable g, using the
  substitution x = sinh(u) style quadrature on a wide interval.
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
                     'booleBranchDeriv_sum', 'booleBranch_surj'):
            self.assertIsNotNone(
                re.search(r'^theorem ' + name + r'\b', source, re.M), name)


if __name__ == '__main__':
    unittest.main()
