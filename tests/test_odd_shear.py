"""Independent exact checks for lean/Research/OddShear.lean.

Python standard library only, exact rational arithmetic (fractions). For
E_d = H_d^{-1} o L o H_d with L(u,v) = (v, v-u), H_d(u,v) = (u + v^d, v):

* E_d^6 = id for d = 0..9 on random rational points;
* E_d^3 = -id exactly for odd d, and E_d^3(0,1) = (-2,-1) for even d;
* Q o H_d is invariant, Q(u,v) = u^2 - uv + v^2;
* the explicit partial derivatives of the Lean file match central differences
  (floating point) and their determinant is exactly 1;
* the d = 3 case uses the same formulas as lean/OrbitTrace.lean.
"""
from __future__ import annotations

import random
import re
import unittest
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / 'lean' / 'Research' / 'OddShear.lean'


def L(z):
    u, v = z
    return (v, v - u)


def H(d, z):
    u, v = z
    return (u + v ** d, v)


def Hinv(d, z):
    u, v = z
    return (u - v ** d, v)


def Ed(d, z):
    return Hinv(d, L(H(d, z)))


def it(d, n, z):
    for _ in range(n):
        z = Ed(d, z)
    return z


def Q(z):
    u, v = z
    return u * u - u * v + v * v


def partials(d, u, v):
    g = v - u - v ** d
    gd = g ** (d - 1) if d >= 1 else 0
    vd = v ** (d - 1) if d >= 1 else 0
    return (d * gd, 1 - d * gd * (1 - d * vd), -1, 1 - d * vd)


class Orders(unittest.TestCase):
    def test_six_and_three(self):
        rng = random.Random(9)
        for d in range(10):
            for _ in range(6):
                z = (Fraction(rng.randint(-9, 9), rng.randint(1, 5)),
                     Fraction(rng.randint(-9, 9), rng.randint(1, 5)))
                self.assertEqual(it(d, 6, z), z)
                cube = it(d, 3, z)
                if d % 2 == 1:
                    self.assertEqual(cube, (-z[0], -z[1]))
                self.assertEqual(Q(H(d, Ed(d, z))), Q(H(d, z)))
            if d % 2 == 0:
                self.assertEqual(it(d, 3, (Fraction(0), Fraction(1))), (-2, -1))


class Jacobian(unittest.TestCase):
    def test_partials_and_determinant(self):
        rng = random.Random(4)
        for d in range(1, 8):
            for _ in range(5):
                u, v = rng.uniform(-1.2, 1.2), rng.uniform(-1.2, 1.2)
                fu, fv, gu, gv = partials(d, u, v)
                h = 1e-6
                num = [
                    (Ed(d, (u + h, v))[0] - Ed(d, (u - h, v))[0]) / (2 * h),
                    (Ed(d, (u, v + h))[0] - Ed(d, (u, v - h))[0]) / (2 * h),
                    (Ed(d, (u + h, v))[1] - Ed(d, (u - h, v))[1]) / (2 * h),
                    (Ed(d, (u, v + h))[1] - Ed(d, (u, v - h))[1]) / (2 * h),
                ]
                for a, b in zip((fu, fv, gu, gv), num):
                    self.assertAlmostEqual(a, b, delta=1e-5 * max(1.0, abs(a)))
                fu, fv, gu, gv = partials(d, Fraction(u), Fraction(v))
                self.assertEqual(fu * gv - fv * gu, 1)


class LeanSource(unittest.TestCase):
    def test_no_holes_and_declarations(self):
        source = LEAN.read_text(encoding='utf-8')
        self.assertIsNone(re.search(r'^\s*(axiom|sorry)\b', source, re.M))
        self.assertNotIn('sorry', source)
        self.assertNotIn('native_decide', source)
        for name in ('Ed_six', 'Ed_cube_iff', 'Ed_invariant', 'Ed_partials', 'Ed_jacobian'):
            self.assertIsNotNone(re.search(r'^theorem ' + name + r'\b', source, re.M), name)

    def test_d_three_matches_orbit_trace(self):
        old = (ROOT / 'lean' / 'OrbitTrace.lean').read_text(encoding='utf-8')
        self.assertIn('def linearE (z : ℝ × ℝ) : ℝ × ℝ := (z.2, z.2 - z.1)', old)
        self.assertIn('def shear (z : ℝ × ℝ) : ℝ × ℝ := (z.1 + z.2 ^ 3, z.2)', old)
        self.assertIn('def unshear (z : ℝ × ℝ) : ℝ × ℝ := (z.1 - z.2 ^ 3, z.2)', old)
        new = LEAN.read_text(encoding='utf-8')
        self.assertIn('def L (z : ℝ × ℝ) : ℝ × ℝ := (z.2, z.2 - z.1)', new)
        self.assertIn('def H (d : ℕ) (z : ℝ × ℝ) : ℝ × ℝ := (z.1 + z.2 ^ d, z.2)', new)


if __name__ == '__main__':
    unittest.main()
