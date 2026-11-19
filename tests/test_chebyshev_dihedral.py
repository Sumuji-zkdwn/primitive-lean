"""Independent numerical checks for lean/Research/ChebyshevDihedral.lean.

Python standard library only (complex floating point, so these are numerical
checks, not proofs). With zeta = exp(2 pi i / m):

* the maps r_i(z) = zeta^i z and sr_i(z) = zeta^i / z follow mathlib's
  DihedralGroup rules (r i * r j = r (i+j), r i * sr j = sr (j-i),
  sr i * r j = sr (i+j), sr i * sr j = r (j-i)) in the substitution
  convention of the Lean file: the automorphism of k(z) attached to g is
  f(z) -> f(g.z), so composing automorphisms g then h composes the point maps
  as h after g: h.(g.z) = (g*h).z. They are 2m distinct maps and fix
  t = z^m + z^(-m);
* the 2m roots of Y^(2m) - t Y^m + 1 are exactly the orbit of one root under
  these maps (transitivity, matching [k(z):k(t)] = 2m);
* y_j = zeta^j z + zeta^(-j) / z are m distinct roots of D_m(Y, 1) = t, z is
  recovered as (y_1 - zeta^(-1) y_0) / (zeta - zeta^(-1)), and in the note's
  normalization T_m(y_j / 2) = t / 2.
"""
from __future__ import annotations

import cmath
import random
import re
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / 'lean' / 'Research' / 'ChebyshevDihedral.lean'


def zeta(m):
    return cmath.exp(2j * cmath.pi / m)


def act(g, m, z):
    kind, i = g
    w = zeta(m) ** i
    return w * z if kind == 'r' else w / z


def mul(g, h, m):
    (a, i), (b, j) = g, h
    if a == 'r' and b == 'r':
        return ('r', (i + j) % m)
    if a == 'r' and b == 'sr':
        return ('sr', (j - i) % m)
    if a == 'sr' and b == 'r':
        return ('sr', (i + j) % m)
    return ('r', (j - i) % m)


def elements(m):
    return [(kind, i) for kind in ('r', 'sr') for i in range(m)]


def dickson(m, y):
    d0, d1 = 2, y
    if m == 0:
        return d0
    for _ in range(m - 1):
        d0, d1 = d1, y * d1 - d0
    return d1


def chebyshev_t(m, x):
    t0, t1 = 1, x
    if m == 0:
        return t0
    for _ in range(m - 1):
        t0, t1 = t1, 2 * x * t1 - t0
    return t1


def close(a, b, tol=1e-8):
    return abs(a - b) <= tol * max(1.0, abs(a), abs(b))


class DihedralAction(unittest.TestCase):
    def test_composition_faithfulness_invariance(self):
        rng = random.Random(11)
        for m in range(1, 10):
            for _ in range(3):
                z = complex(rng.uniform(0.3, 2), rng.uniform(-2, 2))
                for g in elements(m):
                    for h in elements(m):
                        self.assertTrue(close(act(h, m, act(g, m, z)), act(mul(g, h, m), m, z)))
                values = [act(g, m, z) for g in elements(m)]
                for a in range(len(values)):
                    for b in range(a):
                        self.assertGreater(abs(values[a] - values[b]), 1e-9)
                t = z ** m + z ** (-m)
                for g in elements(m):
                    w = act(g, m, z)
                    self.assertTrue(close(w ** m + w ** (-m), t))

    def test_orbit_is_all_roots(self):
        rng = random.Random(5)
        for m in range(1, 9):
            z = complex(rng.uniform(0.3, 2), rng.uniform(-2, 2))
            t = z ** m + z ** (-m)
            orbit = [act(g, m, z) for g in elements(m)]
            for w in orbit:
                self.assertTrue(close(w ** (2 * m) - t * w ** m + 1, 0, 1e-7))
            # a degree-2m polynomial has at most 2m roots: the orbit already has 2m distinct ones
            self.assertEqual(len(orbit), 2 * m)


class Splitting(unittest.TestCase):
    def test_dickson_roots_and_recovery(self):
        rng = random.Random(7)
        for m in range(3, 12):
            q = zeta(m)
            z = complex(rng.uniform(0.3, 2), rng.uniform(-2, 2))
            t = z ** m + z ** (-m)
            ys = [q ** j * z + q ** (-j) / z for j in range(m)]
            for y in ys:
                self.assertTrue(close(dickson(m, y), t, 1e-7))
                self.assertTrue(close(chebyshev_t(m, y / 2), t / 2, 1e-7))
            for a in range(m):
                for b in range(a):
                    self.assertGreater(abs(ys[a] - ys[b]), 1e-9)
            self.assertTrue(close((ys[1] - ys[0] / q) / (q - 1 / q), z))

    def test_small_m_has_no_recovery(self):
        # for m = 1, 2 the factor zeta - zeta^(-1) vanishes, matching the hypothesis 3 <= m
        for m in (1, 2):
            q = zeta(m)
            self.assertLess(abs(q - 1 / q), 1e-12)


class LeanSource(unittest.TestCase):
    def test_no_holes_and_main_declarations_present(self):
        source = LEAN.read_text(encoding='utf-8')
        self.assertIsNone(re.search(r'^\s*(axiom|sorry)\b', source, re.M))
        self.assertNotIn('sorry', source)
        self.assertNotIn('native_decide', source)
        for name in ('sigma_injective', 'sigma_tInv', 'finrank_le', 'finrank_baseField',
                     'isGalois_baseField', 'toGal_bijective', 'isSplittingField',
                     'chebyshev_T_root_half', 'adjoin_half_eq'):
            self.assertIsNotNone(re.search(r'^theorem ' + name + r'\b', source, re.M), name)
        self.assertIn('noncomputable def galEquiv', source)


if __name__ == '__main__':
    unittest.main()
