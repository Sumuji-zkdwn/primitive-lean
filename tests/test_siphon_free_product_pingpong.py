"""Independent exact checks for lean/Research/SiphonFreeProduct.lean.

Python standard library only, with exact integer polynomial arithmetic in one
variable t (pairs of polynomials are the points of ZZ[t]^2 on which the Lean
ping-pong argument runs). Checked here:

* L^6 = id, b^2 = id with b = E o (-id), and E = b a^3, on random integer
  polynomial pairs;
* the closed form E^h = (u + h r^2, r - (u + h r^2)^3), r = v + u^3;
* the invariants of the ping-pong sets: E^h z (h >= 1, deg z2 <= deg z1, deg z1 >= 1)
  has deg = (6d, 18d), positive leading coefficient and lc v = -(lc u)^3; L^k of such
  a point (1 <= k <= 5) leaves this set; for k != 3, -L^k of it is again dominated
  by its first coordinate; b L^3 E^h z = E^(h+1) z;
* every reduced word with at most 2 b-syllables, and four with 3 b-syllables,
  moves the point (t, 0), so it is not the identity.
"""
from __future__ import annotations

import itertools
import random
import re
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / 'lean' / 'Research' / 'SiphonFreeProduct.lean'


def norm(p):
    p = list(p)
    while p and p[-1] == 0:
        p.pop()
    return tuple(p)


def add(p, q):
    n = max(len(p), len(q))
    return norm([(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)])


def neg(p):
    return tuple(-c for c in p)


def sub(p, q):
    return add(p, neg(q))


def mul(p, q):
    if not p or not q:
        return ()
    out = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q):
                out[i + j] += a * b
    return norm(out)


def power(p, n):
    out = (1,)
    for _ in range(n):
        out = mul(out, p)
    return out


def scal(c, p):
    return norm([c * x for x in p])


def deg(p):
    return len(p) - 1  # deg 0 = -1 by convention here


def lc(p):
    return p[-1]


def L(z):
    u, v = z
    return (v, sub(v, u))


def rr(z):
    u, v = z
    return add(v, power(u, 3))


def E(z):
    u, v = z
    r = rr(z)
    u2 = add(u, power(r, 2))
    return (u2, sub(r, power(u2, 3)))


def E_iter(h, z):
    u, v = z
    r = rr(z)
    u2 = add(u, scal(h, power(r, 2)))
    return (u2, sub(r, power(u2, 3)))


def B(z):
    return E((neg(z[0]), neg(z[1])))


def Lpow(k, z):
    for _ in range(k):
        z = L(z)
    return z


def rand_poly(rng, d):
    return norm([rng.randint(-3, 3) for _ in range(d)] + [rng.choice([-2, -1, 1, 2])])


def in_zset(z):
    return deg(z[0]) >= 1 and deg(z[1]) <= deg(z[0])


def in_top(z):
    u, v = z
    return (deg(u) >= 1 and deg(v) == 3 * deg(u) and lc(u) > 0 and lc(v) == -lc(u) ** 3)


class Relations(unittest.TestCase):
    def test_orders_and_E(self):
        rng = random.Random(1)
        for _ in range(20):
            z = (rand_poly(rng, rng.randint(0, 2)), rand_poly(rng, rng.randint(0, 2)))
            self.assertEqual(Lpow(6, z), z)
            self.assertEqual(B(B(z)), z)
            self.assertEqual(B(Lpow(3, z)), E(z))  # E = b a^3 (a^3 applied first)

    def test_closed_form(self):
        rng = random.Random(2)
        for _ in range(10):
            z = (rand_poly(rng, 1), rand_poly(rng, 1))
            w = z
            for h in range(1, 4):
                w = E(w)
                self.assertEqual(w, E_iter(h, z))


class PingPongSets(unittest.TestCase):
    def test_invariants(self):
        rng = random.Random(3)
        for _ in range(12):
            d = rng.randint(1, 2)
            z = (rand_poly(rng, d), rand_poly(rng, rng.randint(0, d)))
            self.assertTrue(in_zset(z))
            for h in (1, 2, 3):
                y = E_iter(h, z)
                self.assertTrue(in_top(y))
                self.assertEqual(deg(y[0]), 6 * d)
                for k in range(1, 6):
                    x = Lpow(k, y)
                    self.assertFalse(in_top(x))
                    if k != 3:
                        self.assertTrue(in_zset((neg(x[0]), neg(x[1]))))
                self.assertEqual(B(Lpow(3, y)), E_iter(h + 1, z))


class ReducedWords(unittest.TestCase):
    def test_reduced_words_move_the_line(self):
        start = ((0, 1), ())  # the point (t, 0)
        checked = 0
        for s in range(1, 4):
            # a^{j0} b a^{j1} ... b a^{js}; interior exponents 1..5, ends 0..5
            for ends in itertools.product(range(6), repeat=2):
                if s == 3 and ends != (0, 0):
                    continue
                for inner in itertools.product(range(1, 6), repeat=s - 1):
                    if s == 3 and inner not in ((1, 2), (3, 3), (5, 4), (3, 1)):
                        continue
                    exps = (ends[1],) + inner + (ends[0],)  # applied right to left
                    z = Lpow(exps[0], start)
                    for e in exps[1:]:
                        z = Lpow(e, B(z))
                    self.assertNotEqual(z, start)
                    self.assertGreaterEqual(max(deg(z[0]), deg(z[1])), 2)
                    checked += 1
        self.assertEqual(checked, 36 + 36 * 5 + 4)


class LeanSource(unittest.TestCase):
    def test_no_holes_and_main_declarations_present(self):
        source = LEAN.read_text(encoding='utf-8')
        self.assertIsNone(re.search(r'^\s*(axiom|sorry)\b', source, re.M))
        self.assertNotIn('sorry', source)
        self.assertNotIn('native_decide', source)
        for name in ('phi_poly_injective', 'phi_real_injective', 'range_phi', 'EIter_mem_Top',
                     'Lpow_not_mem_Top', 'Bperm_maps_Xa', 'pmap_phi'):
            self.assertIsNotNone(re.search(r'^theorem ' + name + r'\b', source, re.M), name)
        self.assertIn('noncomputable def freeProductEquiv', source)


if __name__ == '__main__':
    unittest.main()
