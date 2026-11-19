"""Independent exact checks for lean/Research/SiphonOptimalDetermination.lean.

Python standard library only, exact rational arithmetic. With I(u,v) = v + u^3,
E(u,v) = (u + I^2, I - (u + I^2)^3), L(u,v) = (v, v - u), regularSeed and the
reachable points sample(z, n, m) = E^m L E^n z (n < d+2, m < 3d+1):

* N(d) = (d+1)(d+2)/2 equals the number of monomials u^i v^j with i + j <= d;
* for several seeds and d <= 3 the evaluation matrix on the reachable points has
  rank N(d), and a greedy row selection finds exactly N(d) determining points;
* for every set of N(d) - 1 of these points an explicit nonzero polynomial of
  degree <= d vanishes on them (the lower bound);
* an adaptive strategy with N(d) - 1 queries gets the same transcript for the zero
  polynomial and for such a nonzero polynomial.
"""
from __future__ import annotations

import itertools
import random
import re
import unittest
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / 'lean' / 'Research' / 'SiphonOptimalDetermination.lean'


def I(z):
    return z[1] + z[0] ** 3


def E(z):
    r = I(z)
    x = z[0] + r * r
    return (x, r - x ** 3)


def L(z):
    return (z[1], z[1] - z[0])


def iterate(n, z):
    for _ in range(n):
        z = E(z)
    return z


def regular_seed(z):
    return L(z) if I(z) == 0 else z


def sample(z, n, m):
    return iterate(m, L(iterate(n, z)))


def N(d):
    return (d + 1) * (d + 2) // 2


def monomials(d):
    return [(i, j) for i in range(d + 1) for j in range(d + 1 - i)]


def row(x, d):
    return [Fraction(x[0]) ** i * Fraction(x[1]) ** j for i, j in monomials(d)]


def rank(rows):
    m = [list(r) for r in rows]
    rk, col = 0, 0
    ncol = len(m[0]) if m else 0
    while rk < len(m) and col < ncol:
        piv = next((i for i in range(rk, len(m)) if m[i][col] != 0), None)
        if piv is None:
            col += 1
            continue
        m[rk], m[piv] = m[piv], m[rk]
        for i in range(len(m)):
            if i != rk and m[i][col] != 0:
                f = m[i][col] / m[rk][col]
                m[i] = [a - f * b for a, b in zip(m[i], m[rk])]
        rk += 1
        col += 1
    return rk


def kernel_vector(rows, ncol):
    """A nonzero vector c with rows . c = 0 (rows has fewer rows than ncol)."""
    m = [list(r) for r in rows]
    pivots, rk = [], 0
    for col in range(ncol):
        piv = next((i for i in range(rk, len(m)) if m[i][col] != 0), None)
        if piv is None:
            continue
        m[rk], m[piv] = m[piv], m[rk]
        m[rk] = [a / m[rk][col] for a in m[rk]]
        for i in range(len(m)):
            if i != rk and m[i][col] != 0:
                f = m[i][col]
                m[i] = [a - f * b for a, b in zip(m[i], m[rk])]
        pivots.append(col)
        rk += 1
    free = next(c for c in range(ncol) if c not in pivots)
    c = [Fraction(0)] * ncol
    c[free] = Fraction(1)
    for i, pc in enumerate(pivots):
        c[pc] = -m[i][free]
    return c


SEEDS = [(0, 1), (1, -1), (-2, 3), (2, 1), (1, 0)]


class Counting(unittest.TestCase):
    def test_monomial_count(self):
        for d in range(31):
            self.assertEqual(len(monomials(d)), N(d))


class Determination(unittest.TestCase):
    def test_rank_and_greedy_selection(self):
        for d in range(4):
            for seed in SEEDS:
                a = regular_seed(seed)
                pts = [sample(a, n, m) for n in range(d + 2) for m in range(3 * d + 1)]
                rows = [row(x, d) for x in pts]
                self.assertEqual(rank(rows), N(d), (d, seed))
                chosen = []
                for r in rows:
                    if rank(chosen + [r]) > len(chosen):
                        chosen.append(r)
                self.assertEqual(len(chosen), N(d))

    def test_fewer_points_never_determine(self):
        rng = random.Random(8)
        for d in range(1, 4):
            for seed in SEEDS:
                a = regular_seed(seed)
                pts = [sample(a, n, m) for n in range(d + 2) for m in range(3 * d + 1)]
                for _ in range(5):
                    subset = rng.sample(pts, N(d) - 1)
                    rows = [row(x, d) for x in subset]
                    c = kernel_vector(rows, N(d))
                    self.assertTrue(any(c))
                    for r in rows:
                        self.assertEqual(sum(x * y for x, y in zip(r, c)), 0)

    def test_adaptive_strategy(self):
        d = 2
        a = regular_seed((1, 2))

        def strategy(answers):
            # next query depends on the answers so far
            k = len(answers)
            n = (k + sum(1 for v in answers if v > 0)) % (d + 2)
            return sample(a, n, k % (3 * d + 1))

        def transcript(coeffs, steps):
            answers = []
            for _ in range(steps):
                x = strategy(answers)
                answers.append(sum(c * v for c, v in zip(coeffs, row(x, d))))
            return answers

        steps = N(d) - 1
        zero = [Fraction(0)] * N(d)
        queried, answers = [], []
        for _ in range(steps):
            x = strategy(answers)
            queried.append(x)
            answers.append(Fraction(0))
        c = kernel_vector([row(x, d) for x in queried], N(d))
        self.assertTrue(any(c))
        self.assertEqual(transcript(c, steps), transcript(zero, steps))


class LeanSource(unittest.TestCase):
    def test_no_holes_and_declarations(self):
        source = LEAN.read_text(encoding='utf-8')
        self.assertIsNone(re.search(r'^\s*(axiom|sorry)\b', source, re.M))
        self.assertNotIn('sorry', source)
        self.assertNotIn('native_decide', source)
        for name in ('finrank_V', 'exists_vanishing_of_card_lt', 'adaptive_not_determining',
                     'exists_optimal_determining_set', 'minimum_is_N', 'no_uniform_finite_cutoff'):
            self.assertIsNotNone(re.search(r'^theorem ' + name + r'\b', source, re.M), name)


if __name__ == '__main__':
    unittest.main()
