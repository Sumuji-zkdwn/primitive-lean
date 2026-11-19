"""Independent exact checks for lean/OrbitTraceRankFormula.lean.

Python standard library only (fractions). The moments are rebuilt from the
recurrence M_k = X^k (k <= p), M_k = X M_(k-1) - a M_(k-p-1) (k >= p+1); the
operator N = L - I acts on V_d = Q[X]_{<= d} by N(X^k) = M_k - X^k. Ranks of
N^j are computed by exact Gaussian elimination over the rationals and compared
with the closed forms proved in Lean:

* rank N^j = max(0, d + 1 - j (p + 1));
* dim (V_d cap ker N^j) = min(j (p + 1), d + 1);
* rank N^j - rank N^(j+1) = #{r <= p : chainLength(p, d, r) >= j + 1};
* the image of V_d under N^j is exactly V_{d - j (p+1)} (degree test).
"""
from __future__ import annotations

import re
import unittest
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / 'lean' / 'OrbitTraceRankFormula.lean'


def moments(p, a, kmax):
    """Coefficient lists (index = degree) of M_0..M_kmax."""
    ms = []
    for k in range(kmax + 1):
        if k <= p:
            ms.append([Fraction(0)] * k + [Fraction(1)])
        else:
            shifted = [Fraction(0)] + ms[k - 1]
            low = ms[k - p - 1]
            out = shifted[:]
            for i, c in enumerate(low):
                out[i] -= a * c
            ms.append(out)
    return ms


def delta_matrix(p, a, d):
    """Columns: images of X^0..X^d under N, as length d+1 coefficient vectors."""
    ms = moments(p, a, d)
    cols = []
    for k in range(d + 1):
        v = ms[k] + [Fraction(0)] * (d + 1 - len(ms[k]))
        v[k] -= 1
        cols.append(v[:d + 1])
    return [[cols[c][r] for c in range(d + 1)] for r in range(d + 1)]


def matmul(x, y):
    n = len(x)
    return [[sum(x[i][l] * y[l][j] for l in range(n)) for j in range(n)] for i in range(n)]


def rank(m):
    m = [row[:] for row in m]
    rows, cols, r = len(m), len(m[0]) if m else 0, 0
    for c in range(cols):
        pivot = next((i for i in range(r, rows) if m[i][c] != 0), None)
        if pivot is None:
            continue
        m[r], m[pivot] = m[pivot], m[r]
        for i in range(rows):
            if i != r and m[i][c] != 0:
                f = m[i][c] / m[r][c]
                m[i] = [x - f * y for x, y in zip(m[i], m[r])]
        r += 1
    return r


def chain_length(p, d, r):
    return (d - r) // (p + 1) + 1 if r <= d else 0


class RankFormula(unittest.TestCase):
    def test_rank_kernel_and_chain_counts(self):
        cases = 0
        for p in range(0, 5):
            for d in range(0, 13):
                for a in (Fraction(1), Fraction(-2), Fraction(1, 3)):
                    n = delta_matrix(p, a, d)
                    power = [[Fraction(int(i == j)) for j in range(d + 1)] for i in range(d + 1)]
                    ranks = []
                    for j in range(d + 3):
                        ranks.append(rank(power))
                        q = j * (p + 1)
                        self.assertEqual(ranks[-1], max(0, d + 1 - q), (p, d, a, j))
                        self.assertEqual(d + 1 - ranks[-1], min(q, d + 1))
                        # the image has degree exactly d - j(p+1): its top row block
                        if q <= d:
                            top = d - q
                            self.assertTrue(any(power[top][c] != 0 for c in range(d + 1)))
                            self.assertTrue(all(power[r][c] == 0 for r in range(top + 1, d + 1)
                                                for c in range(d + 1)))
                        power = matmul(n, power)
                        cases += 1
                    for j in range(d + 2):
                        count = sum(1 for r in range(p + 1) if chain_length(p, d, r) >= j + 1)
                        self.assertEqual(ranks[j] - ranks[j + 1], count, (p, d, a, j))
        self.assertGreater(cases, 1000)

    def test_section_five_example(self):
        n = delta_matrix(3, Fraction(1), 11)
        power = [[Fraction(int(i == j)) for j in range(12)] for i in range(12)]
        ranks = []
        for _ in range(4):
            ranks.append(rank(power))
            power = matmul(n, power)
        self.assertEqual(ranks, [12, 8, 4, 0])

    def test_a_zero_is_excluded(self):
        # With a = 0 the moments are X^k, N = 0, and the formula fails for d > p.
        self.assertEqual(rank(delta_matrix(1, Fraction(0), 5)), 0)


class LeanSource(unittest.TestCase):
    def test_no_holes_and_main_declarations_present(self):
        source = LEAN.read_text(encoding='utf-8')
        self.assertIsNone(re.search(r'^\s*(axiom|sorry)\b', source, re.M))
        self.assertNotIn('sorry', source)
        self.assertNotIn('native_decide', source)
        for name in ('canonicalDelta_exactShift', 'canonicalDelta_pow_rank',
                     'canonicalDelta_pow_image', 'canonicalDelta_pow_ker_rank',
                     'canonicalDelta_nilpotency_index', 'canonicalDelta_chain_count',
                     'ExactShift.map_degreeLT'):
            self.assertIsNotNone(
                re.search(r'^theorem ' + re.escape(name) + r'\b', source, re.M), name)


if __name__ == '__main__':
    unittest.main()
