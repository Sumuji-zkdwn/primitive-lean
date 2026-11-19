"""Independent exact checks for lean/OrbitTraceJordanBasis.lean.

Python standard library only. From the moment recurrence, build N = L - I on
V_d and the chain vectors v_{r,j} = N^(M_r - j) X^(r + M_r q), M_r = (d - r) // q.
Check that v_{r,j} has degree exactly r + j q, that N v_{r,0} = 0 and
N v_{r,j+1} = v_{r,j}, and that the matrix B whose column k is
v_{k mod q, k div q} is upper triangular with nonzero diagonal (so invertible)
and satisfies N B = B J for the nilpotent Jordan matrix J of the chains.
"""
from __future__ import annotations

import re
import unittest
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / 'lean' / 'OrbitTraceJordanBasis.lean'


def moments(p, a, kmax):
    ms = []
    for k in range(kmax + 1):
        if k <= p:
            ms.append([Fraction(0)] * k + [Fraction(1)])
        else:
            out = [Fraction(0)] + ms[k - 1]
            for i, c in enumerate(ms[k - p - 1]):
                out[i] -= a * c
            ms.append(out)
    return ms


def apply_delta(ms, vec):
    """N applied to a coefficient vector (index = degree)."""
    out = [Fraction(0)] * len(vec)
    for k, c in enumerate(vec):
        if c:
            for i, m in enumerate(ms[k]):
                out[i] += c * m
            out[k] -= c
    return out


def degree(vec):
    nz = [i for i, c in enumerate(vec) if c != 0]
    return nz[-1] if nz else None


def chain_vec(ms, p, d, r, j):
    q = p + 1
    top = (d - r) // q
    vec = [Fraction(0)] * (d + 1)
    vec[r + top * q] = Fraction(1)
    for _ in range(top - j):
        vec = apply_delta(ms, vec)
    return vec


class JordanBasis(unittest.TestCase):
    def test_chain_basis(self):
        cases = 0
        for p in range(0, 4):
            q = p + 1
            for d in range(0, 11):
                for a in (Fraction(1), Fraction(-3), Fraction(2, 5)):
                    ms = moments(p, a, d)
                    cols = []
                    for k in range(d + 1):
                        r, j = k % q, k // q
                        v = chain_vec(ms, p, d, r, j)
                        self.assertEqual(degree(v), k, (p, d, a, k))
                        nv = apply_delta(ms, v)
                        if j == 0:
                            self.assertTrue(all(c == 0 for c in nv))
                        else:
                            self.assertEqual(nv, chain_vec(ms, p, d, r, j - 1))
                        cols.append(v)
                    # B upper triangular with nonzero diagonal
                    for k in range(d + 1):
                        self.assertNotEqual(cols[k][k], 0)
                        self.assertTrue(all(cols[k][i] == 0 for i in range(k + 1, d + 1)))
                    # N B = B J, J e_k = e_{k-q} (k >= q) else 0
                    for k in range(d + 1):
                        lhs = apply_delta(ms, cols[k])
                        rhs = cols[k - q] if k >= q else [Fraction(0)] * (d + 1)
                        self.assertEqual(lhs, rhs)
                    cases += 1
        self.assertEqual(cases, 4 * 11 * 3)


class LeanSource(unittest.TestCase):
    def test_no_holes_and_main_declarations_present(self):
        source = LEAN.read_text(encoding='utf-8')
        self.assertIsNone(re.search(r'^\s*(axiom|sorry)\b', source, re.M))
        self.assertNotIn('sorry', source)
        self.assertNotIn('native_decide', source)
        for name in ('chainVec_natDegree', 'chainVec_bottom', 'chainVec_succ',
                     'jordan_linearIndependent', 'jordan_span', 'jordanElem_delta',
                     'chainTop_succ_eq_chainLength'):
            self.assertIsNotNone(
                re.search(r'^theorem ' + name + r'\b', source, re.M), name)


if __name__ == '__main__':
    unittest.main()
