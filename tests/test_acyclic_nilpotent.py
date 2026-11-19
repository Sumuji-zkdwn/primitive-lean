"""Independent finite checks for lean/Research/AcyclicNilpotent.lean.

Python standard library only. Recomputes, with integer matrix powers and a
separate depth-first cycle search:

* every digraph with loops allowed on 1..4 labelled vertices (0/1 weights):
  A^n = 0  <=>  no directed cycle  <=>  A^m = 0 for some m (checked up to 2n);
* all weights in {0, 1, 2} on 1..3 vertices, the same equivalence;
* for 0/1 matrices, (A^k)[i][j] equals the number of directed walks of length k;
* the signed counterexample [[1, 1], [-1, -1]], which squares to zero but has
  self-loops, and the two examples stated in the Lean file.
"""
from __future__ import annotations

import itertools
import re
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / 'lean' / 'Research' / 'AcyclicNilpotent.lean'


def matmul(a, b):
    n = len(a)
    return [[sum(a[i][l] * b[l][j] for l in range(n)) for j in range(n)] for i in range(n)]


def power(a, k):
    n = len(a)
    result = [[int(i == j) for j in range(n)] for i in range(n)]
    for _ in range(k):
        result = matmul(a, result)
    return result


def is_zero(m):
    return all(v == 0 for row in m for v in row)


def has_cycle(a):
    n = len(a)
    colour = [0] * n

    def visit(u):
        colour[u] = 1
        for v in range(n):
            if a[u][v] != 0 and (colour[v] == 1 or (colour[v] == 0 and visit(v))):
                return True
        colour[u] = 2
        return False

    return any(colour[i] == 0 and visit(i) for i in range(n))


def matrices(n, weights):
    for entries in itertools.product(weights, repeat=n * n):
        yield [list(entries[r * n:(r + 1) * n]) for r in range(n)]


def count_walks(a, k, i, j):
    n = len(a)
    if k == 0:
        return int(i == j)
    return sum(count_walks(a, k - 1, l, j) for l in range(n) if a[i][l])


class Equivalence(unittest.TestCase):
    def check(self, n, weights):
        acyclic = 0
        total = 0
        for a in matrices(n, weights):
            cyc = has_cycle(a)
            self.assertEqual(is_zero(power(a, n)), not cyc, a)
            # Nilpotency is already decided at exponent n.
            self.assertEqual(is_zero(power(a, 2 * n)), is_zero(power(a, n)), a)
            acyclic += not cyc
            total += 1
        return total, acyclic

    def test_all_unit_digraphs_up_to_four_vertices(self):
        # Labelled DAGs (no loops): 1, 3, 25, 543 (OEIS A003024).
        results = [self.check(n, (0, 1)) for n in range(1, 5)]
        self.assertEqual(results, [(2, 1), (16, 3), (512, 25), (65536, 543)])

    def test_nonnegative_weights_up_to_three_vertices(self):
        results = [self.check(n, (0, 1, 2)) for n in range(1, 4)]
        self.assertEqual([acyclic for _, acyclic in results], [1, 5, 109])

    def test_entries_count_walks(self):
        for a in matrices(3, (0, 1)):
            for k in range(4):
                p = power(a, k)
                for i in range(3):
                    for j in range(3):
                        self.assertEqual(p[i][j], count_walks(a, k, i, j))


class Examples(unittest.TestCase):
    def test_signed_counterexample(self):
        a = [[1, 1], [-1, -1]]
        self.assertTrue(is_zero(power(a, 2)))
        self.assertTrue(has_cycle(a))

    def test_lean_examples(self):
        tournament = [[0, 1, 1], [0, 0, 1], [0, 0, 0]]
        self.assertTrue(is_zero(power(tournament, 3)))
        swap = [[0, 1], [1, 0]]
        self.assertTrue(has_cycle(swap))
        self.assertFalse(any(is_zero(power(swap, k)) for k in range(1, 20)))


class LeanSource(unittest.TestCase):
    def test_no_holes_and_main_declarations_present(self):
        source = LEAN.read_text(encoding='utf-8')
        self.assertIsNone(re.search(r'^\s*(axiom|sorry)\b', source, re.M))
        self.assertNotIn('sorry', source)
        self.assertNotIn('native_decide', source)
        for name in ('pow_apply_ne_zero_iff', 'pow_card_eq_zero_iff_acyclic',
                     'isNilpotent_iff_acyclic', 'isNilpotent_iff_pow_card',
                     'signed_counterexample', 'hasCycle_of_walk'):
            self.assertIsNotNone(
                re.search(r'^theorem ' + name + r'\b', source, re.M), name)


if __name__ == '__main__':
    unittest.main()
