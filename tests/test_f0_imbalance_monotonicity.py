"""Independent integer checks for lean/Research/F0ImbalanceMonotonicity.lean.

Python standard library only. The Lean module proves the general statements;
these checks recompute them by exhaustive enumeration on small sizes, with code
that does not reuse the Lean proof structure:

* every two-block transfer (a, b) -> (a + 1, b - 1), a >= b > 1, strictly
  increases Phi_d for all integer partitions with N <= 20 and d = 1, 2, 3;
* the hook (N - r + 1, 1^(r - 1)) is the unique maximiser of Phi_d among the
  partitions of N into r positive parts (N <= 16);
* the exchange and log-convexity inequalities used in the proof;
* Phi_1 equals the number of actual maps S with S o K = K o S for every
  idempotent K on 1..5 labelled points (the B-compatible count of the source);
* the numerical examples quoted from the F0 source notes;
* numerical evidence only (not proved in Lean): for N <= 16 and fixed r,
  every strictly majorizing type has strictly larger Phi_1.
"""
from __future__ import annotations

import itertools
import re
from itertools import accumulate
import unittest
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / 'lean' / 'Research' / 'F0ImbalanceMonotonicity.lean'


def phi(parts, d=1):
    value = 1
    for mi in parts:
        value *= sum(mj ** (mi - 1) for mj in parts) ** d
    return value


def partitions(n, largest=None):
    if largest is None:
        largest = n
    if n == 0:
        yield ()
        return
    for k in range(min(n, largest), 0, -1):
        for rest in partitions(n - k, k):
            yield (k,) + rest


def transfers(parts):
    seen = set()
    for i, a in enumerate(parts):
        for j, b in enumerate(parts):
            if i != j and a >= b > 1 and (a, b) not in seen:
                seen.add((a, b))
                new = list(parts)
                new[i], new[j] = a + 1, b - 1
                yield (a, b), tuple(sorted(new, reverse=True))


def hook(n, r):
    return (n - r + 1,) + (1,) * (r - 1)


class TransferMonotonicity(unittest.TestCase):
    def test_every_transfer_strictly_increases(self):
        moves = 0
        for n in range(1, 21):
            for p in partitions(n):
                for _, q in transfers(p):
                    self.assertEqual(sum(q), n)
                    self.assertEqual(len(q), len(p))
                    for d in (1, 2, 3):
                        self.assertLess(phi(p, d), phi(q, d), (p, q, d))
                    moves += 1
        self.assertEqual(moves, 6750)

    def test_d_zero_is_constant(self):
        self.assertEqual(phi((4, 3), 0), phi((5, 2), 0))

    def test_hook_is_unique_maximiser(self):
        for n in range(1, 17):
            by_length = {}
            for p in partitions(n):
                by_length.setdefault(len(p), []).append(p)
            for r, ps in by_length.items():
                self.assertIn(hook(n, r), ps)
                for d in (1, 2):
                    best = max(phi(p, d) for p in ps)
                    winners = [p for p in ps if phi(p, d) == best]
                    self.assertEqual(winners, [hook(n, r)], (n, r, d))


    def test_majorization_order_numerically(self):
        # Hand-proof consequence via the integer transfer lemma; Lean does not
        # formalize majorization, so this is recorded as a finite check only.
        pairs = 0
        for n in range(1, 17):
            by_length = {}
            for p in partitions(n):
                by_length.setdefault(len(p), []).append(p)
            for ps in by_length.values():
                for x in ps:
                    for y in ps:
                        if x != y and all(
                                a >= b for a, b in zip(accumulate(x), accumulate(y))):
                            self.assertGreater(phi(x), phi(y), (x, y))
                            pairs += 1
        self.assertEqual(pairs, 6322)


class ProofInequalities(unittest.TestCase):
    def test_exchange_inequality(self):
        for a in range(0, 12):
            for c in range(0, a + 1):
                for n in range(0, 10):
                    lhs = a ** n + (c + 1) ** n
                    rhs = (a + 1) ** n + c ** n
                    self.assertLessEqual(lhs, rhs)
                    if c < a and n >= 2:
                        self.assertLess(lhs, rhs)
                    if c == a or n < 2:
                        self.assertEqual(lhs, rhs)

    def test_power_sum_log_convexity(self):
        def p(xs, e):
            return sum(x ** e for x in xs)

        for xs in itertools.combinations_with_replacement(range(0, 6), 3):
            for e in range(0, 5):
                for k in range(0, 5):
                    self.assertLessEqual(p(xs, e + 1) * p(xs, e + k),
                                         p(xs, e) * p(xs, e + k + 1))


class CompatibleCount(unittest.TestCase):
    """Phi_1 counts actual maps commuting with an idempotent K (d = 1)."""

    def test_phi_counts_commuting_maps(self):
        checked = 0
        for size in range(1, 6):
            points = range(size)
            for k in itertools.product(points, repeat=size):
                if any(k[k[x]] != k[x] for x in points):
                    continue
                fibres = sorted(Counter(k).values(), reverse=True)
                count = sum(
                    1 for s in itertools.product(points, repeat=size)
                    if all(s[k[x]] == k[s[x]] for x in points))
                self.assertEqual(count, phi(fibres), (k, fibres))
                checked += 1
        # Idempotent maps on 1..5 points: 1, 3, 10, 41, 196.
        self.assertEqual(checked, 1 + 3 + 10 + 41 + 196)


class SourceExamples(unittest.TestCase):
    def test_fixed_r_chain(self):
        self.assertEqual(phi((4, 3), 2), 5_175_625)
        self.assertEqual(phi((5, 2), 2), 20_133_169)
        self.assertEqual(phi((6, 1), 2), 241_926_916)

    def test_merges_are_not_monotone(self):
        self.assertEqual(phi((4, 1, 1, 1), 2), 18_386_944)
        self.assertEqual(phi((5, 1, 1), 2), 31_843_449)
        self.assertEqual(phi((1,) * 7, 2), 678_223_072_849)
        self.assertEqual(phi((7,), 2), 13_841_287_201)


class LeanSource(unittest.TestCase):
    def test_no_holes_and_main_declarations_present(self):
        source = LEAN.read_text(encoding='utf-8')
        self.assertIsNone(re.search(r'^\s*(axiom|sorry)\b', source, re.M))
        self.assertNotIn('sorry', source)
        self.assertNotIn('native_decide', source)
        for name in ('phi_lt_of_transfer', 'phi_lt_of_transGen', 'phi_lt_hook',
                     'phi_le_hook', 'phi_map_univ', 'pow_exchange_lt',
                     'powerSum_mul_le', 'merge_can_increase'):
            self.assertIsNotNone(
                re.search(r'^theorem ' + name + r'\b', source, re.M), name)


if __name__ == '__main__':
    unittest.main()
