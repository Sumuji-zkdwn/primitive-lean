"""Independent checks for lean/Research/F0TypeCount.lean.

Python standard library only.

* For N <= 6, all idempotent maps on N labelled points are enumerated and
  grouped by block-size type; each count I(lambda) must equal
  N! / (prod (m - 1)! * prod_k c_k!).
* The K_type column of the source data
  sources/f0_math_chat_2026-10-29/data/partition_counts_N01_to_N12.csv
  (computed independently in the original archive) must match the formula
  for every partition with N <= 12.
* The multinomial step: functions with prescribed fibre sizes are counted by
  brute force for small domains.
"""
from __future__ import annotations

import csv
import itertools
import re
import unittest
from collections import Counter
from math import factorial, prod
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / 'lean' / 'Research' / 'F0TypeCount.lean'
CSV = ROOT / 'sources' / 'f0_math_chat_2026-10-29' / 'data' / 'partition_counts_N01_to_N12.csv'


def formula(parts):
    n = sum(parts)
    denom = prod(factorial(m - 1) for m in parts) * prod(
        factorial(c) for c in Counter(parts).values())
    assert factorial(n) % denom == 0
    return factorial(n) // denom


class TypeCount(unittest.TestCase):
    def test_enumeration(self):
        for n in range(1, 7):
            counts = Counter()
            for k in itertools.product(range(n), repeat=n):
                if all(k[k[x]] == k[x] for x in range(n)):
                    counts[tuple(sorted(Counter(k).values(), reverse=True))] += 1
            for parts, c in counts.items():
                self.assertEqual(c, formula(parts), (n, parts))
            self.assertEqual(sum(counts.values()),
                             sum(factorial(n) // (factorial(r) * factorial(n - r)) * r ** (n - r)
                                 for r in range(1, n + 1)))

    def test_source_table(self):
        rows = 0
        with CSV.open(encoding='utf-8') as handle:
            for row in csv.DictReader(handle):
                parts = tuple(int(x) for x in row['partition'].strip('()').split(','))
                self.assertEqual(sum(parts), int(row['N']))
                self.assertEqual(int(row['K_type']), formula(parts), row)
                rows += 1
        self.assertEqual(rows, 271)

    def test_seven_point_examples(self):
        self.assertEqual(formula((4, 3)), 420)
        self.assertEqual(formula((3, 2, 2)), 1260)

    def test_multinomial_step(self):
        for n in range(0, 6):
            for target in range(1, 4):
                classes = Counter()
                for g in itertools.product(range(target), repeat=n):
                    classes[tuple(g.count(i) for i in range(target))] += 1
                for sizes, c in classes.items():
                    self.assertEqual(c * prod(factorial(s) for s in sizes), factorial(n))


class LeanSource(unittest.TestCase):
    def test_no_holes_and_main_declarations_present(self):
        source = LEAN.read_text(encoding='utf-8')
        self.assertIsNone(re.search(r'^\s*(axiom|sorry)\b', source, re.M))
        self.assertNotIn('sorry', source)
        self.assertNotIn('native_decide', source)
        for name in ('card_sameFibers_mul', 'exists_perm_comp_eq', 'type_eq_iff_fin',
                     'card_type_mul', 'seven_points_43', 'seven_points_322'):
            self.assertIsNotNone(
                re.search(r'^theorem ' + name + r'\b', source, re.M), name)
        self.assertIsNotNone(re.search(r'^def profileEquiv\b', source, re.M))


if __name__ == '__main__':
    unittest.main()
