"""Independent finite checks for lean/Research/F0DropCompatibility.lean.

Python standard library only. For every idempotent K on 1..4 labelled points
and every S with one output component (and, on 1..3 points, two components),
recompute by brute force:

* condition B (S o K = K^(d) o S) can fail  <=>  K is not the identity;
* B can fail without K^(d) o S separating K-equivalent points  <=>  K != id;
* some S separates  <=>  K is not injective and has at least two fixed points;
* the counts of B-compatible S and of non-separating S, against the product
  formulas prod_a (sum_b m_b^(m_a - 1))^d and prod_a (sum_b m_b^m_a)^d.
"""
from __future__ import annotations

import itertools
import re
import unittest
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / 'lean' / 'Research' / 'F0DropCompatibility.lean'


def idempotents(n):
    pts = range(n)
    for k in itertools.product(pts, repeat=n):
        if all(k[k[x]] == k[x] for x in pts):
            yield k


def maps_with_components(n, d):
    """All S : n -> n^d, encoded as a tuple of d-tuples."""
    outputs = list(itertools.product(range(n), repeat=d))
    return itertools.product(outputs, repeat=n)


def compatible(k, s):
    return all(s[k[x]] == tuple(k[v] for v in s[x]) for x in range(len(k)))


def separates(k, s):
    n = len(k)
    return any(k[x] == k[y] and tuple(k[v] for v in s[x]) != tuple(k[v] for v in s[y])
               for x in range(n) for y in range(n))


def product_formula(sizes, d, shift):
    value = 1
    for ma in sizes:
        value *= sum(mb ** (ma - shift) for mb in sizes) ** d
    return value


def classify(k, d):
    n = len(k)
    stats = Counter()
    for s in maps_with_components(n, d):
        c, sep = compatible(k, s), separates(k, s)
        stats['compatible'] += c
        stats['respecting'] += not sep
        stats['incompatible_respecting'] += (not c) and (not sep)
        stats['separating'] += sep
        assert not (c and sep), (k, s)  # B implies indistinguishability
    return stats


class Classification(unittest.TestCase):
    def check(self, n, d):
        seen = 0
        for k in idempotents(n):
            stats = classify(k, d)
            identity = all(k[x] == x for x in range(n))
            injective = len(set(k)) == n
            fixed = sum(1 for x in range(n) if k[x] == x)
            total = n ** (n * d)
            self.assertEqual(stats['compatible'] < total, not identity, k)
            self.assertEqual(stats['incompatible_respecting'] > 0, not identity, k)
            self.assertEqual(stats['separating'] > 0,
                             (not injective) and fixed >= 2, k)
            sizes = sorted(Counter(k).values())
            self.assertEqual(stats['compatible'], product_formula(sizes, d, 1), k)
            self.assertEqual(stats['respecting'], product_formula(sizes, d, 0), k)
            seen += 1
        return seen

    def test_one_component_up_to_four_points(self):
        counts = [self.check(n, 1) for n in range(1, 5)]
        self.assertEqual(counts, [1, 3, 10, 41])

    def test_two_components_up_to_three_points(self):
        counts = [self.check(n, 2) for n in range(1, 4)]
        self.assertEqual(counts, [1, 3, 10])


class SourceExample(unittest.TestCase):
    def test_conversation_example(self):
        k = (0, 0, 2)
        bad = ((0,), (2,), (0,))      # S = (0, 2, 0) from the source notes
        quiet = ((1,), (1,), (2,))    # S = (1, 1, 2)
        self.assertFalse(compatible(k, bad))
        self.assertTrue(separates(k, bad))
        self.assertFalse(compatible(k, quiet))
        self.assertFalse(separates(k, quiet))

    def test_single_block_never_separates(self):
        k = (0, 0, 0)
        self.assertFalse(any(separates(k, s) for s in maps_with_components(3, 1)))


class LeanSource(unittest.TestCase):
    def test_no_holes_and_main_declarations_present(self):
        source = LEAN.read_text(encoding='utf-8')
        self.assertIsNone(re.search(r'^\s*(axiom|sorry)\b', source, re.M))
        self.assertNotIn('sorry', source)
        self.assertNotIn('native_decide', source)
        for name in ('exists_incompatible_iff', 'exists_incompatible_respecting_iff',
                     'exists_separating_iff', 'drop_b_not_always', 'compatible_respects',
                     'respects_count', 'compatible_count', 'incompatible_respecting_count_eq',
                     'incompatible_respecting_count_pos_iff'):
            self.assertIsNotNone(
                re.search(r'^theorem ' + name + r'\b', source, re.M), name)


if __name__ == '__main__':
    unittest.main()
