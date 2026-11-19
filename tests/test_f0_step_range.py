"""Independent finite checks for lean/Research/F0StepRange.lean.

Python standard library only. For every idempotent K on 1..3 points with one
output component, and on 1..2 points with two components, all S and C are
enumerated and the set of updates T = K o C o K^(d) o S is computed directly:
without conditions it has r^N elements, under condition B (S o K = K^(d) o S)
r^r elements, and under A (C o S = id) together with B it is exactly {K}.
"""
from __future__ import annotations

import itertools
import re
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / 'lean' / 'Research' / 'F0StepRange.lean'


def idempotents(n):
    for k in itertools.product(range(n), repeat=n):
        if all(k[k[x]] == k[x] for x in range(n)):
            yield k


def update_sets(k, d):
    n = len(k)
    pts = range(n)
    outs = list(itertools.product(pts, repeat=d))
    index = {o: i for i, o in enumerate(outs)}
    free, with_b, with_ab = set(), set(), set()
    for s in itertools.product(outs, repeat=n):
        compatible = all(s[k[x]] == tuple(k[v] for v in s[x]) for x in pts)
        for c in itertools.product(pts, repeat=len(outs)):
            t = tuple(k[c[index[tuple(k[v] for v in s[x])]]] for x in pts)
            free.add(t)
            if compatible:
                with_b.add(t)
                if all(c[index[s[x]]] == x for x in pts):
                    with_ab.add(t)
    return free, with_b, with_ab


class Ranges(unittest.TestCase):
    def check(self, n, d):
        for k in idempotents(n):
            r = len(set(k))
            free, with_b, with_ab = update_sets(k, d)
            self.assertEqual(len(free), r ** n, k)
            self.assertEqual(len(with_b), r ** r, k)
            self.assertEqual(with_ab, {tuple(k)}, k)
            # characterisations, not only counts
            fixed = {a for a in range(n) if k[a] == a}
            self.assertTrue(all(set(t) <= fixed for t in free))
            self.assertTrue(all(t[k[x]] == t[x] for t in with_b for x in range(n)))

    def test_one_component(self):
        for n in range(1, 4):
            self.check(n, 1)

    def test_two_components(self):
        for n in range(1, 3):
            self.check(n, 2)


class LeanSource(unittest.TestCase):
    def test_no_holes_and_main_declarations_present(self):
        source = LEAN.read_text(encoding='utf-8')
        self.assertIsNone(re.search(r'^\s*(axiom|sorry)\b', source, re.M))
        self.assertNotIn('sorry', source)
        self.assertNotIn('native_decide', source)
        for name in ('range_free', 'range_compatible', 'range_reconstructs_compatible',
                     'card_free', 'card_compatible', 'card_reconstructs_compatible',
                     'example_seven_points'):
            self.assertIsNotNone(
                re.search(r'^theorem ' + name + r'\b', source, re.M), name)


if __name__ == '__main__':
    unittest.main()
