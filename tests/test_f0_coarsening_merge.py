"""Independent finite checks for lean/Research/F0CoarseningMerge.lean.

Python standard library only. For every pair of idempotent maps K, K' on 1..5
labelled points: whenever K' o K = K', the block-size type of K' must be
reachable from that of K by exactly r - r' binary merges (r, r' = numbers of
fixed points), computed by breadth-first search on sorted tuples. Conversely,
for every idempotent K, every type reachable by n merges must be the type of
some idempotent coarsening K' with r - n fixed points.
"""
from __future__ import annotations

import itertools
import re
import unittest
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / 'lean' / 'Research' / 'F0CoarseningMerge.lean'


def idempotents(n):
    for k in itertools.product(range(n), repeat=n):
        if all(k[k[x]] == k[x] for x in range(n)):
            yield k


def block_type(k):
    return tuple(sorted(Counter(k).values(), reverse=True))


def merges(t):
    out = set()
    for i, j in itertools.combinations(range(len(t)), 2):
        rest = [x for idx, x in enumerate(t) if idx not in (i, j)]
        out.add(tuple(sorted(rest + [t[i] + t[j]], reverse=True)))
    return out


def reachable_in(t, n):
    level = {t}
    for _ in range(n):
        level = set().union(*(merges(u) for u in level)) if level else set()
    return level


class Correspondence(unittest.TestCase):
    def test_coarsening_gives_chain(self):
        pairs = 0
        for n in range(1, 6):
            ks = list(idempotents(n))
            for k in ks:
                for k2 in ks:
                    if all(k2[k[x]] == k2[x] for x in range(n)):
                        r, r2 = len(set(k)), len(set(k2))
                        self.assertIn(block_type(k2), reachable_in(block_type(k), r - r2))
                        pairs += 1
        self.assertGreater(pairs, 1000)

    def test_chains_are_realized(self):
        for n in range(1, 6):
            ks = list(idempotents(n))
            for k in ks:
                r = len(set(k))
                coarse = {}
                for k2 in ks:
                    if all(k2[k[x]] == k2[x] for x in range(n)):
                        coarse.setdefault(r - len(set(k2)), set()).add(block_type(k2))
                for steps in range(r):
                    self.assertEqual(reachable_in(block_type(k), steps), coarse.get(steps, set()),
                                     (k, steps))


class LeanSource(unittest.TestCase):
    def test_no_holes_and_main_declarations_present(self):
        source = LEAN.read_text(encoding='utf-8')
        self.assertIsNone(re.search(r'^\s*(axiom|sorry)\b', source, re.M))
        self.assertNotIn('sorry', source)
        self.assertNotIn('native_decide', source)
        for name in ('merge_realized', 'coarsening_chain', 'chain_realized',
                     'chain_iff_coarsening', 'type_mergeFibers', 'type_eq_of_coarsens_card'):
            self.assertIsNotNone(
                re.search(r'^theorem ' + name + r'\b', source, re.M), name)


if __name__ == '__main__':
    unittest.main()
