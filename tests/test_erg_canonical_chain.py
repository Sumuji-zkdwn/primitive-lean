"""Independent finite checks for lean/Research/ErgCanonicalChain.lean.

Python standard library only. Every partial successor function on 1..5 labelled
nodes (out-degree <= 1) is enumerated. Whenever in-degree <= 1 and some node s
without predecessor reaches every node, the checks used by ERG-Aout's
validator for extends_main are recomputed independently (cycle detection by
depth-first search, counting starts and ends) and must all pass; the chain
from s must enumerate all nodes exactly once. Conversely, every enumeration of
the nodes as a path satisfies the three assumptions.
"""
from __future__ import annotations

import itertools
import re
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / 'lean' / 'Research' / 'ErgCanonicalChain.lean'


def has_cycle(n, nxt):
    colour = [0] * n

    def visit(u):
        colour[u] = 1
        v = nxt[u]
        if v is not None and (colour[v] == 1 or (colour[v] == 0 and visit(v))):
            return True
        colour[u] = 2
        return False

    return any(colour[i] == 0 and visit(i) for i in range(n))


def chain(nxt, s, limit):
    out, cur = [], s
    while cur is not None and len(out) <= limit:
        out.append(cur)
        cur = nxt[cur]
    return out


class Chains(unittest.TestCase):
    def test_assumptions_imply_validator_checks(self):
        satisfied = 0
        for n in range(1, 6):
            for nxt in itertools.product([None] + list(range(n)), repeat=n):
                targets = [v for v in nxt if v is not None]
                if len(targets) != len(set(targets)):
                    continue  # in-degree > 1
                for s in range(n):
                    if s in targets:
                        continue  # s has a predecessor
                    walk = chain(nxt, s, n)
                    if set(walk) != set(range(n)):
                        continue  # not all reachable
                    satisfied += 1
                    self.assertFalse(has_cycle(n, nxt))
                    self.assertEqual(len(walk), n)
                    self.assertEqual(sorted(walk), list(range(n)))
                    starts = [x for x in range(n) if x not in targets]
                    ends = [x for x in range(n) if nxt[x] is None]
                    self.assertEqual(starts, [s])
                    self.assertEqual(ends, [walk[-1]])
        # exactly the n! labelled paths
        self.assertEqual(satisfied, 1 + 2 + 6 + 24 + 120)

    def test_paths_satisfy_assumptions(self):
        for n in range(1, 6):
            for order in itertools.permutations(range(n)):
                nxt = [None] * n
                for a, b in zip(order, order[1:]):
                    nxt[a] = b
                targets = [v for v in nxt if v is not None]
                self.assertEqual(len(targets), len(set(targets)))
                self.assertNotIn(order[0], targets)
                self.assertEqual(chain(nxt, order[0], n), list(order))


class LeanSource(unittest.TestCase):
    def test_no_holes_and_main_declarations_present(self):
        source = LEAN.read_text(encoding='utf-8')
        self.assertIsNone(re.search(r'^\s*(axiom|sorry)\b', source, re.M))
        self.assertNotIn('sorry', source)
        self.assertNotIn('native_decide', source)
        for name in ('canonical_chain', 'no_cycle', 'start_unique', 'end_unique',
                     'path_satisfies', 'iter_injective', 'iter_card_eq_none'):
            self.assertIsNotNone(
                re.search(r'^theorem ' + name + r'\b', source, re.M), name)


if __name__ == '__main__':
    unittest.main()
