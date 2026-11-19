"""Independent finite checks for lean/Research/F0DominanceOrder.lean.

Python standard library only. For every N <= 12 and every block count r:

* the set of positive partitions reachable from y by two-block transfers
  (a, b) -> (a + 1, b - 1), a >= b >= 2, computed by breadth-first search,
  equals the set of x with excess_y(t) <= excess_x(t) for all t;
* numerical evidence only (not proved in Lean): the excess order coincides
  with the classical sorted partial-sum majorization;
* Phi_1 is strictly larger at every strictly dominating partition.
"""
from __future__ import annotations

import re
import unittest
from collections import deque
from itertools import accumulate
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / 'lean' / 'Research' / 'F0DominanceOrder.lean'


def partitions(n, largest=None):
    if largest is None:
        largest = n
    if n == 0:
        yield ()
        return
    for k in range(min(n, largest), 0, -1):
        for rest in partitions(n - k, k):
            yield (k,) + rest


def phi(parts):
    value = 1
    for mi in parts:
        value *= sum(mj ** (mi - 1) for mj in parts)
    return value


def excess(p, t):
    return sum(max(m - t, 0) for m in p)


def transfers(p):
    out = set()
    for i, a in enumerate(p):
        for j, b in enumerate(p):
            if i != j and a >= b >= 2:
                q = list(p)
                q[i], q[j] = a + 1, b - 1
                out.add(tuple(sorted(q, reverse=True)))
    return out


def reachable(y):
    seen = {y}
    queue = deque([y])
    while queue:
        p = queue.popleft()
        for q in transfers(p):
            if q not in seen:
                seen.add(q)
                queue.append(q)
    return seen


def dominates_excess(x, y):
    n = sum(x)
    return all(excess(y, t) <= excess(x, t) for t in range(n + 2))


def dominates_partial_sums(x, y):
    return all(a >= b for a, b in zip(accumulate(x), accumulate(y)))


class DominanceOrder(unittest.TestCase):
    def test_reachability_equals_excess_dominance(self):
        pairs = 0
        for n in range(1, 13):
            by_length = {}
            for p in partitions(n):
                by_length.setdefault(len(p), []).append(p)
            for ps in by_length.values():
                for y in ps:
                    reach = reachable(y)
                    for x in ps:
                        dom = dominates_excess(x, y)
                        self.assertEqual(x in reach, dom, (x, y))
                        self.assertEqual(dom, dominates_partial_sums(x, y), (x, y))
                        if dom and x != y:
                            self.assertLess(phi(y), phi(x), (x, y))
                            pairs += 1
        self.assertEqual(pairs, 732)

    def test_examples(self):
        self.assertTrue(dominates_excess((4, 2, 1), (3, 3, 1)))
        self.assertIn((4, 2, 1), transfers((3, 3, 1)))
        x, y = (5, 2, 2, 1, 1), (4, 4, 1, 1, 1)
        self.assertFalse(dominates_excess(x, y))
        self.assertFalse(dominates_excess(y, x))
        self.assertGreater(excess(y, 2), excess(x, 2))
        self.assertGreater(excess(x, 4), excess(y, 4))


class LeanSource(unittest.TestCase):
    def test_no_holes_and_main_declarations_present(self):
        source = LEAN.read_text(encoding='utf-8')
        self.assertIsNone(re.search(r'^\s*(axiom|sorry)\b', source, re.M))
        self.assertNotIn('sorry', source)
        self.assertNotIn('native_decide', source)
        for name in ('reachable_iff_dominates', 'reachable_of_dominates',
                     'exists_transfer_toward', 'phi_lt_of_dominates', 'eq_of_excess_eq'):
            self.assertIsNotNone(
                re.search(r'^theorem ' + name + r'\b', source, re.M), name)


if __name__ == '__main__':
    unittest.main()
