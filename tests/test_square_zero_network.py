"""Independent integer-arithmetic checks for SquareZeroNetwork.lean.

No external dependencies. Includes exhaustive loopless digraphs on 2, 3, 4
labelled vertices, a separate cycle-detection algorithm, and exact path counts.
"""
from __future__ import annotations

import itertools
import json
import unittest


def edge(n, source, target, weight, vector):
    return tuple(weight * vector[source] if j == target else 0 for j in range(n))


def adjacency(n, arcs):
    """Columns are sources, rows are targets; integer (not Boolean) sums."""
    m = [[0] * n for _ in range(n)]
    for source, target in arcs:
        m[target][source] += 1
    return m


def step(matrix, vector):
    return tuple(sum(row[i] * vector[i] for i in range(len(vector))) for row in matrix)


def has_directed_cycle(n, arcs):
    """Depth-first colors, independent of walk-count recurrence."""
    neighbors = [[] for _ in range(n)]
    for source, target in arcs:
        neighbors[source].append(target)
    colors = [0] * n

    def visit(u):
        colors[u] = 1
        for v in neighbors[u]:
            if colors[v] == 1 or (colors[v] == 0 and visit(v)):
                return True
        colors[u] = 2
        return False

    return any(colors[i] == 0 and visit(i) for i in range(n))


def walk_matrix_zero_after_n(n, arcs):
    """A^n=0 is tested on every basis vector; no numerical eigensolver."""
    m = adjacency(n, arcs)
    for start in range(n):
        v = tuple(int(i == start) for i in range(n))
        for _ in range(n):
            v = step(m, v)
        if any(v):
            return False
    return True


def graph_census(n):
    candidates = [(i, j) for i in range(n) for j in range(n) if i != j]
    dag = cyclic = 0
    for mask in range(1 << len(candidates)):
        arcs = [e for index, e in enumerate(candidates) if mask & (1 << index)]
        cycle = has_directed_cycle(n, arcs)
        killed = walk_matrix_zero_after_n(n, arcs)
        assert killed == (not cycle), (n, arcs, killed, cycle)
        if cycle:
            cyclic += 1
        else:
            dag += 1
    return {"vertices": n, "graphs": 1 << len(candidates),
            "dag": dag, "with_cycle": cyclic}


class SquareZeroNetworkChecks(unittest.TestCase):
    def test_all_edge_compositions_on_small_graphs(self):
        weights = [-2, -1, 0, 1, 2]
        for n in (2, 3, 4):
            arcs = [(i, j) for i in range(n) for j in range(n) if i != j]
            basis = [tuple(int(i == start) for i in range(n)) for start in range(n)]
            for first in arcs:
                for w in weights:
                    for x in basis:
                        self.assertEqual(edge(n, *first, w, edge(n, *first, w, x)), (0,) * n)
                for second in arcs:
                    for p in weights:
                        for q in weights:
                            for x in basis:
                                composed = edge(n, *second, q, edge(n, *first, p, x))
                                if first[1] == second[0]:
                                    self.assertEqual(composed, edge(n, first[0], second[1], q * p, x))
                                else:
                                    self.assertEqual(composed, (0,) * n)

    def test_signed_cycle_exact_gain(self):
        for a, b in itertools.product(range(-3, 4), repeat=2):
            v = (1, 0)
            for k in range(9):
                self.assertEqual(v, ((a * b) ** k, 0))
                v = edge(2, 1, 0, b, edge(2, 0, 1, a, v))

    def test_aggregate_has_only_square_zero_summands(self):
        arcs = [(i, j) for i in range(3) for j in range(3) if i != j]
        m = adjacency(3, arcs)
        for k in range(13):
            v = (1, 0, 0)
            for _ in range(k):
                direct = step(m, v)
                by_edges = tuple(sum(edge(3, *a, 1, v)[j] for a in arcs)
                                 for j in range(3))
                self.assertEqual(direct, by_edges)
                v = direct
            self.assertEqual(sum(v), 2 ** k)
            self.assertEqual(v[1], v[2])
            self.assertEqual(3 * v[0], 2 ** k + 2 * (-1) ** k)
            self.assertEqual(3 * v[1], 2 ** k - (-1) ** k)

    def test_all_loopless_digraphs_up_to_four_vertices(self):
        self.assertEqual(graph_census(2), {"vertices": 2, "graphs": 4,
                                           "dag": 3, "with_cycle": 1})
        self.assertEqual(graph_census(3), {"vertices": 3, "graphs": 64,
                                           "dag": 25, "with_cycle": 39})
        self.assertEqual(graph_census(4), {"vertices": 4, "graphs": 4096,
                                           "dag": 543, "with_cycle": 3553})


if __name__ == "__main__":
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(SquareZeroNetworkChecks)
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    if result.wasSuccessful():
        print(json.dumps({"census": [graph_census(n) for n in (2, 3, 4)],
                          "two_cycle_gain": "(ab)^k",
                          "complete_three_graph_paths": "2^k"}, sort_keys=True))
    raise SystemExit(0 if result.wasSuccessful() else 1)
