#!/usr/bin/env python3
"""Exact finite sign-holonomy verification (standard library only).

Represent a+b*phi as integer pair (a,b), where phi^2 = phi+1.
The checks cover the icosahedral six equiangular lines, all Hamiltonian
orders on all 3/4/5/6 subsets, K4 sign parity, and representative flips.
"""
from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from itertools import combinations, permutations, product
import json


@dataclass(frozen=True)
class Phi:
    a: int = 0
    b: int = 0

    def __add__(self, other: "Phi") -> "Phi":
        return Phi(self.a + other.a, self.b + other.b)

    def __neg__(self) -> "Phi":
        return Phi(-self.a, -self.b)

    def __sub__(self, other: "Phi") -> "Phi":
        return self + -other

    def __mul__(self, other: "Phi") -> "Phi":
        return Phi(self.a * other.a + self.b * other.b,
                   self.a * other.b + self.b * other.a + self.b * other.b)


Z, ONE, PHI = Phi(), Phi(1), Phi(0, 1)
NPHI = -PHI
# A,B,C,D,E,F: one chosen vector per antipodal icosahedral vertex pair.
V = (
    (Z, ONE, PHI), (Z, ONE, NPHI),
    (ONE, PHI, Z), (ONE, NPHI, Z),
    (PHI, Z, ONE), (PHI, Z, -ONE),
)


def dot(u: tuple[Phi, ...], v: tuple[Phi, ...]) -> Phi:
    return sum((a * b for a, b in zip(u, v)), Z)


def sign(x: Phi) -> int:
    assert x in (PHI, NPHI), x
    return 1 if x == PHI else -1


def cycle_sign(path: tuple[int, ...], signs: tuple[tuple[int, ...], ...]) -> int:
    ans = 1
    for i, j in zip(path, path[1:]):
        ans *= signs[i][j]
    return ans


def all_loops(nodes: tuple[int, ...]):
    start = nodes[0]
    for rest in permutations(nodes[1:]):
        yield (start, *rest, start)


def count_signs(nodes: tuple[int, ...],
                signs: tuple[tuple[int, ...], ...]) -> dict[int, int]:
    c = Counter(cycle_sign(path, signs) for path in all_loops(nodes))
    return {1: c[1], -1: c[-1]}


def main() -> None:
    assert PHI * PHI == PHI + ONE
    norm = dot(V[0], V[0])
    assert norm == Phi(2, 1)
    assert all(dot(v, v) == norm for v in V)
    assert norm * norm == Phi(5) * PHI * PHI
    # Since phi>0, |<unit(u),unit(v)>| = phi/(phi+2) = 1/sqrt(5).
    G = [[dot(u, v) for v in V] for u in V]
    assert all(G[i][j] in (PHI, NPHI) for i in range(6)
               for j in range(6) if i != j)
    S = tuple(tuple(0 if i == j else sign(G[i][j]) for j in range(6))
              for i in range(6))
    assert all(S[i][j] == S[j][i] for i in range(6) for j in range(6))
    assert all(sum(S[i][k] * S[k][j] for k in range(6))
               == (5 if i == j else 0) for i in range(6) for j in range(6))

    four = {"".join("ABCDEF"[i] for i in path): cycle_sign(path, S)
            for path in all_loops((0, 1, 2, 3))}
    assert four == {
        "ABCDA": -1, "ABDCA": -1, "ACBDA": 1,
        "ACDBA": -1, "ADBCA": 1, "ADCBA": -1,
    }, four

    # For any three lines, the only two anchored orders are reverses.
    for nodes in combinations(range(6), 3):
        seq = list(all_loops(nodes))
        assert len(seq) == 2
        assert cycle_sign(seq[0], S) == cycle_sign(seq[1], S)

    subsets = {}
    for k in (3, 4, 5, 6):
        counts = {nodes: count_signs(nodes, S)
                  for nodes in combinations(range(6), k)}
        if k == 4:
            assert len(counts) == 15
            assert all(c == {1: 2, -1: 4} for c in counts.values())
        if k == 5:
            assert len(counts) == 6
            assert all(c == {1: 12, -1: 12} for c in counts.values())
        if k == 6:
            assert counts[(0, 1, 2, 3, 4, 5)] == {1: 80, -1: 40}
        subsets[str(k)] = {
            "number_of_subsets": len(counts),
            "positive_counts_by_subset": sorted(c[1] for c in counts.values()),
            "negative_counts_by_subset": sorted(c[-1] for c in counts.values()),
        }

    # Arbitrary symmetric +/-1 weights on K4 (all 2^6 assignments).
    k4_cycle_counts = Counter()
    k4_edges = list(combinations(range(4), 2))
    for values in product((-1, 1), repeat=len(k4_edges)):
        H = [[1 if i == j else 0 for j in range(4)] for i in range(4)]
        for (i, j), val in zip(k4_edges, values):
            H[i][j] = H[j][i] = val
        gain = lambda seq: cycle_sign(seq, H)
        p = (gain((0, 1, 2, 3, 0)), gain((0, 1, 3, 2, 0)),
             gain((0, 2, 1, 3, 0)))
        assert p[0] * p[1] * p[2] == 1
        positive = sum(gain(path) == 1 for path in all_loops(tuple(range(4))))
        assert positive in (2, 6)
        k4_cycle_counts[positive] += 1
    assert k4_cycle_counts == {2: 48, 6: 16}

    # Reversing any of the six unoriented representatives cannot flip holonomy.
    original = {path: cycle_sign(path, S)
                for path in all_loops(tuple(range(6)))}
    for eps in product((-1, 1), repeat=6):
        switched = tuple(tuple(eps[i] * S[i][j] * eps[j]
                               for j in range(6)) for i in range(6))
        assert all(cycle_sign(path, switched) == old
                   for path, old in original.items())

    summary = {
        "arithmetic": "exact Z[phi], phi^2=phi+1",
        "squared_length_ratio_per_projection": "1/5",
        "four_line_signed_final_factor": {
            word: f"{value:+d}/25" for word, value in four.items()},
        "three_line_reversal": "identical sign for all 20 triples",
        "subsets": subsets,
        "universal_signed_k4_positive_count_histogram": dict(k4_cycle_counts),
        "gauge_checks": 64 * 120,
        "six_line_final_absolute_factor": "1/125",
        "seidel_S_squared": "5*I_6",
    }
    print(json.dumps(summary, indent=2, ensure_ascii=False, sort_keys=True))


if __name__ == "__main__":
    main()
