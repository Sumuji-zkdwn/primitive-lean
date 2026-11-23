"""Exact finite certificates extracted from stages 29 and 30.

Uses only Fraction arithmetic for the 7-edge metric compatibility, a flat
non-affine embedding counterexample, and rank-one Hessian kernel tests.
Does NOT derive the Regge action or establish propagating gravitons.
"""
from fractions import Fraction as Q
from random import Random
import json


def rank(a):
    """Gaussian elimination over the rationals (not floating point)."""
    a = [[Q(v) for v in row] for row in a]
    n = len(a)
    m = len(a[0]) if n else 0
    r = 0
    for c in range(m):
        pivot = next((i for i in range(r, n) if a[i][c]), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        p = a[r][c]
        a[r] = [v / p for v in a[r]]
        for i in range(n):
            if i != r:
                d = a[i][c]
                a[i] = [x - d * y for x, y in zip(a[i], a[r])]
        r += 1
        if r == n:
            break
    return r


def metric_edges(g):
    a, b, c, d, e, f = g
    return [a, b, c, a + b + 2*d, a + c + 2*e, b + c + 2*f,
            a + b + c + 2*d + 2*e + 2*f]


def mismatch(v):
    return v[6] - v[3] - v[4] - v[5] + v[0] + v[1] + v[2]


def sqdist(a, b):
    return sum((x-y)**2 for x, y in zip(a, b))


def flat_embedding_stencil(a, eps):
    """Seven squared distances from origin after (x,y,z)->(x+eps*y*z,y,z)."""
    origin = (Q(0), Q(0), Q(0))
    dirs = [(1,0,0), (0,1,0), (0,0,1), (1,1,0),
            (1,0,1), (0,1,1), (1,1,1)]
    result = []
    for dx, dy, dz in dirs:
        x, y, z = a*dx, a*dy, a*dz
        result.append(sqdist((x + eps*y*z, y, z), origin))
    return result


def matvec(a, v):
    return [sum(x*y for x, y in zip(row, v)) for row in a]


def main():
    rng = Random(20261123)
    m = [[metric_edges([Q(int(i == j)) for i in range(6)])[k]
          for j in range(6)] for k in range(7)]
    r = [Q(1), Q(1), Q(1), Q(-1), Q(-1), Q(-1), Q(1)]
    assert rank(m) == 6
    assert all(sum(r[k] * m[k][j] for k in range(7)) == 0
               for j in range(6))
    for _ in range(512):
        g = [Q(rng.randrange(-100,101),rng.randrange(1,90)) for _ in range(6)]
        assert mismatch(metric_edges(g)) == 0

    for _ in range(512):
        a = Q(rng.randrange(1,40),rng.randrange(1,50))
        eps = Q(rng.randrange(-40,41),rng.randrange(1,30))
        assert mismatch(flat_embedding_stencil(a,eps)) == 2*eps*a**3

    j5 = [[Q(1) for _ in range(5)] for _ in range(5)]
    gauge = [[Q(int(i == k) - int(i == 4)) for i in range(5)]
             for k in range(4)]
    assert rank(j5) == 1 and rank(gauge) == 4
    assert all(matvec(j5, v) == [Q(0)]*5 for v in gauge)
    assert rank([[j5[i][k] + Q(int(i == k)) for k in range(5)]
                 for i in range(5)]) == 5
    assert rank([[Q(7) * j5[i][k] for k in range(5)]
                 for i in range(5)]) == 1
    assert matvec(j5, [Q(1)]*5) == [Q(5)]*5
    print(json.dumps({"status":"PASS", "seven_edge_rank":6,
                      "flat_embedding_exact_cases":512,
                      "metric_exact_cases":512,
                      "five_edge_hessian_rank":1,
                      "four_sum_zero_witnesses":4,
                      "fixed_edge_spring_rank":5,
                      "scope":"algebraic consequences only"},sort_keys=True))


if __name__ == "__main__":
    main()
