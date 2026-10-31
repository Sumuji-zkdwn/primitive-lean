"""Finite checks for WFS sampling kernels and observation pseudodistance.

This is NOT a proof of the arbitrary-period theorem, nor a Lean check.
Only the two finite statements in the WFSObservationGeometry note are tested.
Requires the Python standard library only.
"""
from itertools import combinations
from math import gcd


def signature(m, ds, x):
    return tuple(d * x % m for d in ds)


def distance(m, ds, x, y):
    return sum((d * x) % m != (d * y) % m for d in ds)


def check_kernel_counts():
    checked = 0
    for m in range(1, 56):
        for n in range(4):
            for ds in combinations(range(13), n):
                g = m
                for d in ds:
                    g = gcd(g, d)
                kernel = [x for x in range(m) if not any(d * x % m for d in ds)]
                assert kernel == list(range(0, m, m // g)), (m, ds)
                assert len(kernel) == g, (m, ds)
                assert len({signature(m, ds, x) for x in range(m)}) == m // g
                checked += 1
    return checked


def check_pseudodistance():
    checked = 0
    for m in range(1, 15):
        for ds in [(), (2,), (2, 3), (2, 4), (1, 3, 6), (0, 6, 12)]:
            for x in range(m):
                assert distance(m, ds, x, x) == 0
                for y in range(m):
                    assert distance(m, ds, x, y) == distance(m, ds, y, x)
                    assert (distance(m, ds, x, y) == 0) == (
                        all(d * (x - y) % m == 0 for d in ds)
                    )
                    for z in range(m):
                        assert distance(m, ds, x, z) <= (
                            distance(m, ds, x, y) + distance(m, ds, y, z)
                        ), (m, ds, x, y, z)
                        checked += 1
    return checked


if __name__ == "__main__":
    counts = check_kernel_counts()
    triangles = check_pseudodistance()
    print(f"PASS: {counts} kernel/image cases; {triangles} pseudometric triples")
