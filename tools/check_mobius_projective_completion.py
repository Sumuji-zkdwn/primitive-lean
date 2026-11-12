"""Independent exact rational witnesses for WFS Möbius and cross ratios.

This is finite regression testing only, not a universal proof.
Infinity is represented by None; finite values by Fraction.
"""
from fractions import Fraction as F
from itertools import product


def act(m, z):
    a, b, c, d = m
    if z is None:
        return None if c == 0 else a / c
    denominator = c * z + d
    return None if denominator == 0 else (a * z + b) / denominator


def lift(z):
    return (F(1), F(0)) if z is None else (z, F(1))


def hom(m, p):
    a, b, c, d = m
    x, y = p
    return (a * x + b * y, c * x + d * y)


def bracket(p, q):
    return p[0] * q[1] - p[1] * q[0]


def cr(p, q, r, s):
    denominator = bracket(p, s) * bracket(q, r)
    numerator = bracket(p, r) * bracket(q, s)
    return None if denominator == 0 else numerator / denominator


def main():
    wfs = (F(-1), F(0), F(2), F(1))
    pts = [None] + [F(i, 2) for i in range(-6, 7)]
    assert act(wfs, F(-1, 2)) is None
    assert act(wfs, None) == F(-1, 2)
    for z in pts:
        assert act(wfs, act(wfs, z)) == z
    mats = [
        tuple(map(F, m))
        for m in product([-2, -1, 0, 1, 2], repeat=4)
        if m[0] * m[3] - m[1] * m[2] != 0
    ][:36] + [wfs]
    total = 0
    for m in mats:
        a, b, c, d = m
        for p, q, r, s in product(pts[::2], repeat=4):
            ps = list(map(lift, (p, q, r, s)))
            det = a * d - b * c
            assert bracket(hom(m, ps[0]), hom(m, ps[1])) == det * bracket(ps[0], ps[1])
            assert cr(*(hom(m, v) for v in ps)) == cr(*ps)
            assert cr(*(lift(act(m, z)) for z in (p, q, r, s))) == cr(*ps)
            total += 1
    print(f"PASS: {len(pts)} points; {len(mats)} matrices; "
          f"{total} exact cross-ratio tests including infinite values")


if __name__ == "__main__":
    main()
