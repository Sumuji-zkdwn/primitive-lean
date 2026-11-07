#!/usr/bin/env python3
"""Independent exact-Fraction checks for the prism hysteresis readout model.

This is a finite regression, NOT a Lean proof or physical validation.
"""
from fractions import Fraction as F
from itertools import product

C, S = F(3, 5), F(4, 5)


def mix(x, c=C, s=S):
    br, bi, dr, di = x
    return (c * br + s * di, c * bi - s * dr,
            c * dr + s * bi, c * di - s * br)


def coherence(x):
    br, bi, dr, di = x
    return (br * dr + bi * di, bi * dr - br * di)


def imbalance(x):
    br, bi, dr, di = x
    return br * br + bi * bi - dr * dr - di * di


def intensities(x):
    br, bi, dr, di = x
    return ((br - di)**2 + (bi + dr)**2,
            (br + di)**2 + (bi - dr)**2)


def contrast(x):
    p, m = intensities(x)
    return p - m


def write(old, u):
    return True if u >= 1 else False if u <= -1 else old


def main():
    states = [tuple(map(F, t)) for t in product(range(-2, 3), repeat=4)]
    for x in states:
        assert contrast(x) == 4 * coherence(x)[1]
        y = mix(x)
        assert mix(y, C, -S) == x
        assert imbalance(x) == (25 * contrast(y) + 7 * contrast(x)) / 48
    a = (F(1), F(0), F(2), F(0))
    b = (F(2), F(0), F(1), F(0))
    assert coherence(a) == coherence(b)
    assert sum(z*z for z in a) == sum(z*z for z in b)
    assert coherence(mix(a)) == (2, F(-36, 25))
    assert coherence(mix(b)) == (2, F(36, 25))
    assert contrast(mix(a)) == F(-144, 25)
    assert contrast(mix(b)) == F(144, 25)
    assert write(write(False, 2), 0) is True
    assert write(write(False, -2), 0) is False
    assert all(write(h, 0) == h for h in (False, True))
    print(f"PASS: {len(states)} exact states for contrast, inverse and reconstruction")
    print("PASS: two blind states split by balanced interferometric readout")
    print("PASS: two-state threshold write and retention")


if __name__ == "__main__":
    main()
