"""Exact arithmetic witness for WFS Möbius and 4-point Fourier aliasing.

Independent of Lean. Fraction arithmetic is exact; exp/log conjugacy uses
a small floating tolerance only as a numerical regression.
"""
from fractions import Fraction
from itertools import product
from math import exp


def g2(r):
    return (r * r - 1) / 2


def mobius(z):
    return -z / (1 + 2 * z)


def rotate(state):
    x, u = state
    return -u, x


def four_trace(state):
    x0, u0 = state
    out = []
    state = (x0, u0)
    for _ in range(4):
        out.append(state[0])
        state = rotate(state)
    return out


def first_mode(values):
    return (values[0] - 1j * values[1] - values[2] + 1j * values[3]) / 4


def main():
    positives = [Fraction(1, 8), Fraction(1, 4), Fraction(1, 2),
                 Fraction(1), Fraction(2), Fraction(3), Fraction(8)]
    for r in positives:
        z = g2(r)
        assert z > -Fraction(1, 2)
        assert 1 + 2 * z > 0
        assert mobius(z) == g2(1 / r)
        assert mobius(mobius(z)) == z
        assert 1 + 2 * mobius(z) > 0

    # Projective matrix [-1,0;2,1] has A²=I, det(A)=-1.
    a, b, c, d = Fraction(-1), Fraction(0), Fraction(2), Fraction(1)
    assert (a*a+b*c, a*b+b*d, c*a+d*c, c*b+d*d) == (1, 0, 0, 1)
    assert a*d-b*c == -1

    vals = [Fraction(-3), Fraction(-2), Fraction(-1), Fraction(0),
            Fraction(1), Fraction(2), Fraction(3)]
    for state in product(vals, repeat=2):
        x, u = state
        t = four_trace(state)
        assert t == [x, -u, -x, u]
        assert first_mode(t) == (float(x) + 1j*float(u)) / 2
        assert rotate(rotate(state)) == (-x, -u)
        assert (t[0],t[2]) == (x,-x)
        if x in [-1,0,1]:
            z = g2(exp(float(x)))
            new = g2(exp(-float(x)))
            assert abs(mobius(z)-new) < 1e-10

    s1,s2=(Fraction(0),Fraction(0)),(Fraction(0),Fraction(1))
    assert four_trace(s1)[::2] == four_trace(s2)[::2]
    assert first_mode(four_trace(s1)) != first_mode(four_trace(s2))
    print("WFS Möbius rational domain/involution and projective matrix: PASS")
    print("E quarter-turn 4-phase Fourier aliasing and hidden quadrature: PASS")
    print("Exponential positive-gauge numerical conjugacy: PASS")


if __name__ == "__main__":
    main()
