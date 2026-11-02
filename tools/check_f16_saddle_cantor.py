"""Exact rational finite check of the F16 saddle and Cantor branch construction.

Numerical/symbolic checks complement (but do not replace) Lean verification.
"""
from fractions import Fraction as Q
from itertools import product


def reflection(z):
    return z[1], z[0]


def saddle(z):
    j = reflection(z)
    return (5 * z[0] + 4 * j[0]) / 3, (5 * z[1] + 4 * j[1]) / 3


def eigen(z):
    return z[0] + z[1], z[0] - z[1]


def from_eigen(z):
    return (z[0] + z[1]) / 2, (z[0] - z[1]) / 2


def branch(a, z):
    return 3 * z[0] - a, (z[1] + a) / 3


def ternary(digits):
    return sum((Q(a, 3 ** (i + 1)) for i, a in enumerate(digits)), Q(0))


def run():
    assert Q(5, 3) ** 2 - Q(4, 3) ** 2 == 1
    for z in [(Q(0), Q(0)), (Q(1), Q(0)), (Q(1, 7), Q(-5, 3))]:
        assert eigen(saddle(z)) == (3 * eigen(z)[0], eigen(z)[1] / 3)
        assert from_eigen(eigen(z)) == z
        for a in (0, 2):
            assert branch(a, z) == (
                eigen(saddle(from_eigen(z)))[0] - a,
                eigen(saddle(from_eigen(z)))[1] + Q(a, 3),
            )
    assert saddle((Q(1), Q(1))) == (Q(3), Q(3))
    assert saddle((Q(1), Q(-1))) == (Q(1, 3), Q(-1, 3))
    for n in range(1, 9):
        words = list(product((0, 1), repeat=n))
        assert len(words) == 2 ** n
        assert len({tuple(2 * a for a in w) for w in words}) == 2 ** n
    # Exact finite-prefix shift in two-sided Cantor coding.
    n = 6
    for future in product((0, 2), repeat=n):
        for past in ((0,) * n, (2,) * n, (0, 2, 0, 2, 0, 2)):
            a = future[0]
            out_u, out_v = branch(a, (ternary(future), ternary(past)))
            assert out_u == ternary(future[1:])
            assert out_v == ternary((a,) + past)
    print("F16 saddle/Cantor exact-rational smoke checks: PASS")


if __name__ == "__main__":
    run()
