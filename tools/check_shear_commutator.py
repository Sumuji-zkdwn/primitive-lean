"""Exact integer regression checks for ShearCommutator.inc.

This is independent arithmetic, not a substitute for the Lean axiom audit.
"""
from itertools import product


def swap(z):
    return z[1], z[0]


def g(k, z):
    x, y = z
    return k*x + y, x


def A(a, z):
    return g(a, swap(z))


def B(b, z):
    return swap(g(b, z))


def undo_A(a, z):
    x, y = z
    return x-a*y, y


def undo_B(b, z):
    x, y = z
    return x, y-b*x


def C(a, b, z):
    return undo_B(b, undo_A(a, B(b, A(a, z))))


def matrix_C(a, b, z):
    x, y = z
    return ((1-a*b)*x-a*a*b*y,
            a*b*b*x+(1+a*b+a*a*b*b)*y)


cases = 0
for a, b in product(range(-4, 5), repeat=2):
    for z in product(range(-3, 4), repeat=2):
        assert A(a, z) == (z[0]+a*z[1], z[1])
        assert B(b, z) == (z[0], z[1]+b*z[0])
        assert undo_A(a, A(a, z)) == z
        assert undo_B(b, B(b, z)) == z
        assert undo_A(a, undo_B(b, B(b, A(a, z)))) == z
        assert C(a, b, z) == matrix_C(a, b, z)
        cases += 1
    p, q, r, s = 1-a*b, -a*a*b, a*b*b, 1+a*b+a*a*b*b
    assert p*s-q*r == 1
    assert p+s == 2+(a*b)**2

z = (1, 0)
orbit = [(1, 0)]
for i in range(19):
    z = C(1, 1, z)
    orbit.append(z)
assert orbit[:5] == [(1, 0), (0, 1), (-1, 3), (-3, 8), (-8, 21)]
for old, new in zip(orbit[1:-1], orbit[2:]):
    assert old[1] > 0
    assert new[1] * 2 >= 5 * old[1]

print(f"PASS: {cases} exact pair/parameter checks, 81 determinant/trace checks; 20 exact orbit points")
