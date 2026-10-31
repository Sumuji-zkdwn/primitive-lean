"""Independent arithmetic checks for E and WFS/Fenchel statements.
This does not replace Lean proof compilation and axiom audit.
"""
from fractions import Fraction
from itertools import product
from math import exp, log


def H(k, lam, c, y, x, u):
    return k*x + lam*x**3 - c*y - u, x


def H_inv(k, lam, c, y, p, q):
    return q, k*q + lam*q**3 - c*y - p


def wfs2(r):
    return (r*r - 1) / 2


def V(r):
    return r*r / 2


def main():
    values = [Fraction(-2), Fraction(-1), Fraction(0),
              Fraction(1, 2), Fraction(1), Fraction(2)]
    cases = 0
    for k, lam, c, y, x, u in product(values, repeat=6):
        z = H(k, lam, c, y, x, u)
        assert H_inv(k, lam, c, y, *z) == (x, u)
        assert H(k, lam, c, y, *H_inv(k, lam, c, y, x, u)) == (x, u)
        cases += 1
    assert 4*Fraction(-1)**3 - 3*Fraction(-1) == -1
    half = Fraction(1, 2)
    assert 4*half**3 - 3*half == -1
    assert H(-3, 4, 0, 0, -1, -1)[0] == 0
    assert H(-3, 4, 0, 0, half, -1)[0] == 0
    E = lambda x, u: x**4 - Fraction(3, 2)*x*x - u*x
    assert E(-1, -1) == Fraction(-3, 2)
    assert E(half, -1) == Fraction(3, 16)
    assert E(-1, -1) < E(half, -1)

    positive = [Fraction(1, 4), half, Fraction(1), Fraction(2)]
    assert len({wfs2(r) for r in positive}) == len(positive)
    assert all(wfs2(r) == (r*r - 1) / 2 for r in positive)
    assert all((r - V(r)) <= half for r in positive)
    assert Fraction(1) - V(Fraction(1)) == half
    assert all(wfs2(r) - V(r) == -half for r in positive)
    for r, u in product(positive, values):
        z = wfs2(r)
        xi = u / r
        assert xi * r == u  # xi dz=u dr because dz/dr=r
        assert xi * (2 * z + 1) == u * r
        assert r * (1 / r) == 1

    assert all(abs(exp(log(float(r))) - float(r)) < 1e-12
               for r in positive)

    print("E two-way inverse exact checks:", cases)
    print("T3 collision: (-1,1/2) both map to -1")
    print("Fenchel scores: physical maximum = +1/2, new WFS2 pairing = -1/2")
    print("Positive WFS2 gauge + log/exp checks: PASS")
    print("Arithmetic smoke PASS; all Lean claims need --trust=0 audit")


if __name__ == "__main__":
    main()
