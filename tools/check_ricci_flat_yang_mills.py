"""Independent exact arithmetic checks of Ricci-flat -> curvature Yang--Mills.

D[e,a,b,c,d] represents a covariant derivative of Riemann curvature
at a point in a pseudo-orthonormal frame. We build it from symmetric
third derivatives of a metric in normal coordinates; this automatically
obeys the differential Bianchi, pair exchange and last-pair skew.

The checker also supplies a nonzero linearized vacuum gravitational-wave
jet with Ricci derivative=0 and D != 0, and a deliberately fake derivative
that fails Bianchi despite trace cancellation. Standard library only.
"""
from fractions import Fraction
from hashlib import sha256
from itertools import product


def generic_jet(n, seed):
    """Third partials T[i,j,k,l,m] symmetric in (i,j), (k,l,m)."""
    def third(i, j, k, ell, m):
        label = f"{seed}/{min(i,j)},{max(i,j)}/{sorted((k,ell,m))}"
        return sha256(label.encode()).digest()[0] % 7 - 3

    def D(e, a, b, c, d):
        return Fraction(
            third(a, d, b, c, e) + third(b, c, a, d, e)
            - third(a, c, b, d, e) - third(b, d, a, c, e), 2)
    return D


def vacuum_wave_jet():
    """Linearized transverse-traceless h_xx=-h_yy=(t-z)^3/6.

    At the origin all first/second derivatives vanish and the third
    derivative provides a nontrivial (nabla R) jet in Lorentz signature.
    """
    v = (1, 0, 0, -1)

    def third(i, j, k, ell, m):
        amp = (1 if i == j == 1 else -1 if i == j == 2 else 0)
        return amp * v[k] * v[ell] * v[m]

    def D(e, a, b, c, d):
        return Fraction(
            third(a, d, b, c, e) + third(b, c, a, d, e)
            - third(a, c, b, d, e) - third(b, d, a, c, e), 2)
    return D


def test_contracted_bianchi(D, n, signs):
    axes = range(n)
    def ricci_derivative(e, b, d):
        return sum((signs[a] * D(e, a, b, a, d) for a in axes),
                   Fraction())
    def first_divergence(b, c, d):
        return sum((signs[a] * D(a, a, b, c, d) for a in axes),
                   Fraction())
    def ym_divergence(a, b, d):
        return sum((signs[c] * D(c, a, b, c, d) for c in axes),
                   Fraction())
    for e, a, b, c, d in product(axes, repeat=5):
        assert D(e, a, b, c, d) == -D(e, a, b, d, c)
        assert D(e, a, b, c, d) == D(e, c, d, a, b)
        assert (D(e, a, b, c, d) + D(c, a, b, d, e)
                + D(d, a, b, e, c)) == 0
    for a, b, d in product(axes, repeat=3):
        assert ym_divergence(a, b, d) == (
            ricci_derivative(a, d, b) - ricci_derivative(b, d, a))
        assert first_divergence(d, a, b) == ym_divergence(a, b, d)
    return ricci_derivative, ym_divergence


def verify():
    count = 0
    for n in (2, 3, 4):
        for seed in range(3):
            D = generic_jet(n, seed)
            for signs in product((-1, 1), repeat=n):
                test_contracted_bianchi(D, n, signs)
                count += 1
    print(f"PASS {count} metric-jet/signature combinations in dimensions 2,3,4")

    D = vacuum_wave_jet()
    ricci, ym = test_contracted_bianchi(D, 4, (-1, 1, 1, 1))
    assert any(D(*i) != 0 for i in product(range(4), repeat=5))
    assert all(ricci(*i) == 0 for i in product(range(4), repeat=3))
    assert all(ym(*i) == 0 for i in product(range(4), repeat=3))
    print("PASS nonzero linearized vacuum wave jet, Ricci derivative=0, YM=0")

    def fake(e, a, b, c, d):
        if (e, a, b, c, d) == (0, 0, 1, 1, 2):
            return 1
        if (e, a, b, c, d) == (0, 0, 1, 2, 1):
            return -1
        return 0
    axes = range(3)
    assert all(sum(fake(e, a, b, a, d) for a in axes) == 0
               for e, b, d in product(axes, repeat=3))
    assert sum(fake(a, a, 1, 1, 2) for a in axes) == 1
    assert (fake(0, 0, 1, 1, 2) + fake(1, 0, 1, 2, 0)
            + fake(2, 0, 1, 0, 1)) != 0
    print("PASS counterexample: Bianchi assumption cannot be omitted")


if __name__ == "__main__":
    verify()
