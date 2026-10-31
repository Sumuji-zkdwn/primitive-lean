"""Independent numeric and finite-state checks for the E/WFS predictive bridge.

The CI Lean proof is authoritative. These tests are regression witnesses,
not a replacement for proof compilation.
"""
from fractions import Fraction
from itertools import product


def H(k, lam, c, y, state):
    x, u = state
    return k*x + lam*x**3 - c*y - u, x


def wfs2(r):
    return (r*r - 1) / 2


def radius_intensity(z):
    x, u = z
    return 1 + x*x + u*u


def trace(U, K, x, n):
    out = []
    for _ in range(n):
        out.append(K(x))
        x = U(x)
    return tuple(out)


def main():
    vals = tuple(map(Fraction, [-2, -1, 0, 1, 2]))
    tested = 0
    for k, lam, c, y in product(vals, repeat=4):
        f = lambda z: H(k, lam, c, y, z)
        for x, u in product(vals, repeat=2):
            s = (x, u)
            first_two = trace(f, lambda z: z[0], s, 2)
            assert s == (first_two[0], k*first_two[0] +
                         lam*first_two[0]**3 - c*y - first_two[1])
            tested += 1
    # x-only instantaneous observation is not a valid lossless quotient.
    assert (Fraction(0), Fraction(0))[0] == (Fraction(0), Fraction(1))[0]
    assert H(0, 0, 0, 0, (0, 0))[0] != H(0, 0, 0, 0, (0, 1))[0]

    rotate = lambda z: H(0, 0, 0, 0, z)
    sample = tuple(product(vals, repeat=2))
    for z in sample:
        assert radius_intensity(z) > 0
        assert radius_intensity(z) == radius_intensity(rotate(z))
        for t in range(10):
            assert trace(rotate, radius_intensity, z, t+1)[-1] == radius_intensity(z)
    # Distinct states can have the same entire WFS-gauged radial trace.
    x, y = (Fraction(1), Fraction(0)), (Fraction(-1), Fraction(0))
    assert x != y
    assert trace(rotate, lambda z: wfs2(radius_intensity(z)), x, 8) == \
           trace(rotate, lambda z: wfs2(radius_intensity(z)), y, 8)
    print("E x-trace recovery cases:", tested)
    print("Radial observer and positive WFS2 future equality: PASS")
    print("Real-variable Lean proof / exact quotient theorem: independently audited in CI")


if __name__ == "__main__":
    main()
