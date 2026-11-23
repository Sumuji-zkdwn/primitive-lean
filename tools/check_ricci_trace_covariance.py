"""Independent exact finite-frame oracle for Ricci trace/covariant derivative.

No external libraries. Verifies with integer/Fraction arithmetic:
  tr(nabla R) = nabla(tr R)
for arbitrary rank n, skew frame connection coefficients, arbitrary
curvature fields and arbitrary linear scalar-directional difference
operators. Also checks a nonzero algebraic Weyl-type Ricci-flat R
with nonzero metric-frame Gamma: its contracted nabla R remains zero.
This is a finite algebraic test, NOT the smooth Levi-Civita instance.
"""
from fractions import Fraction
from itertools import product
from random import Random


def verify(n, m, seed):
    rng = Random(seed)
    rngv = lambda: Fraction(rng.randrange(-5, 6), 3)
    # R at each of m points: arbitrary real rank-four tensor
    R = {
        (p, a, b, c, d): rngv()
        for p, a, b, c, d in product(range(m), range(n), range(n),
                                      range(n), range(n))
    }
    G = {}
    for p, e in product(range(m), range(n)):
        for i in range(n):
            G[p, e, i, i] = Fraction()
            for j in range(i + 1, n):
                x = rngv()
                G[p, e, i, j] = x
                G[p, e, j, i] = -x

    # Arbitrary linear differential operator on a function at a point.
    # Finite difference on the cyclic set P; not an actual smooth derivation.
    def dd(e, f, p):
        return (e + 1) * (f((p + 1) % m) - f(p))

    def ric(p, b, d):
        return sum((R[p, i, b, i, d] for i in range(n)), Fraction())

    def dc(p, e, a, b, c, d):
        return (
            dd(e, lambda q: R[q, a, b, c, d], p)
            - sum((G[p, e, a, j] * R[p, j, b, c, d]
                   for j in range(n)), Fraction())
            - sum((G[p, e, b, j] * R[p, a, j, c, d]
                   for j in range(n)), Fraction())
            - sum((G[p, e, c, j] * R[p, a, b, j, d]
                   for j in range(n)), Fraction())
            - sum((G[p, e, d, j] * R[p, a, b, c, j]
                   for j in range(n)), Fraction())
        )

    def covric(p, e, b, d):
        return (
            dd(e, lambda q: ric(q, b, d), p)
            - sum((G[p, e, b, j] * ric(p, j, d)
                   for j in range(n)), Fraction())
            - sum((G[p, e, d, j] * ric(p, b, j)
                   for j in range(n)), Fraction())
        )

    count = 0
    for p, e, b, d in product(range(m), range(n), range(n), range(n)):
        lhs = sum((dc(p, e, i, b, i, d) for i in range(n)), Fraction())
        assert lhs == covric(p, e, b, d), (p, e, b, d, lhs, covric(p, e, b, d))
        count += 1
    return count


def exact_ricci_flat_example():
    n, m = 4, 2
    K = {(0, 1): 1, (0, 2): -1, (0, 3): 0,
         (1, 2): 0, (1, 3): -1, (2, 3): 1}

    def kval(i, j):
        if i == j:
            return 0
        return K[tuple(sorted((i, j)))]

    def R(a, b, c, d):
        return Fraction(
            kval(a, b) * ((1 if a == c and b == d else 0)
                         - (1 if a == d and b == c else 0)))

    assert R(0, 1, 0, 1) == 1
    assert all(sum(R(i, b, i, d) for i in range(n)) == 0
               for b, d in product(range(n), repeat=2))
    assert all(R(a,b,c,d) == R(c,d,a,b) for a,b,c,d in
               product(range(n),repeat=4))
    # Skew connection, nontrivial even while Ricci=0 globally.
    gamma = {(e,i,j): Fraction((e+1)*(i-j), 7)
             for e,i,j in product(range(n), repeat=3)}
    assert gamma[0, 0, 1] != 0
    for e,b,d in product(range(n),repeat=3):
        contraction=Fraction()
        for i in range(n):
            for j in range(n):
                g=lambda u,v: gamma[e,u,v]
                contraction -= g(i,j)*R(j,b,i,d)
                contraction -= g(b,j)*R(i,j,i,d)
                contraction -= g(i,j)*R(i,b,j,d)
                contraction -= g(d,j)*R(i,b,i,j)
        assert contraction == 0, (e,b,d,contraction)
    print("PASS: nonzero Ricci-flat algebraic Weyl-type curvature,")
    print("      nonzero skew connection, zero contracted nabla R")


if __name__ == "__main__":
    count = sum(verify(n,m,seed) for n in (2,3,4)
                for m in (2,3) for seed in range(3))
    print("PASS: exact metric-trace derivative identities:", count)
    exact_ricci_flat_example()
    print("BOUNDARY: frame algebra; smooth LC instance remains to construct")
