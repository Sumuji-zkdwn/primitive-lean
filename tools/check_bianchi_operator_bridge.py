"""Independent exact rational oracle for the matrix-operator Bianchi bridge.

For a commuting coordinate frame with operator covariant derivatives N_i,
curvature is [N_i,N_j], and the induced adjoint derivative of curvature
is [N_k,[N_i,N_j]]. Verify Jacobi / second Bianchi without assuming them.
This is NOT an oracle for smooth manifold Levi-Civita curvature.
"""
from fractions import Fraction
from itertools import product
from random import Random


def zero(n):
    return tuple(tuple(Fraction(0) for j in range(n)) for i in range(n))


def add(a, b):
    n = len(a)
    return tuple(tuple(a[i][j] + b[i][j] for j in range(n))
                 for i in range(n))


def minus(a):
    return tuple(tuple(-v for v in row) for row in a)


def mul(a, b):
    n = len(a)
    return tuple(tuple(sum((a[i][k] * b[k][j] for k in range(n)),
                           Fraction(0)) for j in range(n))
                 for i in range(n))


def bracket(a, b):
    return add(mul(a, b), minus(mul(b, a)))


def curvature(operators, i, j):
    return bracket(operators[i], operators[j])


def covderiv(operators, e, c, d):
    return bracket(operators[e], curvature(operators, c, d))


def tensor(operators, e, a, b, c, d):
    return covderiv(operators, e, c, d)[a][b]


def check_connection(ops):
    n = len(ops)
    z = zero(n)
    for e, c, d in product(range(n), repeat=3):
        lhs = add(add(covderiv(ops,e,c,d),covderiv(ops,c,d,e)),
                  covderiv(ops,d,e,c))
        assert lhs == z
    for e, a, b, c, d in product(range(n), repeat=5):
        assert tensor(ops,e,a,b,c,d) == -tensor(ops,e,a,b,d,c)
        assert (tensor(ops,e,a,b,c,d) +
                tensor(ops,c,a,b,d,e) +
                tensor(ops,d,a,b,e,c)) == 0
    for b, c, d in product(range(n), repeat=3):
        for signs in product((-1,1), repeat=n):
            left = sum((signs[a]*tensor(ops,a,a,b,c,d)
                        for a in range(n)), Fraction(0))
            right = sum((signs[a]*(
                tensor(ops,c,a,b,a,d)-tensor(ops,d,a,b,a,c))
                for a in range(n)), Fraction(0))
            assert left == right


def run():
    rng=Random(20261122)
    count=0
    for n in (2,3,4):
        for trial in range(5):
            ops=tuple(tuple(tuple(Fraction(rng.randrange(-3,4))
                         for j in range(n)) for i in range(n))
                      for _ in range(n))
            check_connection(ops)
            count+=1

    E01=((0,1,0),(0,0,0),(0,0,0))
    E10=((0,0,0),(1,0,0),(0,0,0))
    ops=(E01,E10,zero(3))
    check_connection(ops)
    assert curvature(ops,0,1)[0][0] == 1
    print(f"PASS Jacobi/Bianchi/contraction on {count} exact operator ensembles")
    print("PASS non-flat 3x3 operator example: curvature_01[0,0]=1")
    print("BOUNDARY: metric and torsion facts come separately from mathlib")


if __name__ == "__main__":
    run()
