"""Exact finite symbolic probes for orbit-trace integrals and algebraic transfer.

Requires sympy==1.14.0. Run: python tools/check_orbit_trace.py

Finite symbolic checks are not general Lean proofs.
"""
from sympy import (
    Integer, Matrix, Poly, Rational, binomial, diff, expand, integrate,
    rem, simplify, symbols,
)

x, s = symbols("x s")


def residue_trace(p, a, k):
    """Coefficient X^p in X^(k+p) mod X^(p+1)-s*X^p+a."""
    f = x ** (p + 1) - s*x**p + a
    return expand(Poly(rem(x ** (k+p), f, x), x).coeff_monomial(x**p))


def closed_trace(p, a, k):
    return expand(sum(
        (-a)**j * binomial(k-p*j, j) * s**(k-(p+1)*j)
        for j in range(k//(p+1)+1)
    ))


for p in range(1, 6):
    for k in range(25):
        assert expand(residue_trace(p, Integer(2), k)
                      - closed_trace(p, Integer(2), k)) == 0, (p, k)
print("Algebraic transfer: 125 exact residue comparisons passed.")

p, d, a = 3, 11, Integer(1)
N = Matrix.zeros(d+1)
for k in range(d+1):
    poly = Poly(closed_trace(p, a, k) - s**k, s)
    for j in range(k+1):
        N[j, k] = poly.coeff_monomial(s**j)
ranks = [int((N**power).rank()) for power in range(4)]
assert ranks == [12, 8, 4, 0]
print("Jordan witness: nilpotent ranks", ranks, "= four blocks of size 3.")

P, Q = x**3 - 3*x + 1, x**2-x
S = P/Q
T, T2 = 1/(1-x), (x-1)/x
assert simplify(S.subs(x, T)-S) == 0
assert simplify(S.subs(x, T2)-S) == 0
assert simplify(diff(S, x) - (1 + diff(T, x) + diff(T2, x))) == 0
assert S.subs(x, -1) == Rational(3, 2)
assert S.subs(x, Rational(-1, 2)) == Rational(19, 6)
assert integrate(1/s**2, (s, Rational(3, 2), Rational(19, 6))) == Rational(20, 57)
discriminant = (-s)**2*(s-3)**2-4*(s-3)**3-4*(-s)**3-27+18*(-s)*(s-3)
assert expand(discriminant - (s**2-3*s+9)**2) == 0

F = P-s*Q


def original_transfer(z):
    z = expand(z.subs(s, x))
    return expand(Poly(rem(z*Q, F, x), x).coeff_monomial(x**2))


expected = [Integer(1), s-1, s**2-2*s+3, s**3-3*s**2+7*s-4]
assert [original_transfer(s**k) for k in range(4)] == expected
assert original_transfer(x**2+2*x-1) == s**2
N0 = lambda z: expand(original_transfer(z)-z)
for degree in range(7):
    z = s**degree
    for _ in range(degree+1):
        z = N0(z)
    assert z == 0
print("Cyclic cubic: invariants, exact integral, first moments and nilpotence passed.")

# A concrete Jacobian-one polynomial E with invariant V=v+u^3.
u, v, t, n = symbols("u v t n")
V = v + u**3
U_next = u + V**2
v_next = V - U_next**3
jac = diff(U_next,u)*diff(v_next,v) - diff(U_next,v)*diff(v_next,u)
assert simplify(jac - 1) == 0
assert expand(v_next + U_next**3 - V) == 0
U_n = u + n*V**2
v_n = V - U_n**3
assert expand(v_n + U_n**3 - V) == 0
u_path = t + n*t**6
integrand = t**3 * diff(u_path,t)
exact = integrate(integrand,(t,0,1))
assert simplify(exact - (Rational(1,4)+Rational(2,3)*n)) == 0
assert exact.subs(n,5) == Rational(43,12)
print("Polynomial E: Jacobian=1, invariant, finite linear moment in n passed.")
print("PASS (symbolic finite probes; general Lean proofs not claimed)")
