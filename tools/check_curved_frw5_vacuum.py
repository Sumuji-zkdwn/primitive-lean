"""Pure 5D vacuum FRW curvature test: an asymptotically finite S1 radius.

The only primitive variable is a five-dimensional metric. Ricci and Riemann
are differentiated independently in local coordinates with SymPy 1.14.0.
This verifies the full k-dependent time ODE and an explicit curved k=-1
vacuum solution; no scalar/matter/flux input is added.

Scope: smooth local metrics with a,b>0. No dynamical *attractor* or
globally geodesically complete compactification is claimed.
"""
from functools import lru_cache
import sympy as sp

t, r, theta, az, chi, z = sp.symbols(
    "t r theta az chi z", real=True
)
k = sp.symbols("k", real=True)
aa, bb = sp.Function("a")(t), sp.Function("b")(t)


def curvature(diag, coords, with_kretschmann=False):
    """Direct Levi-Civita Gamma^a_bc, R^a_bcd, and all Ricci entries."""
    n = len(coords)
    dg = {(i, j): sp.diff(diag[i], coords[j])
          for i in range(n) for j in range(n)}

    @lru_cache(None)
    def gamma(i, j, m):
        return sp.factor(
            ((dg[i, j] if i == m else 0)
             + (dg[i, m] if i == j else 0)
             - (dg[j, i] if j == m else 0))
            / (2 * diag[i])
        )

    @lru_cache(None)
    def riemann(i, j, m, n_):
        return sp.factor(
            sp.diff(gamma(i, n_, j), coords[m])
            - sp.diff(gamma(i, m, j), coords[n_])
            + sum(
                gamma(i, m, h) * gamma(h, n_, j)
                - gamma(i, n_, h) * gamma(h, m, j)
                for h in range(n)
            )
        )

    ricci = sp.Matrix(
        n, n,
        lambda j, m: sp.factor(
            sum(riemann(i, j, i, m) for i in range(n))
        )
    )
    if not with_kretschmann:
        return ricci
    nonzero = {
        (i, j, m, n_): x
        for i in range(n) for j in range(n)
        for m in range(n) for n_ in range(n)
        if (x := riemann(i, j, m, n_)) != 0
    }
    # In these diagonal charts the full Lorentzian Riemann contraction:
    K = sp.factor(sum(
        diag[i] * x**2 / (diag[j] * diag[m] * diag[n_])
        for (i, j, m, n_), x in nonzero.items()
    ))
    return ricci, K

coords_frw = (t, r, theta, az, chi)
diag_frw = (
    -1,
    aa**2 / (1 - k*r**2),
    aa**2*r**2,
    aa**2*r**2*sp.sin(theta)**2,
    bb**2,
)
R = curvature(diag_frw, coords_frw)
Q = aa*sp.diff(aa, t, 2) + 2*sp.diff(aa, t)**2 + 2*k \
    + aa*sp.diff(aa, t)*sp.diff(bb, t)/bb
assert sp.factor(R[0,0] + 3*sp.diff(aa,t,2)/aa + sp.diff(bb,t,2)/bb) == 0
assert sp.factor(R[1,1] - Q/(1-k*r**2)) == 0
assert sp.factor(R[2,2] - r**2*Q) == 0
assert sp.factor(R[3,3] - r**2*sp.sin(theta)**2*Q) == 0
assert sp.factor(R[4,4] - bb*sp.diff(bb,t,2)
                 - 3*bb*sp.diff(aa,t)*sp.diff(bb,t)/aa) == 0
assert all(R[i,j] == 0 for i in range(5) for j in range(5) if i != j)
print("PASS general k=-1,0,+1 FRW x S1 Ricci: all 25 components")

# Paper derivation from those verified ODEs:
# Ric_tt=0 and Ric_chichi=0 imply a''*b=a'*b'.
# Ric_ij=0 then gives a*a'' + (a')^2 + k=0.
# Thus (a'/b)'=0 and (a^2)''=-2k.
# On a connected interval with b>0:
# (1) a'=0 identically -> k=0 and b is affine;
# (2) a' never vanishes -> a^2=-k*t^2+C*t+D and b=B*abs(a').
# No C2 vacuum can switch branches with b>0.

beta = sp.symbols("beta", real=True)
a = sp.sqrt(t*t + beta)
b = t/a

# Expanding open-k witness in the upper half-space H3 chart z>0:
# gamma_H3=(dx^2+dy^2+dz^2)/z^2.
coords_open = (t, sp.Symbol("x"), sp.Symbol("y"), z, chi)
metric_open = (-1, a**2/z**2, a**2/z**2, a**2/z**2, b**2)
Ropen, Kopen = curvature(metric_open, coords_open, True)
assert all(sp.factor(x) == 0 for x in Ropen)
assert sp.factor(Kopen - 72*beta**2/(t*t+beta)**4) == 0
print("PASS all 25 Ricci entries of explicit open vacuum")
print("PASS full 5D Riemann contraction: 72*beta^2/(t^2+beta)^4")

# beta=1, t>0: genuine nonflat vacuum, growing a, b<1, b -> 1.
b1 = b.subs(beta, 1)
assert sp.simplify(sp.diff(a.subs(beta,1),t)-b1) == 0
assert sp.simplify(sp.diff(b1,t) - 1/(t*t+1)**sp.Rational(3,2)) == 0
assert sp.limit(b1,t,sp.oo) == 1
assert sp.limit(Kopen.subs(beta,1),t,sp.oo) == 0
assert sp.factor(Kopen.subs({beta:1,t:2})-sp.Rational(72,625))==0
# beta=0 gives Milne x S1: flat in five dimensions, fixed b=1.
assert sp.factor(Kopen.subs(beta,0)) == 0
# beta=-1, t>1: a grows, b>1 and decreases ->1; past K diverges.
assert sp.limit(b.subs(beta,-1),t,sp.oo) == 1
assert sp.limit(Kopen.subs(beta,-1),t,1,dir="+") == sp.oo
print("PASS beta=1 curved asymptotic b=1; beta=0 flat Milne; beta=-1 past curvature singularity")

# Einstein frame: g_E=b * (-dt^2+a(t)^2 gamma_H3), with b metric-defined.
diagE = (-b, b*a*a/z**2, b*a*a/z**2, b*a*a/z**2)
RE = curvature(diagE, coords_open[:4])
phi_prime = sp.sqrt(3)*sp.diff(b,t)/(2*b)
for i in range(4):
    for j in range(4):
        rhs = 2*phi_prime**2 if (i,j)==(0,0) else 0
        assert sp.factor(RE[i,j]-rhs) == 0, (i,j)
assert sp.factor(sp.diff(a**3*sp.diff(b,t),t)) == 0
# This equality implies box_E(phi)=0 because
# sqrt(-gE)*gE^tt*phi' = -(sqrt(3)/2)*a^3*b'.
alpha = a*sp.sqrt(b)
dtau_dt = sp.sqrt(b)
HE = sp.simplify(sp.diff(alpha,t)/(alpha*dtau_dt))
phi_dot = sp.simplify(phi_prime/dtau_dt)
accel = sp.simplify(
    sp.diff(sp.diff(alpha,t)/dtau_dt,t)/(alpha*dtau_dt)
)
assert sp.simplify(3*(HE**2-1/alpha**2)-phi_dot**2)==0
assert sp.simplify(accel + phi_dot**2*sp.Rational(2,3))==0
assert sp.simplify(accel +
    beta**2/(2*t**3*(t*t+beta)**sp.Rational(3,2)))==0
print("PASS full 4D Einstein-frame Ricci, box(phi), Friedmann with k=-1, deceleration")

# A positive exact constant circle b'=0 makes b''=0, so Ric_tt=0
# forces a''=0; Ric_ij then forces (a')^2+k=0.
# k=-1 -> expanding Milne with slope +1, K5=0.
# k=0 -> static a; k=+1 -> no real fixed-b vacuum.
print("RESULT fixed b and expansion => only k=-1 flat Milne; nonflat b(t) asymptotes without a radion potential")
print("LIMITS no dynamical attractor, no global completeness, fermions or non-Abelian gauge fields")
