#!/usr/bin/env python3
"""Independent local variable-charge magnetic profile test for 4D KK/EMD.

Checks the gauge-invariant curvature norm, dilaton-weighted Maxwell equations,
flux and a polar-axis smoothness obstruction. NOT a full EMD solution, nor a
global bundle theorem. SymPy 1.14.0.
"""
import sympy as s

r = s.symbols("r", positive=True)
theta = s.symbols("theta", real=True)
c, b0 = s.symbols("c b0", real=True)
H = s.Function("H", positive=True)(r)
B = s.Function("B")(r)
t, az = s.symbols("t az", real=True)
coords = [t, r, theta, az]
rootH = s.sqrt(H)
g = s.diag(-1/rootH, rootH, rootH*r*r, rootH*r*r*s.sin(theta)**2)
ginv = g.inv()
A = s.Matrix([0, 0, 0, B*s.cos(theta)])
F = s.Matrix(4, 4, lambda i,j: s.diff(A[j],coords[i])-s.diff(A[i],coords[j]))
Fup = ginv*F*ginv
F2 = s.factor(sum(F[i,j]*Fup[i,j] for i in range(4) for j in range(4)))
expected = 2*(B**2/r**4+s.diff(B,r)**2*s.cot(theta)**2/r**2)/H
assert s.trigsimp(s.simplify(F2-expected)) == 0

rootg = rootH*r*r*s.sin(theta)
weight = H**(-s.Rational(3,2))
divs = [s.trigsimp(s.simplify(
    sum(s.diff(rootg*weight*Fup[mu,nu],coords[mu]) for mu in range(4))
)) for nu in range(4)]
expected_phi = s.cot(theta)*s.diff(s.diff(B,r)/H**2,r)
assert all(s.trigsimp(s.simplify(divs[i]-
    (expected_phi if i==3 else 0)))==0 for i in range(4))

flux = s.simplify(2*s.pi*s.integrate(F[2,3],(theta,0,s.pi)))
assert s.simplify(flux+4*s.pi*B)==0
assert s.simplify(s.diff(flux,r)+4*s.pi*s.diff(B,r))==0

# Any B'(r) nonzero gives a pole in the gauge-invariant F^2 at theta=0.
limit = s.limit(s.sin(theta)**2*F2,theta,0,dir="+")
assert s.simplify(limit-2*s.diff(B,r)**2/(H*r**2))==0

# Local weighted Maxwell equations alone do not force B'=0:
# H=1 and B=b0+c*r is a source-free local solution with an axis pole if c!=0.
sub = {H:s.Integer(1), B:b0+c*r, s.diff(B,r):c,
       s.diff(B,r,2):0, s.diff(H,r):0}
assert s.simplify(divs[3].subs(sub).doit())==0
assert s.simplify(F2.subs(sub)-2*((b0+c*r)**2/r**4+
        c**2*s.cot(theta)**2/r**2))==0

print("PASS: exact F^2, all 4 Maxwell density divergences, flux")
print("PASS: B' != 0 gives a polar-axis pole in the invariant F^2")
print("PASS: local Maxwell solution H=1, B=b0+c*r is axis-singular for c!=0")
print("SCOPE: global circle bundle and full EMD not established")
