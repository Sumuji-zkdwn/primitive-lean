"""Finite cubic SU(2) lattice: no exact topological sector and an unstable one-site lump.

The 8 site values are unit quaternions. Energy = a/2 sum_edges |q_u-q_v|^2
    + b/4 sum_faces (|d_i q|^2 |d_j q|^2 - (d_i q . d_j q)^2).
Here the Skyrme-like term is a *discrete* face Gram determinant, not a
continuum Skyrme baryon-number functional. No external fields assumed.

Analytic statements (connected product (S^3)^8 is path connected, and
all polynomial energies are bounded on it) are explained in the note.
This script checks the finite combinatorics and exact algebra independently.
"""

from itertools import product, combinations
import sympy as sp

NODES = tuple(product((0, 1), repeat=3))
EDGES = tuple((u, tuple(u[k] + (k == axis) for k in range(3)))
              for u in NODES for axis in range(3) if u[axis] == 0)
FACES = tuple((u, i, j)
              for u in NODES for i, j in combinations(range(3), 2)
              if u[i] == 0 and u[j] == 0)
assert (len(NODES), len(EDGES), len(FACES)) == (8, 12, 6)

def plus(u, axis):
    return tuple(u[k] + (k == axis) for k in range(3))

def dot(u, v):
    return sum((u[k]*v[k] for k in range(4)), sp.S.Zero)

def energy(q, a, b):
    e2 = sp.S.Zero
    e4 = sp.S.Zero
    for u,v in EDGES:
        d=q[u]-q[v]
        e2 += dot(d,d)
    for u,i,j in FACES:
        di=q[plus(u,i)]-q[u]
        dj=q[plus(u,j)]-q[u]
        e4 += dot(di,di)*dot(dj,dj)-dot(di,dj)**2
    return sp.expand(a*e2/2),sp.expand(b*e4/4)

a,b,s=sp.symbols('a b s',real=True)
D=s*s+(1-s)**2
c=(2*s-1)/D
sine=2*s*(1-s)/D
assert sp.factor((2*s-1)**2+4*s*s*(1-s)**2-D**2)==0
# D = 2(s-1/2)^2 + 1/2 > 0 for all real s.
assert sp.factor(D-(2*(s-sp.Rational(1,2))**2+sp.Rational(1,2)))==0
origin=(0,0,0)
one=sp.Matrix([1,0,0,0])
q={u:one for u in NODES}
q[origin]=sp.Matrix([c,sine,0,0])

E2,E4=energy(q,a,b)
assert sp.factor(E2-3*a*(1-c))==0
assert sp.factor(E4)==0
# Complete exact rational quarter-turn: |-1,0,0,0> -> <0,1,0,0> -> <1,0,0,0>.
for t,expected in [(0,6*a),(sp.Rational(1,2),3*a),(1,sp.S.Zero)]:
    assert sp.simplify(E2.subs(s,t)-expected)==0
    assert sp.simplify(E4.subs(s,t))==0
    assert sp.simplify((c*c+sine*sine-1).subs(s,t))==0
# E strictly decreases on 0 < s < 1, a > 0, since derivative =
# -12*a*s*(1-s)/D**2.
assert sp.factor(sp.diff(E2,s)+12*a*s*(1-s)/D**2)==0
# At the antipodal state the exact one-coordinate Hessian is -3a,
# independent of b. This direction is allowed in the full 8-site field space.
theta=sp.symbols('theta',real=True)
path_curv=3*a*(1-sp.cos(theta))
assert sp.diff(path_curv,theta).subs(theta,sp.pi)==0
assert sp.simplify(sp.diff(path_curv,theta,2).subs(theta,sp.pi)+3*a)==0
# Stationarity of the anti-lump on (S^3)^8: all E2 gradients are normal
# to site unit spheres, and the face term has vanishing first variation
# whenever each face's two finite-difference vectors are parallel.
q0={u:(-one if u==origin else one) for u in NODES}
_,quartic=energy(q0,a,b)
assert quartic==0
for u in NODES:
    grad = sum((q0[u]-q0[v] if uu==u else q0[u]-q0[uu]
                for uu,v in EDGES if u in (uu,v)),sp.zeros(4,1))
    # constrained tangent gradient = ambient gradient - (gradient dot q)*q
    assert sp.simplify(grad-dot(grad,q0[u])*q0[u]) == sp.zeros(4,1)
# Area quartic is nonnegative by Gram determinant for any real 4-vectors.
# On the 8-site cube |du|<=2, so E2<=24a, E4<=24b when a,b>=0.
# The arbitrary-field bound is mathematical (Cauchy-Schwarz); test values:
assert energy(q0,sp.S.One,sp.S.One)==(sp.Integer(6),sp.S.Zero)
print('PASS 8 vertices, 12 edges, 6 square faces')
print('PASS rational SU(2)=S^3 path: unit norm, endpoints and exact energy')
print('PASS all six quartic face terms vanish along one-site unwind')
print('PASS E(0)=6a, E(1/2)=3a, E(1)=0, E\'(s)=-12a s(1-s)/D^2')
print('PASS antipode equilibrium, admissible negative curvature E\'\'(pi)=-3a')
print('LIMITS topology is a general mathematical argument; full Lean kernel/continuum Skyrme not asserted')
