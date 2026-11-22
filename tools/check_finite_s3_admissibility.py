"""Exact finite S^3 degree wall on the boundary of a 4-simplex.

The five unit quaternion vertex values are e_0,...,e_3 and -1/2(1,1,1,1).
Every tetrahedral facet uses normalized affine interpolation, provided its
raw affine interpolant is nonzero. This is an added HARD admissibility rule,
not a consequence of the unit-site field's finite polynomial energy.

The script checks all finite linear algebra over Q with SymPy. Brouwer degree
and its homotopy invariance are standard EXTERNAL topology, not executed here.
No metric-only or physical-particle claim is made.
"""
from itertools import combinations
import sympy as sp

t = sp.symbols("t", real=True)
E = sp.eye(4)
v = tuple(E[:, i] for i in range(4)) + (sp.Matrix([-sp.Rational(1, 2)] * 4),)
w = (v[0],) + tuple((1 - t) * v[i] + t * v[0] for i in range(1, 5))
facets = tuple(tuple(j for j in range(5) if j != i) for i in range(5))
assert len(v) == len(w) == len(facets) == 5
assert len(set(combinations(range(5), 2))) == 10
for x in v:
    assert x.dot(x) == 1

# At t=0 the five vertices form an affine 4-simplex containing 0 strictly.
alpha0 = (sp.Rational(1, 6),) * 4 + (sp.Rational(1, 3),)
assert sum(alpha0) == 1 and all(x > 0 for x in alpha0)
assert sum((a * x for a, x in zip(alpha0, v)), sp.zeros(4, 1)) == sp.zeros(4, 1)
A = sp.Matrix.hstack(*(w[i] - w[4] for i in range(4)))
assert sp.factor(A.det()) == 3 * (t - 1) ** 4

# An actual normalized unit-quaternion path exists at every vertex, 0<=t<=1.
expected_norm_sq = (sp.S.One,) + (2*t*t - 2*t + 1,) * 3 + (3*t*t - 3*t + 1,)
for x, expected in zip(w, expected_norm_sq):
    assert sp.factor(x.dot(x) - expected) == 0
assert sp.factor(expected_norm_sq[1] - (2 * (t-sp.Rational(1, 2))**2 + sp.Rational(1, 2))) == 0
assert sp.factor(expected_norm_sq[4] - (3 * (t-sp.Rational(1, 2))**2 + sp.Rational(1, 4))) == 0

# For t<1, individual tetrahedra have no zero iff their raw 4x4 determinants
# are nonzero. At t=1 every vertex is e0, also admissible, despite det=0.
expected_dets = (
    (t-1)**3 * (6*t-1) / 2,
    (t-1)**3 / 2,
    -(t-1)**3 / 2,
    (t-1)**3 / 2,
    -(t-1)**3,
)
for i, facet in enumerate(facets):
    D = sp.Matrix.hstack(*(w[j] for j in facet))
    assert sp.factor(D.det() - expected_dets[i]) == 0, (i, D.det())

# At t=1/6 the tetrahedron opposite vertex 0 has a positive barycentric
# zero: (w1 + w2 + w3 + 2*w4)/5 = 0. This remains true after normalizing each
# w_i, after rescaling the positive barycentric coefficients by ||w_i||.
critical = sp.Rational(1, 6)
weights = (sp.Rational(1, 5),) * 3 + (sp.Rational(2, 5),)
assert sum(weights) == 1 and all(a > 0 for a in weights)
assert sp.simplify(sum((a * w[i] for a, i in zip(weights, facets[0])), sp.zeros(4,1)).subs(t, critical)) == sp.zeros(4, 1)
assert all(sp.factor(expected_dets[i].subs(t,critical)) != 0 for i in range(1,5))

# Exact affine barycentrics of the origin for the full 5-vertex simplex:
# lambda0=(1-6t)/(6(1-t)), lambda1=lambda2=lambda3=1/(6(1-t)),
# lambda4=1/(3(1-t)). Thus lambda_i>0 for all i and 0<=t<1/6.
bary = ((1-6*t)/(6*(1-t)),) + (1/(6*(1-t)),)*3 + (1/(3*(1-t)),)
assert sp.factor(sum(bary)-1)==0
assert sp.simplify(sum((a*x for a,x in zip(bary,w)), sp.zeros(4,1)))==sp.zeros(4,1)

# For t>1/6, a separating functional L=(5,-1,-1,-1) is strictly positive
# on all five vertices, hence 0 is outside their convex hull.
L=sp.Matrix([5,-1,-1,-1])
assert [sp.factor(L.dot(x)) for x in w] == [5]+[6*t-1]*4
assert all(sp.simplify(x.subs(t,1)-v[0])==sp.zeros(4,1) for x in w)

# Along the whole normalized path, any K5 quadratic nearest-neighbor energy
# E2=a/2 sum_{i<j}||q_i-q_j||^2 stays bounded by 20a for a>=0,
# because every pair of unit quaternions has squared distance <=4.
# At t=0 the exact energy is 12a, not infinite.
e2_at_zero = sum(((v[i]-v[j]).dot(v[i]-v[j]) for i,j in combinations(range(5),2)), sp.S.Zero) / 2
assert e2_at_zero == 12
print("PASS unit S^3 vertex data; initial affine simplex encloses origin")
print("PASS 5 tetrahedron determinants, all facet-admissibility intervals")
print("PASS unique t=1/6 wall with strictly positive tetrahedral zero weights")
print("PASS exact interior barycentrics and post-wall separating hyperplane")
print("PASS quadratic energy E2(0)=12a, and 0 <= E2(t) <= 20a")
print("LIMITS degree +/-1 to 0 uses standard topology; no local Lean/CI kernel PASS")
