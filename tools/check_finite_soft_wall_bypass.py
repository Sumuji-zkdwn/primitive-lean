"""Exact finite S³ soft-wall bypass: smooth penalty is not a hard sector.

Five SU(2)=S³ site quaternions on the boundary of a four-simplex. A chosen
smooth penalty V(q)=1/(1/100+||q1+q2+q3+2*r*q4||²), r=sqrt(21/26),
spikes to 100 on the direct path's topological wall but is strictly
below 50 on a sequential-site bypass. The K5 quadratic energy is at most 20.
The penalty is constructed by hand and is NOT metric-derived gravity.

All finite identities are checked with exact SymPy. The topological degree
statement relies on standard external topology, not an executed proof.
"""
from itertools import combinations
import sympy as sp

s = sp.symbols("s", real=True)
e = tuple(sp.eye(4)[:, i] for i in range(4))
v = e + (-sp.ones(4, 1) / 2,)
r = sp.sqrt(sp.Rational(21, 26))
rho = 2 * r
eps = sp.Rational(1, 100)
zero = sp.zeros(4, 1)


def norm2(x):
    return sp.expand(sum((x[i] ** 2 for i in range(4)), sp.S.Zero))


def bond_energy(q):
    return sp.expand(sum((norm2(q[i] - q[j])
                          for i, j in combinations(range(5), 2)),
                         sp.S.Zero) / 2)


def target(q):
    return q[1] + q[2] + q[3] + rho * q[4]


def unnormalized(i, t):
    return (1 - t) * v[i] + t * v[0]


def unit(x):
    return x / sp.sqrt(norm2(x))


assert all(norm2(x) == 1 for x in v)
assert sp.simplify(r * r - sp.Rational(21, 26)) == 0
assert 0 < r < sp.Rational(9, 10)
assert (1 - r) ** 2 > sp.Rational(1, 100)
assert bond_energy(v) == 12
assert bond_energy((v[0],) * 5) == 0

# Direct path of PR 207 crosses one genuine simplex admissibility wall.
twall = sp.Rational(1, 6)
qwall = (v[0],) + tuple(unit(unnormalized(i, twall)) for i in range(1, 5))
assert all(sp.simplify(norm2(x) - 1) == 0 for x in qwall)
assert all(sp.simplify(x) == 0 for x in target(qwall))
assert sp.simplify(norm2(target(qwall))) == 0
assert sp.simplify(1 / (eps + norm2(target(qwall))) - 100) == 0

# Initial and vacuum soft potentials remain strictly below 2 and 1.
assert sp.simplify(norm2(target(v)) - (3 - 6*r + 4*r*r)) == 0
assert sp.expand(3 - 6*r + 4*r*r - (4*(r-sp.Rational(3,4))**2+sp.Rational(3,4))) == 0
assert 3 - 6*r + 4*r*r >= sp.Rational(3,4)
assert 12 + 1 / (eps + norm2(target(v))) < 14
vac = (v[0],) * 5
assert sp.simplify(norm2(target(vac)) - (3 + 2*r)**2) == 0
assert 1 / (eps + norm2(target(vac))) < 1

# Four staged continuous paths: move q1, then q2, then q3, then q4,
# with each moving site following its normalized affine geodesic chord.
# All stage endpoints match and all normalizing factors stay positive.
for i in range(1, 5):
    assert sp.simplify(norm2(unnormalized(i, 0)) - 1) == 0
    assert sp.simplify(norm2(unnormalized(i, 1)) - 1) == 0
    start = list(v)
    finish = list(v)
    for j in range(1, i):
        start[j] = finish[j] = v[0]
    finish[i] = v[0]
    for q, expected in ((unit(unnormalized(i, 0)), start[i]),
                        (unit(unnormalized(i, 1)), finish[i])):
        assert q == expected
    stage = list(start)
    stage[i] = unit(unnormalized(i, s))
    if i <= 3:
        assert sp.factor(norm2(unnormalized(i, s)) -
                         (2*s*s - 2*s + 1)) == 0
        # 2(s-1/2)^2+1/2>0. Along stages 1 and 2, fourth Cartesian
        # target coordinate is 1-r. Along stage 3, first coordinate
        # is 2 + s/sqrt(2s²-2s+1)-r >= 2-r > 1-r.
        if i <= 2:
            assert sp.simplify(target(stage)[3] - (1-r)) == 0
        else:
            assert sp.simplify(target(stage)[0] -
                   (2 + s/sp.sqrt(2*s*s-2*s+1) - r)) == 0
    else:
        assert sp.factor(norm2(unnormalized(i, s)) -
                         (3*s*s - 3*s + 1)) == 0
        # 3(s-1/2)^2+1/4>0; ||q4||=1.
        assert sp.simplify(norm2(stage[4])-1) == 0
        assert sp.simplify(norm2(target(stage)) -
            ((3-2*r)**2 + 12*r*(1+stage[4][0]))) == 0

# Cauchy-Schwarz gives q4[0]>=-1, so in the last stage
# ||target|| >= 3-2r > 1-r. All stages thus satisfy
# S=||target||² >= (1-r)² >1/100 exactly.
assert 3-2*r > 1-r
assert 1/(eps+(1-r)**2) < 50
# The uniform 10-edge bound (each unit-pair difference squared <=4):
# E_bond <= (10*4)/2 = 20, E_total(bypass) <20+50=70.
# Direct path passes through E_total >= 100 at t=1/6.
assert 20+50 < 100

# The staged route still crosses a TRUE topological interpolation wall,
# but at another barycentric combination. First stage s=1/2, where
# 2*w1+w2+w3+2*w4=0 on face opposite vertex 0.
raw_half = (v[0], unnormalized(1,sp.Rational(1,2)),v[2],v[3],v[4])
assert 2*raw_half[1]+raw_half[2]+raw_half[3]+2*raw_half[4] == zero
assert sp.Matrix.hstack(*raw_half[1:]).det() == 0
q_half = (v[0],unit(raw_half[1]),v[2],v[3],v[4])
shalf = sp.simplify(norm2(target(q_half)))
assert sp.simplify(shalf -
    (2*(1/sp.sqrt(2)-r)**2 + 2*(1-r)**2)) == 0
assert shalf > sp.Rational(1,100)
assert sp.simplify(bond_energy(q_half) - sp.Rational(23,2)) == 0

print("PASS direct S3 wall t=1/6: selected smooth soft V=100 exactly")
print("PASS four-piece bypass: exact positive margin S>1/100")
print("PASS E_total(bypass)<70, while E_total(direct at wall)>=100")
print("PASS bypass crosses another genuine tetrahedral wall at stage 1 s=1/2")
print("PASS bypass crossing quadratic bond energy 23/2, initial 12, vacuum 0")
print("LIMITS topology external; penalty artificial; no stability/GR/quantum claim")
