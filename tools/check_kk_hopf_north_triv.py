#!/usr/bin/env python3
"""Independent polynomial certificates for the Hopf north fibre chart.

This does not claim a Lean continuity/quotient atlas theorem.
"""
import sympy as s
from itertools import product
C,S=s.symbols("C S",real=True)
v=s.symbols("v0:4",real=True)
norm=sum(z*z for z in v)
rotate=lambda c,t,z:s.Matrix([
 c*z[0]-t*z[1],t*z[0]+c*z[1],
 c*z[2]-t*z[3],t*z[2]+c*z[3]])
dot=lambda u,w:sum(u[i]*w[i] for i in range(4))
skew=lambda u,w:u[0]*w[1]-u[1]*w[0]+u[2]*w[3]-u[3]*w[2]
r=rotate(C,S,v)
assert s.expand(dot(v,r)-C*norm)==0
assert s.expand(skew(v,r)-S*norm)==0
assert s.expand(sum(z*z for z in r)-(C*C+S*S)*norm)==0
assert all(s.expand((rotate(1,0,v))[i]-v[i])==0 for i in range(4))
assert all(s.expand((rotate(C,S,rotate(1,0,v)))[i]-r[i])==0 for i in range(4))
print("PASS: dot/skew recover the fibre phase on a unit sphere")
print("PASS: phase rotation preserves sphere radius")
print("SCOPE: algebraic chart equivalence; topology/smoothness require separate Lean proofs")
