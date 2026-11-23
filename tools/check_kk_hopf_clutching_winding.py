#!/usr/bin/env python3
"""Exact algebra check: equatorial Hopf transition is conjugation.
This script does not compute topological winding; Mathlib covers that.
"""
import sympy as s
u,v=s.symbols('u v',real=True)
# On u²+v²=1 the north and south sections have sqrt(2) denominator.
d=s.sqrt(2)
N=s.Matrix([1/d,0,u/d,v/d])
S=s.Matrix([u/d,-v/d,1/d,0])
C,T=u,-v
rot=s.Matrix([C*N[0]-T*N[1],T*N[0]+C*N[1],
              C*N[2]-T*N[3],T*N[2]+C*N[3]])
for i in range(4):
    residual=s.factor((rot[i]-S[i]).subs(v*v,1-u*u))
    assert residual==0,(i,residual)
assert s.expand(C*C+T*T-1).subs(v*v,1-u*u)==0
print("PASS: explicit Hopf transition on entire unit equator equals conjugation")
print("PASS: all 4 rotation components and unit norm")
print("SCOPE: integer winding number is proved in Mathlib, not by SymPy")
