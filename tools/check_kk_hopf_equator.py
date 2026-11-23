#!/usr/bin/env python3
"""Exact equator Hopf transition polynomial oracle; no winding theorem."""
import sympy as s
u,v,d=s.symbols("u v d",real=True,nonzero=True)
N=[1/d,s.Integer(0),u/d,v/d]
S=[u/d,-v/d,1/d,s.Integer(0)]
rotate=[u*N[0]+v*N[1],-v*N[0]+u*N[1],
        u*N[2]+v*N[3],-v*N[2]+u*N[3]]
for i in range(4):
    numerator=s.cancel(rotate[i]-S[i])*d
    numerator=s.factor(numerator)
    assert s.simplify(numerator.subs(v**2,1-u**2))==0,(i,numerator)
print("PASS: four exact equator transition components under u²+v²=1")
print("SCOPE: complex conjugate transition phase; winding/Chern not checked")
