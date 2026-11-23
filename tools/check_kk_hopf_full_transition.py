#!/usr/bin/env python3
"""Exact symbolic identities for the general Hopf north/south transition.

Assumes u²+v²+w²=1, dn²=2(1+w), ds²=2(1-w), dn,ds>0.
No numerical sampling; not a topological degree or Chern-class proof.
"""
import sympy as s
u,v,w,dn,ds=s.symbols("u v w dn ds",real=True)
unit=s.expand(4*(u*u+v*v)-dn*dn*ds*ds)
unit=s.factor(unit.subs(dn**2,2*(1+w)).subs(ds**2,2*(1-w)))
unit=s.factor(unit.subs(v**2,1-w*w-u*u))
assert unit==0,unit
N=s.Matrix([(1+w)/dn,0,u/dn,v/dn])
South=s.Matrix([u/ds,-v/ds,(1-w)/ds,0])
C,T=2*u/(dn*ds),-2*v/(dn*ds)
Rot=s.Matrix([C*N[0]-T*N[1],T*N[0]+C*N[1],C*N[2]-T*N[3],T*N[2]+C*N[3]])
for i in range(4):
    expr=s.expand(s.cancel((Rot[i]-South[i])*dn**2*ds))
    expr=s.factor(expr.subs(dn**2,2*(1+w)))
    expr=s.factor(expr.subs(v**2,1-w*w-u*u))
    assert expr==0,(i,expr)
print("PASS: full 4-component overlap transition for arbitrary sphere coordinates")
print("PASS: transition has unit modulus from the two squared denominators")
print("SCOPE: Chern class/winding degree and smooth bundle atlas are NOT checked")
