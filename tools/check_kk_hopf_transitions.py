#!/usr/bin/env python3
"""Exact polynomial checks of the south Hopf section and unique transition phase."""
import sympy as s
u,v,w,d=s.symbols('u v w d',real=True)
X=[u/d,-v/d,(1-w)/d,s.Integer(0)]
base=[2*(X[0]*X[2]+X[1]*X[3]),
      2*(X[0]*X[3]-X[1]*X[2]),
      X[0]**2+X[1]**2-X[2]**2-X[3]**2]
for tag,expr in [('south unit',sum(z*z for z in X)-1),
                 ('south x',base[0]-u),('south y',base[1]-v),('south z',base[2]-w)]:
    num,_=s.fraction(s.together(expr))
    num=s.expand(num).subs(d**2,2*(1-w)).subs(v**2,1-w**2-u**2)
    assert s.expand(num)==0,(tag,num)
    print('PASS:',tag)
C,D=s.symbols('C D',real=True)
Z=s.symbols('z0:4',real=True)
def rotate(c,v,z):
    return [c*z[0]-v*z[1],v*z[0]+c*z[1],c*z[2]-v*z[3],v*z[2]+c*z[3]]
def dot(a,b): return sum(a[i]*b[i] for i in range(4))
def skew(a,b): return a[0]*b[1]-a[1]*b[0]+a[2]*b[3]-a[3]*b[2]
norm=dot(Z,Z)
assert s.expand(dot(Z,rotate(C,D,Z))-C*norm)==0
assert s.expand(skew(Z,rotate(C,D,Z))-D*norm)==0
print('PASS: two independent phase extractions imply uniqueness on unit S3')
print('LIMIT: no smooth bundle transition or Chern-degree theorem')
