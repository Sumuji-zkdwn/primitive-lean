#!/usr/bin/env python3
"""Exact independent polynomial certificates for Hopf sphere surjectivity.

The only analytic input is positive sqrt(2(1+w)) when (u,v,w) lies
on the unit sphere with w != -1. This is NOT a smooth quotient theorem.
"""
import sympy as s
u,v,w,d=s.symbols('u v w d',real=True)
X=[(1+w)/d,s.Integer(0),u/d,v/d]
hopf=[2*(X[0]*X[2]+X[1]*X[3]),
      2*(X[0]*X[3]-X[1]*X[2]),
      X[0]**2+X[1]**2-X[2]**2-X[3]**2]
sphere=sum(z*z for z in X)
for title, residual in [('unit norm', sphere-1),
                        ('Hopf X',hopf[0]-u),
                        ('Hopf Y',hopf[1]-v),
                        ('Hopf Z',hopf[2]-w)]:
    num,den=s.fraction(s.factor(s.together(residual)))
    num=s.expand(num).subs(d**2,2*(1+w)).subs(v**2,1-w**2-u**2)
    assert s.factor(num)==0,(title,s.factor(num),den)
    print('PASS:',title,'under base unit sphere and positive root')
P=[0,0,1,0]
def fhopf(A):
    return [2*(A[0]*A[2]+A[1]*A[3]),
      2*(A[0]*A[3]-A[1]*A[2]),
      A[0]**2+A[1]**2-A[2]**2-A[3]**2]
assert sum(z*z for z in P)==1 and fhopf(P)==[0,0,-1]
print('PASS: south-pole exceptional section')
print('SCOPE: explicit algebraic sphere surjectivity; topology and smooth quotient external')
