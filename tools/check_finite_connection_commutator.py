#!/usr/bin/env python3
"""Exact nonabelian covariant-derivative commutator with nonconstant coefficients.

The 2x2 connection matrices and rank-two section have independent symbolic
polynomial first/second jets. No PDE assumptions or numerical samples.
This is a regression oracle, not a Lean kernel proof.
"""
import sympy as sp
x,y=sp.symbols('x y',real=True)
c=sp.symbols('c0:24')
A=sp.Matrix(2,2,lambda i,j:c[i*6+j*3]+c[i*6+j*3+1]*x+c[i*6+j*3+2]*y)
B=sp.Matrix(2,2,lambda i,j:c[12+i*6+j*3]+c[12+i*6+j*3+1]*x+c[12+i*6+j*3+2]*y)
u=sp.symbols('u0:12')
s=sp.Matrix([u[0]+u[1]*x+u[2]*y+u[3]*x*x+u[4]*x*y+u[5]*y*y,
             u[6]+u[7]*x+u[8]*y+u[9]*x*x+u[10]*x*y+u[11]*y*y])
def Dx(v):return v.diff(x)+A*v
def Dy(v):return v.diff(y)+B*v
F=B.diff(x)-A.diff(y)+A*B-B*A
assert any(sp.expand(e)!=0 for e in F)
assert all(sp.expand(e)==0 for e in Dx(Dy(s))-Dy(Dx(s))-F*s)
print('PASS: rank-two arbitrary affine noncommuting connection and quadratic section')
print('PASS: [nabla_x,nabla_y]s = (partial_x B-partial_y A+[A,B])s')
print('SCOPE: generic finite-rank theorem is Lean kernel verified separately')
