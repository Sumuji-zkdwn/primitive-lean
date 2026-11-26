#!/usr/bin/env python3
"""Independent exact coordinate curvature regression for a nonflat 2D metric.

No Lean kernel claims: ties rational connection-jet point values to an actual
Levi-Civita connection. Also checks matrix Jacobi and antisymmetry.
"""
import sympy as s
from itertools import product

x,y=s.symbols('x y',real=True)
coords=[x,y]
f=1+x*x
g=s.diag(1,f*f)
gi=g.inv()
n=2
G={}
for i,a,b in product(range(n),repeat=3):
    G[i,a,b]=s.factor(sum(gi[a,c]*(s.diff(g[c,b],coords[i])+
            s.diff(g[c,i],coords[b])-s.diff(g[i,b],coords[c]))
            for c in range(n))/2)

def check0(expr,label):
    q=s.factor(s.cancel(expr))
    assert q==0,(label,q)

expected_gamma={(0,1,1):s.Integer(1), (1,0,1):-s.Integer(4), (1,1,0):s.Integer(1)}
for key in product(range(n),repeat=3):
    check0(G[key].subs(x,1)-expected_gamma.get(key,0),('gamma',key))
D={}
for d,i,a,b in product(range(n),repeat=4):
    D[d,i,a,b]=s.factor(s.diff(G[i,a,b],coords[d]))
expected_dgamma={(0,1,0,1):-s.Integer(8)}
for key in product(range(n),repeat=4):
    check0(D[key].subs(x,1)-expected_dgamma.get(key,0),('dGamma',key))
print('PASS: all 8 Levi-Civita coefficients and 16 first derivatives at x=1')

R={}
for i,j,a,b in product(range(n),repeat=4):
    R[i,j,a,b]=s.factor(D[i,j,a,b]-D[j,i,a,b]+
        sum(G[i,a,c]*G[j,c,b]-G[j,a,c]*G[i,c,b] for c in range(n)))
for i,j,a,b in product(range(n),repeat=4):
    check0(R[i,j,a,b]+R[j,i,a,b],('curvature skew',i,j,a,b))
Ric=s.Matrix(n,n,lambda j,b:s.factor(sum(R[a,j,a,b] for a in range(n))))
expected=s.diag(-2/f,-2*f)
for j,b in product(range(n),repeat=2):
    check0(Ric[j,b]-expected[j,b],('Ricci formula',j,b))
    check0(Ric[j,b].subs(x,1)+g[j,b].subs(x,1),('Ricci=-g at x=1',j,b))
check0(R[0,1,0,1].subs(x,1)+4,'Riemann witness')
print('PASS: all 16 Riemann entries skew and all 4 Ricci entries; Ric(x=1)=-g')

A=s.Matrix(3,3,lambda i,j:s.Symbol(f'A{i}{j}'))
B=s.Matrix(3,3,lambda i,j:s.Symbol(f'B{i}{j}'))
C=s.Matrix(3,3,lambda i,j:s.Symbol(f'C{i}{j}'))
def bracket(P,Q):return P*Q-Q*P
J=bracket(A,bracket(B,C))+bracket(B,bracket(C,A))+bracket(C,bracket(A,B))
assert J.applyfunc(s.expand)==s.zeros(3)
print('PASS: arbitrary 3x3 matrix commutator Jacobi identity (symbolic)')
