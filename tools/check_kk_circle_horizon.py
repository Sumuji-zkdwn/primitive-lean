"""Exact curvature and causal tests of the compact-circle EF extension."""
import sympy as s
from functools import lru_cache
from itertools import product
r,z,B,L=s.symbols('r z B L',positive=True)
v,x,y=s.symbols('v x y',real=True)
coords=(r,v,x,y,z); n=len(coords)
f=1-B/r**2
h=r**2/z**2
g=s.Matrix([[0,-1,0,0,0],[-1,f,0,0,0],[0,0,h,0,0],[0,0,0,h,0],[0,0,0,0,h]])
inv=g.inv().applyfunc(s.factor)
assert s.factor(g.det()+h**3)==0
assert g[:2,:2].det()==-1
@lru_cache(None)
def G(i,j,k):
    return s.factor(sum(inv[i,m]*(s.diff(g[m,j],coords[k])+s.diff(g[m,k],coords[j])-s.diff(g[j,k],coords[m])) for m in range(n))/2)
@lru_cache(None)
def R(i,j,k,l):
    return s.factor(s.diff(G(i,l,j),coords[k])-s.diff(G(i,k,j),coords[l])+sum(G(i,k,m)*G(m,l,j)-G(i,l,m)*G(m,k,j) for m in range(n)))
assert all(s.factor(sum(R(i,j,i,k) for i in range(n)))==0 for j in range(n) for k in range(n))
assert all(G(i,0,0)==0 for i in range(n))
print('PASS 25 Ricci components; constant-v radial null curves affine')
# Lower first index then contract both four-tensors, using sparse inverse.
ri={}
for I in product(range(n),repeat=4):
    i,j,k,l=I
    a=s.factor(sum(g[i,m]*R(m,j,k,l) for m in range(n)))
    if a!=0: ri[I]=a
nz=[[j for j in range(n) if inv[i,j]!=0] for i in range(n)]
K=s.factor(sum(a*ri.get(J,0)*s.prod(inv[i,j] for i,j in zip(I,J)) for I,a in ri.items() for J in product(*(nz[i] for i in I))))
assert s.factor(K-72*B**2/r**8)==0
assert s.simplify(K.subs(r,s.sqrt(B))-72/B**2)==0
assert s.simplify(s.diff(f,r).subs(r,s.sqrt(B))-2/s.sqrt(B))==0
assert g[1,1].subs(r,s.sqrt(B))==0
assert f.subs(r,s.sqrt(B)/2)==-3
assert f.subs(r,2*s.sqrt(B))==s.Rational(3,4)
print('PASS full non-diagonal Riemann contraction:',K,'; finite horizon value 72/B^2')
# Coordinate pullback: r=sqrt(t^2+B), v=chi+rstar, dv=dchi+dr/f.
t=s.symbols('t',positive=True)
rt=s.sqrt(t*t+B); b=t/rt
f0=s.simplify(f.subs(r,rt)); J=s.Matrix([[b,0],[b/f0,1]])
assert (J.T*g[:2,:2].subs(r,rt)*J-s.diag(-1,b*b)).applyfunc(s.simplify)==s.zeros(2)
print('PASS exact pullback to original t>0 vacuum')
print('RESULT v periodic: closed null orbit at r=sqrt(B), closed timelike orbits 0<r<sqrt(B). No extra fields.')
