"""Exact checks for 4-spatial-dimensional CMC constraint lift.
The elliptic existence theorem and horizon limit are analytic arguments.
"""
import sympy as S
from functools import lru_cache
from itertools import product
r,B=S.symbols('r B',positive=True)
f=1-B/r**2
# r>sqrt(B); use algebraic sqrt(f) formal expressions there.
a=S.sqrt(f)/r; b=S.diff(f,r)/(2*S.sqrt(f)); tau=3*a+b
sigma2=3*(a-tau/4)**2+(b-tau/4)**2
R0=-6/r**2; C=3*tau**2/4
assert S.simplify(R0-sigma2+C)==0
assert S.simplify(C-3*(3*a+b)**2/4)==0
print('PASS background vacuum constraint and CMC trace',flush=True)
# Direct conformal curvature and divergence on a product slice.
chi,x,y,z=S.symbols('chi x y z',real=True); X=(chi,x,y,z); n=4
A,b0=S.symbols('A b0',positive=True)
g=S.diag(b0**2,A**2/z**2,A**2/z**2,A**2/z**2)
G=g.inv(); phi=S.Function('phi')(*X)
# Connection difference for h=phi^2 g.
@lru_cache(None)
def Gamma(i,j,k):
    return S.simplify(sum(G[i,l]*(S.diff(g[l,k],X[j])+S.diff(g[l,j],X[k])-S.diff(g[j,k],X[l]))/2 for l in range(n)))
@lru_cache(None)
def D(i,j,k):
    return ((int(i==j)*S.diff(phi,X[k])+int(i==k)*S.diff(phi,X[j]))-g[j,k]*G[i,i]*S.diff(phi,X[i]))/phi
@lru_cache(None)
def covD(k,i,j,l):
    return S.diff(D(i,j,l),X[k])+sum(Gamma(i,k,m)*D(m,j,l)-Gamma(m,k,j)*D(i,m,l)-Gamma(m,k,l)*D(i,j,m) for m in range(n))
# Contract conformal Ricci difference using background covariant derivative.
DR=S.simplify(sum(G[j,j]*(covD(i,i,j,j)-covD(j,i,i,j)+sum(D(i,i,m)*D(m,j,j)-D(i,j,m)*D(m,i,j) for m in range(n))) for i,j in product(range(n),repeat=2)))
Delta=sum(G[i,i]*(S.diff(phi,X[i],2)-sum(Gamma(j,i,i)*S.diff(phi,X[j]) for j in range(n))) for i in range(n))
assert S.simplify(DR+6*Delta/phi)==0
T=S.Matrix(n,n,lambda i,j:S.Function(f'T{min(i,j)}{max(i,j)}')(*X)); tr=sum(G[i,i]*T[i,i] for i in range(n))
for j in range(n):
    div0=sum(G[i,i]*(S.diff(T[i,j],X[i])-sum(Gamma(k,i,i)*T[k,j]+Gamma(k,i,j)*T[i,k] for k in range(n))) for i in range(n))
    div1=sum(G[i,i]/phi**2*(S.diff(T[i,j]/phi**2,X[i])-sum((Gamma(k,i,i)+D(k,i,i))*T[k,j]/phi**2+(Gamma(k,i,j)+D(k,i,j))*T[i,k]/phi**2 for k in range(n))) for i in range(n))
    assert S.simplify(div1-phi**-4*div0+phi**-5*S.diff(phi,X[j])*tr)==0
print('PASS conformal scalar curvature and all four divergence identities',flush=True)
# Hamiltonian polynomial and linearization, T pointwise orthogonal to background shear.
p,U,C0,W,e=S.symbols('p U C0 W e',real=True)
F=(U-C0)*p-(U+e**2*W)*p**-5+C0*p**3
assert S.simplify(F.subs(p,1)+e**2*W)==0
assert S.simplify(S.diff(F,p).subs({p:1,e:0})-(6*U+2*C0))==0
assert S.diff(F,e).subs({p:1,e:0})==0
assert S.simplify(S.diff(F,e,2).subs({p:1,e:0})+2*W)==0
assert S.simplify((p-p**-5)/(p-1)-sum(p**-i for i in range(6)))==0
assert S.simplify((p**3-p)/(p-1)-p*(p+1))==0
print('PASS Lichnerowicz residual, positive mass, quadratic source and comparison factor',flush=True)
# Zero-circle-frequency mode, normalized to vanish initially.
r0=S.symbols('r0',positive=True); f0=1-B/r0**2
p0=S.log(f/f0)/(2*B)
assert S.simplify(r**3*f*S.diff(p0,r)-1)==0
assert S.simplify(p0.subs(r,r0))==0
assert S.simplify(S.diff(p0,r).subs(r,r0)*S.sqrt(f0)-1/(r0**3*S.sqrt(f0)))==0
# -2(p_rr+2p_r/r) = 2(r^2+B)/(r^2(r^2-B)^2)
tidal=S.simplify(-2*(S.diff(p0,r,2)+2*S.diff(p0,r)/r))
assert S.simplify(tidal-2*(r*r+B)/(r*r*(r*r-B)**2))==0
assert S.simplify(S.limit((r-S.sqrt(B))**2*tidal,r,S.sqrt(B),dir='+')-1/B)==0
print('PASS velocity-only zero mode and nonzero divergent first variation',flush=True)
print('LIMIT: exact initial data existence via analytic elliptic IFT; no nonlinear horizon evolution theorem',flush=True)
