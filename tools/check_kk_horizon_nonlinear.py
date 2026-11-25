"""Exact Ricci/Riemann oracle for a metric-only 5D Bianchi V x circle family.
Analytic asymptotics use the identities checked here; no nonlinear PDE claim.
"""
import sympy as S
from functools import lru_cache
from itertools import product, combinations

tau,z=S.symbols('tau z', real=True); chi,x,y=S.symbols('chi x y',real=True)
coords=(tau,chi,x,y,z)
A,C,p=[S.Function(n)(tau) for n in ('A','C','p')]
N=S.exp(3*A+C)
scale=[N,S.exp(C),S.exp(A+p)/z,S.exp(A-p)/z,S.exp(A)/z]
g=S.diag(-scale[0]**2,*[a**2 for a in scale[1:]])
G=g.inv(); dim=5; I=range(dim)
@lru_cache(None)
def Gamma(a,b,c):
    return S.simplify(sum(G[a,d]*(S.diff(g[d,c],coords[b])+S.diff(g[d,b],coords[c])-S.diff(g[b,c],coords[d]))/2 for d in I))
@lru_cache(None)
def R(a,b,c,d):
    return S.simplify(S.diff(Gamma(a,d,b),coords[c])-S.diff(Gamma(a,c,b),coords[d])+sum(Gamma(a,c,e)*Gamma(e,d,b)-Gamma(a,d,e)*Gamma(e,c,b) for e in I))
Ric=S.Matrix(dim,dim,lambda b,d:S.simplify(sum(R(a,b,a,d) for a in I)))
Ap,Cp,pp=[S.diff(a,tau) for a in (A,C,p)]
App,Cpp,ppp=[S.diff(a,tau,2) for a in (A,C,p)]
W=S.exp(4*A+2*C)
expected=S.zeros(dim)
expected[0,0]=-3*App-Cpp+6*Ap**2+6*Ap*Cp-2*pp**2
for i,q in enumerate([None,C,A+p,A-p,A]):
    if i:
        expected[i,i]=g[i,i]/N**2*(S.diff(q,tau,2)-(2*W if i>=2 else 0))
assert all(S.simplify(Ric[i,j]-expected[i,j])==0 for i,j in product(I,repeat=2))
print('PASS all 25 exact nonlinear Ricci entries, including momentum constraints',flush=True)
# w=2A+C, w'=D*(1+q^2)/(1-q^2), e^w=D*q/(1-q^2), C'=B,p'=P.
q,D,B,P=S.symbols('q D B P',positive=True)
w1=D*(1+q**2)/(1-q**2); ew=D*q/(1-q**2)
w2=S.diff(w1,q)*D*q
assert S.simplify(w2-4*ew**2)==0
assert S.simplify(w1**2-4*ew**2-D**2)==0
sub={App:w2/2,Cpp:0,ppp:0,Ap:(w1-B)/2,Cp:B,pp:P,W:ew**2}
constraint=S.factor(expected[0,0].subs(sub,simultaneous=True))
assert S.simplify(constraint-(3*(D**2-B**2)/2-2*P**2))==0
print('PASS closed form vacuum iff D^2=B^2+4P^2/3',flush=True)
# Orthornormal curvature: diagonal time planes, spatial planes, mixed Codazzi.
@lru_cache(None)
def Rhat(a,b,c,d):
    return S.simplify(g[a,a]*R(a,b,c,d)/(scale[a]*scale[b]*scale[c]*scale[d]))
F=[None,C,A+p,A-p,A]; H=[None]+[S.diff(F[i],tau)/N for i in range(1,dim)]
for i in range(1,dim):
    assert S.simplify(Rhat(0,i,0,i)+S.diff(H[i],tau)/N+H[i]**2)==0
    for j in range(i+1,dim):
        assert S.simplify(Rhat(i,j,i,j)-H[i]*H[j]+(S.exp(-2*A) if i>=2 else 0))==0
# Verify pair-index curvature matrix; possible nonzero mixed only (0,i),(i,4), i=x,y.
pairs=list(combinations(I,2)); mixed=[]
for u,(a,b) in enumerate(pairs):
    for c,d in pairs[u+1:]:
        val=Rhat(a,b,c,d)
        if (a,b,c,d) in [(0,2,2,4),(0,3,3,4)]:
            assert S.simplify(val**2-S.exp(-2*A)*(H[b]-H[4])**2)==0
            mixed.append(val)
        else:
            assert val==0,(a,b,c,d,val)
assert len(mixed)==2
# K=4 sum of diagonal pair squares minus 8 sum of mixed pair squares.
print('PASS orthonormal Riemann matrix: 10 diagonal planes and 2 mixed Codazzi entries',flush=True)
# Asymptotic Kasner exponents and coefficient.
M=(3*D-B)/2
F0=[B,(D-B)/2+P,(D-B)/2-P,(D-B)/2]
assert S.simplify(sum(F0)-M)==0
assert S.simplify(sum(f**2 for f in F0)-M**2-(-3*D**2+3*B**2+4*P**2)/2)==0
# Scalar coefficient for nonzero anisotropy, positive via z-plane alone.
Q=[f/M for f in F0]
K0=4*(sum(u**2*(u-1)**2 for u in Q)+sum(Q[i]**2*Q[j]**2 for i,j in combinations(range(4),2)))
assert S.simplify(Q[-1]*(1-Q[-1])-2*D*(D-B)/(3*D-B)**2)==0
assert S.simplify(K0.subs({D:B,P:0},simultaneous=True))==0
print('PASS Kasner identities, positive lower bound from z tidal plane when D>B',flush=True)
# Isotropic background normalization: q=b=t/sqrt(t^2+B), a^2=B/(1-q^2).
t=S.symbols('t',positive=True)
q0=t/S.sqrt(t*t+B)
a2=B/(1-q0*q0)
assert S.simplify(a2-(t*t+B))==0
V0=t*(t*t+B)
assert S.simplify(S.diff(S.log(q0)/B,t)-1/V0)==0
print('PASS exact P=0 background match',flush=True)
print('LIMIT: homogeneous nonlinear family; no global finite-total-energy or generic instability theorem',flush=True)
