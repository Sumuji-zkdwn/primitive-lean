"""Exact regular-coordinate checks for the full linear vacuum wave system.
The existence, energy, gauge reduction and uniqueness proofs are analytic.
"""
import sympy as S
from functools import lru_cache
from itertools import product, combinations_with_replacement
from pathlib import Path
import hashlib

r,s,z=S.symbols('r s z',positive=True)
v,x,y=S.symbols('v x y',real=True)
X=(r,v,x,y,z); I=range(5)
f=1-s**2/r**2
G=S.Matrix([[0,-1,0,0,0],[-1,f,0,0,0],[0,0,r**2/z**2,0,0],[0,0,0,r**2/z**2,0],[0,0,0,0,r**2/z**2]])
Gi=G.inv().applyfunc(S.cancel)
assert S.cancel(G.det()+r**6/z**6)==0
nz=[(i,j,Gi[i,j]) for i,j in product(I,repeat=2) if Gi[i,j]!=0]
@lru_cache(None)
def Gamma(a,b,c):
    return S.cancel(sum(Gi[a,d]*(S.diff(G[d,c],X[b])+S.diff(G[d,b],X[c])-S.diff(G[b,c],X[d]))/2 for d in I))
@lru_cache(None)
def Rup(a,b,c,d):
    return S.cancel(S.diff(Gamma(a,d,b),X[c])-S.diff(Gamma(a,c,b),X[d])+sum(Gamma(a,c,e)*Gamma(e,d,b)-Gamma(a,d,e)*Gamma(e,c,b) for e in I))
@lru_cache(None)
def Rlow(a,b,c,d):
    return S.cancel(sum(G[a,e]*Rup(e,b,c,d) for e in I))
assert all(S.cancel(sum(Rup(a,b,a,d) for a in I))==0 for b,d in product(I,repeat=2))
# No 1/f denominator occurs in the regular EF chart.
def regular(expr):
    den=S.Poly(S.denom(S.cancel(expr)),r,z,s)
    return len(den.terms())==1 and den.terms()[0][0][2]==0
assert all(regular(e) for e in list(G)+list(Gi))
assert all(regular(Gamma(a,b,c)) for a,b,c in product(I,repeat=3))
assert all(regular(Rlow(a,b,c,d)) for a,b,c,d in product(I,repeat=4))
print('PASS all 25 background Ricci entries and regular connection/curvature at r=s')
# Scalar wave drift -g^{mu nu} Gamma^lambda_{mu nu}.
drift=[S.cancel(-sum(g*Gamma(k,i,j) for i,j,g in nz)) for k in I]
assert drift==[S.cancel(-S.diff(f,r)-3*f/r),-3/r,0,0,-z/r**2]
# Coordinate scalar wave operator: -t^2 Box_0 in logarithmic time.
t,chi=S.symbols('t chi',positive=True); chi=S.Symbol('chi',real=True)
rr=S.sqrt(s*s+t*t); ff=t*t/rr**2
p=S.Function('p')(t,chi)
Dr=lambda h: rr/t*S.diff(h,t)-S.diff(h,chi)/ff
L=ff*Dr(Dr(p))+(Dr(ff)+3*ff/rr)*Dr(p)+2*Dr(S.diff(p,chi))+3*S.diff(p,chi)/rr
De=lambda h:t*S.diff(h,t)
a=rr**2; b=t*t/rr**2
assert S.simplify(t*t*L-(De(De(p))+2*b*De(p)-a*S.diff(p,chi,2)))==0
assert S.simplify(De(a)-2*b*a)==0 and S.simplify(De(b)-2*(1-b)*b)==0
assert S.simplify(De(S.asinh(t/s))-S.sqrt(b))==0
print('PASS scalar principal/drift, exact time change and screen speed')
# Connection matrices on the regular coordinate components (covectors and symmetric 2-tensors).
# D_mu = partial_mu + C_mu. In the rough wave operator the principal part
# is the scalar wave componentwise; A^k=2g^{k mu}C_mu and
# B=g^{mu nu}(partial_mu C_nu+C_mu C_nu-Gamma^k_mu nu C_k).
for rank in (1,2):
    labels=[(i,) for i in I] if rank==1 else list(combinations_with_replacement(I,2))
    n=len(labels); idx={label:j for j,label in enumerate(labels)}
    Cs=[]
    for mu in I:
        C=S.zeros(n)
        for row,label in enumerate(labels):
            for slot in range(rank):
                for k in I:
                    L=list(label); L[slot]=k
                    C[row,idx[tuple(sorted(L))]]-=Gamma(k,mu,label[slot])
        Cs.append(C.applyfunc(S.cancel))
    As=[sum((2*g*Cs[j] for i,j,g in nz if i==k),S.zeros(n)).applyfunc(S.cancel) for k in I]
    B=sum((g*(Cs[j].diff(X[i])+Cs[i]*Cs[j]-sum((Gamma(k,i,j)*Cs[k] for k in I),S.zeros(n))) for i,j,g in nz),S.zeros(n)).applyfunc(S.cancel)
    if rank==2:
        # Curvature endomorphism in harmonic gauge: 2 R_{a c b d} h^{cd}.
        K=S.zeros(n)
        for row,(a0,b0) in enumerate(labels):
            for c,i,gci in nz:
                for d,j,gdj in nz:
                    K[row,idx[tuple(sorted((i,j)))]]+=2*Rlow(a0,c,b0,d)*gci*gdj
        B=(B+K).applyfunc(S.cancel)
    assert all(regular(e) for M in As+[B] for e in M)
    # -t² A^r partial_r -t² A^v partial_v transforms to
    # -r A^r partial_eta + (r² A^r-t² A^v) partial_chi.
    # Weighted chi derivative /r and screen derivative /(t/r) stay bounded.
    t2=r*r-s*s
    Aeta=(-r*As[0]).applyfunc(S.cancel)
    Ach=((r*r*As[0]-t2*As[1])/r).applyfunc(S.cancel)
    Ax=[(-r*As[k]).applyfunc(S.cancel) for k in (2,3,4)] # multiply by t afterwards
    V=(-t2*B).applyfunc(S.cancel)
    assert all(regular(e) for M in [Aeta,Ach,*Ax,V] for e in M)
    print(f'PASS rank {rank}: {n} components, all weighted first-order and potential coefficients regular')
# Base energy (without lower-order matrix terms) and boundary flux.
a,b,X0,Y0,Z0,G0=S.symbols('a b X0 Y0 Z0 G0',real=True)
e=(X0**2+a*Y0**2+b*G0**2+Z0**2)/2
bulk=-2*b*X0**2+b*a*Y0**2+(1-b)*b*G0**2+X0*Z0
sos=(X0-Z0)**2/2+(S.Rational(1,2)+2*b)*X0**2+(1-b)*a*Y0**2+b*b*G0**2+Z0**2/2
assert S.expand(2*e-bulk-sos)==0
c,n,j=S.symbols('c n j',real=True)
eb=(X0**2+a*Y0**2+c*c*(n*n+j*j)+Z0**2)/2
assert S.expand(c*eb-c*c*X0*n-c*((X0-c*n)**2+a*Y0**2+c*c*j*j+Z0**2)/2)==0
print('PASS positive energy bound and moving-ball flux')
print('LIMIT: algebraic identities, not a computer proof of the PDE existence/uniqueness theorem')
print('SHA256',hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
