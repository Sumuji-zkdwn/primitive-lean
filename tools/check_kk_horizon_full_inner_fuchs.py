"""Exact indicial and scalarization checks for fixed-background inner waves.
The Fuchsian theorem and analytic elliptic continuation are analytic inputs.
"""
from itertools import product, combinations_with_replacement
from functools import lru_cache
from collections import Counter
import sympy as S

r,s,z,u=S.symbols('r s z u',positive=True)
v,x,y,k=S.symbols('v x y k',real=True)
X=(r,v,x,y,z); I=range(5)
f=1-s*s/r**2
G=S.diag(0,f,r*r/z**2,r*r/z**2,r*r/z**2)
G[0,1]=G[1,0]=-1
Gi=G.inv().applyfunc(S.cancel)
@lru_cache(None)
def Gamma(a,b,c):
    return S.cancel(sum(Gi[a,d]*(S.diff(G[d,c],X[b])+S.diff(G[d,b],X[c])-S.diff(G[b,c],X[d]))/2 for d in I))
C1=[S.Matrix(5,5,lambda i,j:-Gamma(j,mu,i)) for mu in I]
assert C1[1].subs(r,s)==S.diag(1/s,-1/s,0,0,0)
assert all(S.denom(S.cancel(e)).subs(r,s)!=0 for C in C1 for e in C)
# scalar drift, including transverse part
nz=[(i,j,Gi[i,j]) for i,j in product(I,repeat=2) if Gi[i,j]!=0]
assert S.cancel(-sum(g*Gamma(0,i,j) for i,j,g in nz)+S.diff(f,r)+3*f/r)==0
assert S.cancel(-sum(g*Gamma(1,i,j) for i,j,g in nz)+3/r)==0
F=f.subs(r,s-u)
B=S.cancel(u*(-S.diff(f,r)-3*f/r-2*S.I*k).subs(r,s-u)/F)
H=S.cancel(-u*u/(F*(s-u)**2))
assert S.simplify(S.limit(B,u,0)-1-S.I*k*s)==0
assert S.cancel(H-u/(2*s-u))==0
print('PASS regular connection, scalar indicial factor and screen weight')

D=S.symbols('D'); m=3
poly=(D+m)*S.prod(D+m+S.I*k*s+w for w in range(-2,3))
for rank in (1,2):
    labels=[(i,) for i in I] if rank==1 else list(combinations_with_replacement(I,2))
    n=len(labels); idx={a:i for i,a in enumerate(labels)}
    Cs=[]
    for mu in I:
        C=S.zeros(n)
        for i,inds in enumerate(labels):
            for slot in range(rank):
                for j in I:
                    ind=list(inds); ind[slot]=j
                    C[i,idx[tuple(sorted(ind))]]+=C1[mu][inds[slot],j]
        Cs.append(C.applyfunc(S.cancel))
    wts=[sum({0:1,1:-1,2:0,3:0,4:0}[i] for i in a) for a in labels]
    assert Cs[1].subs(r,s)==S.diag(*[S.Rational(w)/s for w in wts])
    Ar=(-2*f*Cs[0]-2*Cs[1]).applyfunc(S.cancel)
    # multiplying (Box + V) by -u²/F gives +(u/F) Ar D
    radial=(u/F*Ar.subs(r,s-u)).applyfunc(S.cancel)
    r0=radial.applyfunc(lambda e:S.simplify(S.limit(e,u,0,dir='+')))
    assert r0==S.diag(*wts)
    # Remaining matrix coefficients are analytic at the horizon; bounded curvature
    # terms are covered by the explicit factor u²/F=O(u).
    for C in Cs:
        for e in C:
            assert S.denom(S.cancel(e)).subs(r,s)!=0
    for w in wts:
        p=(D+m)*(D+m+S.I*k*s+w)
        A=S.prod(D+m+S.I*k*s+j for j in range(-2,3) if j!=w)
        assert S.Poly(A,D).degree()==4 and S.Poly(A,D).LC()==1
        assert S.expand(A*p-poly)==0
    assert min(m+w for w in wts)>0
    print(f'PASS rank {rank}, components {n}, weight multiplicities {sorted(Counter(wts).items())}')
assert S.Poly(poly,D).degree()==6 and S.Poly(poly,D).LC()==1
assert all(m+w>0 for w in range(-2,3))
# Formal order audit after multiplying by the monic degree-four row operators.
# radial Euler power j, screen derivative count d, whether matrix-valued.
# Scalar principal screen term may be encoded without a fiber derivative.
for j,d,matrix in [(1,0,True),(0,0,True),(0,1,True),(0,2,False)]:
    for a in range(5):
        for hit in range(a+1): # D's landing on coefficient
            euler=j+a-hit
            scalar=(not matrix and a==4)
            fiber=0 if scalar else 1
            assert euler<6 and euler+d+fiber<=6
            assert d+fiber<=3
# Encoding matrix action on a linear polynomial (arbitrary component count).
N=15
w=S.Matrix(S.symbols('w0:'+str(N))); q=S.Matrix(S.symbols('q0:'+str(N)))
M=S.Matrix(N,N,lambda i,j:S.Symbol(f'M{i}_{j}'))
p=(w.T*q)[0]
assert S.expand(sum(w[i]*M[i,j]*S.diff(p,w[j]) for i,j in product(range(N),repeat=2))-(w.T*M*q)[0])==0
print('PASS common monic degree-six scalarization, weighted derivative-order audit, and 15-component matrix lift')
print('LIMIT: analytic fixed background; gauge-fixed wave uniqueness, not arbitrary-gauge nonlinear rigidity')
