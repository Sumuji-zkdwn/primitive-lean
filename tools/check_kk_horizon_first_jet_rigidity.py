"""Exact horizon Ricci jet checks in 5D Gaussian-null coordinates.
At a point use transverse Riemannian normal coordinates; q_ij=delta_ij,
q_ij,k=0. All unneeded higher derivatives are left symbolic.
No claims of nonlinear PDE existence or full Killing rigidity.
"""
import sympy as s
from functools import lru_cache
from itertools import product
I=range(5); J=range(2,5); u,v=0,1
F=s.Symbol('F',real=True); B={i:s.Symbol(f'b{i}',real=True) for i in J}
F1={i:s.Symbol(f'F_{i}',real=True) for i in I}
B1={(i,j):s.Symbol(f'b{i}_{j}',real=True) for i in J for j in I}
def symmat(prefix):return {(i,j):s.Symbol(f'{prefix}{min(i,j)}{max(i,j)}',real=True) for i,j in product(J,repeat=2)}
H=symmat('H'); S=symmat('S'); Hv=symmat('Hv'); Sv=symmat('Sv')
@lru_cache(None)
def q2(i,j,k,l):
    i,j=sorted((i,j)); k,l=sorted((k,l))
    if (k,l)==(v,v):return Hv[i,j]
    if (k,l)==(u,v):return Sv[i,j]
    return s.Symbol(f'q{i}{j}_{k}{l}',real=True)
G=s.zeros(5);G[u,v]=G[v,u]=-1
for i in J:G[i,i]=1
assert G.inv()==G
nonzero=[(i,j,G[i,j]) for i,j in product(I,repeat=2) if G[i,j]!=0]
@lru_cache(None)
def dg(i,j,k):
    i,j=sorted((i,j))
    if i==j==v:return F if k==u else 0
    if i==v and j in J:return B[j] if k==u else 0
    if i in J and j in J:return S[i,j] if k==u else H[i,j] if k==v else 0
    return 0
@lru_cache(None)
def ddg(i,j,k,l):
    i,j=sorted((i,j));k,l=sorted((k,l))
    if i==j==v:return (2 if l==u else 1)*F1[l] if k==u else 0
    if i==v and j in J:return (2 if l==u else 1)*B1[j,l] if k==u else 0
    if i in J and j in J:return q2(i,j,k,l)
    return 0
@lru_cache(None)
def C(a,b,c):return (dg(a,c,b)+dg(a,b,c)-dg(b,c,a))/2
@lru_cache(None)
def ric(b,d):
    deriv=sum(w*(ddg(a,d,b,c)+ddg(b,c,a,d)-ddg(a,c,b,d)-ddg(b,d,a,c))/2 for a,c,w in nonzero)
    quad=sum(w*t*(C(e,b,c)*C(f,a,d)-C(e,b,d)*C(f,a,c)) for a,c,w in nonzero for e,f,t in nonzero)
    return s.expand(deriv+quad)
tr=lambda A:sum(A[i,i] for i in J)
trH2=sum(H[i,j]**2 for i,j in product(J,repeat=2))
expect=-tr(Hv)/2+trH2/4+F*tr(H)/4
print('Rvv residual:',s.simplify(ric(v,v)-expect)); assert s.simplify(ric(v,v)-expect)==0
noH={x:0 for x in list(H.values())+list(Hv.values())+[q2(i,j,v,k) for i,j in product(J,repeat=2) for k in J]}
for i in J:
    a=s.expand(ric(v,i).subs(noH)); print('Rv',i,a);assert s.simplify(a-(B1[i,v]-F1[i])/2)==0
# transverse Ricci in normal coords, quadratic intrinsic Gamma=0
for i,j in product(J,repeat=2):
    rQ=sum((q2(k,j,i,k)+q2(i,k,k,j)-q2(k,k,i,j)-q2(i,j,k,k))/2 for k in J)
    a=s.expand(ric(i,j).subs(noH)-rQ)
    expect=Sv[i,j]+F*S[i,j]/2-(B1[i,j]+B1[j,i])/2-B[i]*B[j]/2
    print('Rij residual',i,j,s.simplify(a-expect));assert s.simplify(a-expect)==0
print('PASS exact Ricci vv, vA, AB horizon jets')
# Future cone lower bound by completing the square, valid for general q.
r,w,b,x,Q=s.symbols('r w b x Q',real=True); F0=s.symbols('F0',real=True)
assert s.expand((-2*r*w+F0*w*w+2*b*w*x+Q*x*x)-(-2*r*w+(F0-b*b/Q)*w*w+Q*(x+b*w/Q)**2))==0
print('PASS square completion (general screen follows by matrix contraction)')
