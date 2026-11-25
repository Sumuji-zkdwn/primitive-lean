import sympy as s
from itertools import product
from functools import lru_cache
I=range(5); A=range(2,5); u,v=0,1
G=s.diag(0,0,1,1,1); G[0,1]=G[1,0]=-1
nz=[(i,j,G[i,j]) for i,j in product(I,repeat=2) if G[i,j]!=0]
F=s.Symbol('F', real=True)
b={i:s.Symbol(f'b{i}') for i in A}
S={(i,j):s.Symbol(f'S{min(i,j)}{max(i,j)}') for i,j in product(A,repeat=2)}
H={(i,j):s.Symbol(f'H{min(i,j)}{max(i,j)}') for i,j in product(A,repeat=2)}
a=s.Symbol('a'); w={i:s.Symbol(f'w{i}') for i in A}
# arbitrary leading coefficient of metric difference
@lru_cache(None)
def h(i,j):
    i,j=sorted((i,j))
    if i==j==v: return a
    if i==v and j in A: return w[j]
    if i in A and j in A: return H[i,j]
    return 0
# coefficients of second radial derivative, Ricci principal term at u=0
@lru_cache(None)
def d2(i,j,k,l): return h(i,j) if k==l==u else 0
@lru_cache(None)
def principal(b,d):
    return s.expand(sum(t*(d2(i,d,b,j)+d2(b,j,i,d)-d2(i,j,b,d)-d2(b,d,i,j))/2 for i,j,t in nz))
assert principal(u,v)==-a/2
assert all(principal(u,i)==-w[i]/2 for i in A)
assert principal(u,u)==-sum(H[i,i] for i in A)/2
assert all(principal(i,j)==0 for i,j in product(A,repeat=2))
print('PASS leading radial constraints Ric_uv, Ric_uA, Ric_uu; Ric_AB has no order m-2 term')
# at horizon normalized v-independent first jets; use normal screen chart.
@lru_cache(None)
def base_dg(i,j,k):
    i,j=sorted((i,j))
    if k!=u:return 0
    if i==j==v:return F
    if i==v and j in A:return b[j]
    if i in A and j in A:return S[i,j]
    return 0
@lru_cache(None)
def delta_dg(i,j,k):return H[i,j] if k==u and i in A and j in A else 0
@lru_cache(None)
def C(which,a,b,c):
    dg=base_dg if which==0 else delta_dg
    return (dg(a,c,b)+dg(a,b,c)-dg(b,c,a))/2
# exact first variation of quadratic Ricci term, no second derivative terms included.
for i,j in product(A,repeat=2):
    quad=s.expand(sum(t*l*(C(1,e,i,c)*C(0,f,a,j)+C(0,e,i,c)*C(1,f,a,j)-C(1,e,i,j)*C(0,f,a,c)-C(0,e,i,j)*C(1,f,a,c)) for a,c,t in nz for e,f,l in nz))
    assert s.simplify(quad-F*H[i,j]/2)==0,(i,j,quad)
print('PASS all nine screen quadratic cross terms = F H_AB/2')
# mixed second partials at coefficient order m-1, delta h_v* leading eliminated.
Hv={(i,j):s.Symbol(f'V{min(i,j)}{max(i,j)}') for i,j in product(A,repeat=2)}
Hx={(i,j,k):s.Symbol(f'X{min(i,j)}{max(i,j)}_{k}') for i,j in product(A,repeat=2) for k in A}
@lru_cache(None)
def mix(i,j,k,l):
    if not (i in A and j in A): return 0
    if sorted((k,l))==[u,v]:return Hv[i,j]
    if min(k,l)==u and max(k,l) in A:return Hx[i,j,max(k,l)]
    return 0
for i,j in product(A,repeat=2):
    mixed=s.expand(sum(t*(mix(a,j,i,c)+mix(i,c,a,j)-mix(a,c,i,j)-mix(i,j,a,c))/2 for a,c,t in nz))
    assert mixed==Hv[i,j],(i,j,mixed)
# inverse correction from g^uu = -uF+O(u²) contracts radial second derivatives
for i,j in product(A,repeat=2):
    rad=s.expand(-F*(d2(u,j,i,u)+d2(i,u,u,j)-d2(u,u,i,j)-d2(i,j,u,u))/2)
    assert rad==F*H[i,j]/2
m=s.symbols('m', integer=True, positive=True); k=s.symbols('k', real=True)
assert s.expand(m*(m-1)*F/2+m*F/2-m*m*F/2)==0
assert s.expand((m*m*F/2).subs(F,2*k)-m*m*k)==0
print('PASS all nine mixed and inverse radial terms; recurrence m*(d_v H + m*kappa H)')
print('LIMIT: local jet algebra only; induction and analytic continuation are hand proofs; smooth unique continuation open')
