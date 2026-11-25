"""Symbolic radial-gauge reduction for the fixed five-dimensional vacuum collar.
Checks the flat gauge equations and the leading weighted Ricci system; no PDE
uniqueness theorem is asserted by this script.
"""
from functools import lru_cache
from itertools import product, combinations_with_replacement
from collections import defaultdict
import sympy as S

r,s,z=S.symbols('r s z', positive=True)
v,x,y=S.symbols('v x y',real=True)
X=(r,v,x,y,z); I=range(5); A=range(2,5)
f=1-s*s/r**2
g=S.diag(0,f,*[r*r/z**2]*3); g[0,1]=g[1,0]=-1
G=g.inv().applyfunc(S.cancel)
labels=list(combinations_with_replacement(range(1,5),2))
# Coordinate Lie derivative in the radial slots: arbitrary vector field.
Y=S.Matrix([S.Function('Y'+str(i))(*X) for i in I])
def lie(i,j):
    return S.expand(sum(Y[k]*S.diff(g[i,j],X[k])+g[k,j]*S.diff(Y[k],X[i])+g[i,k]*S.diff(Y[k],X[j]) for k in I))
assert S.simplify(lie(0,0)+2*S.diff(Y[1],r))==0
assert S.simplify(lie(0,1)+S.diff(Y[0],r)-f*S.diff(Y[1],r)+S.diff(Y[1],v))==0
for i in A:
    assert S.simplify(lie(0,i)-r*r/z**2*S.diff(Y[i],r)+S.diff(Y[1],X[i]))==0
print('PASS all five radial gauge equations',flush=True)
# Linearize the Ricci formula in terms of independent metric jets. v-derivatives
# are replaced by ik only after extracting the coefficients.
@lru_cache(None)
def h(i,j,der=()):
    p=tuple(sorted((i,j)))
    if p not in labels:return S.Integer(0)
    return S.Symbol('h'+str(p[0])+str(p[1])+'_'+''.join(map(str,der)))
@lru_cache(None)
def C(a,b,c):return (S.diff(g[a,c],X[b])+S.diff(g[a,b],X[c])-S.diff(g[b,c],X[a]))/2
@lru_cache(None)
def dC(a,b,c):return (h(a,c,(b,))+h(a,b,(c,))-h(b,c,(a,)))/2
@lru_cache(None)
def E(a,c,b,d):return S.diff(g[a,d],X[b],X[c])+S.diff(g[b,c],X[a],X[d])-S.diff(g[a,c],X[b],X[d])-S.diff(g[b,d],X[a],X[c])
@lru_cache(None)
def dE(a,c,b,d):
    hd=lambda i,j,k,l:h(i,j,tuple(sorted((k,l))))
    return hd(a,d,b,c)+hd(b,c,a,d)-hd(a,c,b,d)-hd(b,d,a,c)
H=S.Matrix(5,5,lambda i,j:h(i,j)); dG=-G*H*G
gnz=[(i,j,G[i,j]) for i,j in product(I,repeat=2) if G[i,j]!=0]
dgnz=[(i,j,dG[i,j]) for i,j in product(I,repeat=2) if dG[i,j]!=0]
@lru_cache(None)
def deltaRic(b,d):
    val=sum(w*dE(a,c,b,d)/2 for a,c,w in gnz)+sum(w*E(a,c,b,d)/2 for a,c,w in dgnz)
    for a,c,w in gnz:
        for e,l,q in gnz:
            val+=w*q*(dC(e,b,c)*C(l,a,d)+C(e,b,c)*dC(l,a,d)-dC(e,b,d)*C(l,a,c)-C(e,b,d)*dC(l,a,c))
    for terms1,terms2 in [(dgnz,gnz),(gnz,dgnz)]:
        for a,c,w in terms1:
            for e,l,q in terms2:
                val+=w*q*(C(e,b,c)*C(l,a,d)-C(e,b,d)*C(l,a,c))
    val=S.expand(val)
    return {j:S.cancel(val.coeff(j)) for j in val.free_symbols if j.name.startswith('h') and val.coeff(j)!=0}
# In w=sqrt(s-r), set h_v*=w S_v*, h_AB=S_AB. D=u d_u, u=w².
w=S.symbols('w',positive=True); k=S.symbols('k',real=True); D=S.symbols('D')
F=f.subs(r,s-w*w)
rows=[(0,j) for j in range(1,5)]+list(combinations_with_replacement(A,2))
for row in rows:
    screen=row[0]!=0
    target=row if screen else (1,row[1])
    norm=2*w**4/F if screen else -2*w**3
    result=defaultdict(lambda:S.Integer(0))
    for jet,c in deltaRic(*row).items():
        pair=tuple(map(int,jet.name[1:3])); der=jet.name[4:]
        l=der.count('0'); nv=der.count('1'); tang=der.replace('0','').replace('1','')
        a=S.Rational(1,2) if pair[0]==1 else S.Integer(0)
        fac=(-1)**l*w**(2*a-2*l)*(S.I*k)**nv*S.prod(D+a-j for j in range(l))
        result[pair,tang]+=norm*c.subs(r,s-w*w)*fac
    target_poly=(D*(D+S.I*k*s) if screen else (D+S.Rational(1,2))*(D-S.Rational(1,2)))
    for key,c in result.items():
        c=S.Poly(S.cancel(c),D)
        for (j,),p in c.terms():
            # Every coefficient is analytic in w, and its constant limit
            # equals the stated indicial diagonal. The residual vanishes O(w).
            expected=S.expand(target_poly).coeff(D,j) if key==(target,'') else 0
            num,den=S.fraction(S.cancel(p)); assert S.simplify(den.subs(w,0))!=0,(row,key,j,p)
            assert S.simplify(p.subs(w,0)-expected)==0,(row,key,j,p,expected)
            # The equation is monic in D^2, with no additional second radial term.
            if j==2: assert S.simplify(p-expected)==0,(row,key,j,p)
            assert j+len(key[1])<=2
    for j in range(3):
        assert S.simplify(S.expand(S.Poly(S.cancel(result[target,'']),D).as_expr()).coeff(D,j).subs(w,0)-S.expand(target_poly).coeff(D,j))==0
    print('PASS weighted row',row,'indicial',S.factor(target_poly),flush=True)
print('LIMIT: analytic-coefficient radial-gauge Fuchsian system; local coupled uniqueness not checked by this script',flush=True)
# Unlike the wave-gauge operator, the top tangential symbol is not scalar:
# R_xx contains a second x derivative of h_yy. A direct auxiliary-variable
# matrix lift of this term would add one differential order.
assert S.cancel(deltaRic(2,2)[h(3,3,(2,2))]+z*z/(2*r*r))==0
assert S.cancel((2*w**4/F*deltaRic(2,2)[h(3,3,(2,2))].subs(r,s-w*w))-w*w*z*z/(2*s-w*w))==0
print('PASS non-scalar tangential principal coefficient',flush=True)
# Flatness permits shifting by u^2. Both row polynomials then have roots
# with negative real parts (including k=0).
pbase=(D+2+S.Rational(1,2))*(D+2-S.Rational(1,2))
pscreen=(D+2)*(D+2+S.I*k*s)
assert S.expand(pbase-(D+S.Rational(5,2))*(D+S.Rational(3,2)))==0
assert S.re(-2-S.I*k*s)==-2
print('PASS shifted indicial root audit',flush=True)
