"""Exact local identities for a Hausdorff vacuum extension.

The global Cauchy uniqueness, compact-action argument and quotient topology
are analytic proofs in the companion note, not computed by this script.
"""
from functools import lru_cache
from itertools import product
import sympy as S

r,s,z=S.symbols('r s z', positive=True)
v,x,y=S.symbols('v x y', real=True)
X=(r,v,x,y,z); I=range(5)
f=1-s**2/r**2
G=S.Matrix([[0,-1,0,0,0],[-1,f,0,0,0],[0,0,r**2/z**2,0,0],[0,0,0,r**2/z**2,0],[0,0,0,0,r**2/z**2]])
Gi=S.simplify(G.inv())
assert S.simplify(G.det()+r**6/z**6)==0
assert Gi[:2,:2]==S.Matrix([[-f,-1],[-1,0]])
@lru_cache(None)
def Gamma(a,b,c):
    return S.simplify(sum(Gi[a,d]*(S.diff(G[d,c],X[b])+S.diff(G[d,b],X[c])-S.diff(G[b,c],X[d]))/2 for d in I))
@lru_cache(None)
def R(a,b,c,d):
    return S.simplify(S.diff(Gamma(a,d,b),X[c])-S.diff(Gamma(a,c,b),X[d])+sum(Gamma(a,c,e)*Gamma(e,d,b)-Gamma(a,d,e)*Gamma(e,c,b) for e in I))
Ric=S.Matrix(5,5,lambda b,d:S.simplify(sum(R(a,b,a,d) for a in I)))
assert Ric==S.zeros(5)
assert S.simplify(G.det().subs(r,s)+s**6/z**6)==0
print('PASS all 25 vacuum Ricci components and nondegenerate horizon metric')
# The periodic Killing field V=partial_v has dual one-form -dr+f dv.
V=S.Matrix([0,1,0,0,0]); Vflat=G*V
F=S.Matrix(5,5,lambda a,b:S.simplify(S.diff(Vflat[b],X[a])-sum(Gamma(c,a,b)*Vflat[c] for c in I)))
assert F+F.T==S.zeros(5)
assert F[0,1]==S.diff(f,r)/2
assert F[1,0]==-S.diff(f,r)/2
assert all(F[a,b]==0 for a,b in product(I,repeat=2) if (a,b) not in [(0,1),(1,0)])
F2=S.simplify(S.trace(F.T*Gi*F*Gi))
assert S.simplify(F2+S.diff(f,r)**2/2)==0
assert S.simplify(F2.subs(r,s)+2/s**2)==0
assert S.simplify((V.T*G*V)[0]-f)==0
print('PASS Killing norm and negative invariant at horizon:',F2.subs(r,s))
# A compact isometry isotropy generator cannot have these real boost eigenvalues.
lam=S.symbols('lambda',real=True)
A=Gi*F
cp=A.charpoly(lam); l=cp.gen
assert S.simplify(cp.as_expr()-l**3*(l**2-S.diff(f,r)**2/4))==0
print('PASS boost spectrum of raised antisymmetric tensor')
# Explicit smooth timelike direction across the horizon.
W=S.Matrix([1,1,0,0,0])
assert S.simplify((W.T*G*W)[0]+1+s**2/r**2)==0
# In the added collar, r=s-d with 0<d<s. Norm is strictly negative.
d=S.symbols('d',positive=True)
assert S.simplify(f.subs(r,s-d)-d*(d-2*s)/(s-d)**2)==0
print('PASS time orientation and algebraic sign of closed timelike orbit')
print('LIMIT: global topology and Cauchy-development identification are analytic arguments')
