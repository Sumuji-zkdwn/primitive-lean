"""Exact algebraic audit of the 20-component Fuchsian reduction and interior gauge.
Analytic PDE uniqueness and local elliptic solvability are external theorems.
The actual weighted Ricci row coefficients were audited by the #290 script.
"""
import sympy as S
from itertools import product
from collections import Counter

lam,k,s=S.symbols('lam k s', real=True)
I=S.I
# U=(S,DS), D=(w/2) d_w, W=w^-4 U. A0=2 M0-4 I.
# These are the two audited diagonal polynomials in #290.
blocks=[]
for a,b,count in [(0,-S.Rational(1,4),4),(I*k*s,0,6)]:
    M=S.Matrix([[0,1],[-b,-a]])
    A=2*M-4*S.eye(2)
    expected=(lam+5)*(lam+3) if count==4 else (lam+4)*(lam+4+2*I*k*s)
    assert S.expand((lam*S.eye(2)-A).det()-expected)==0
    blocks.extend([A]*count)
A0=S.diag(*blocks)
assert A0.shape==(20,20)
assert S.expand(S.prod((lam*S.eye(2)-B).det() for B in blocks)-(lam+5)**4*(lam+3)**4*(lam+4)**6*(lam+4+2*I*k*s)**6)==0
assert all(S.re(root)<0 for root in [-5,-3,-4,-4-2*I*k*s])
print('PASS 20-component indicial matrix; all exponents strictly negative, including k=0')
# Volevic weights n_S=0, n_V=1. Full possible derivative support,
# using monic D² and j+|alpha|<=2 from #290.
weights={'S':0,'V':1}
orders={('S','V'):{0},('S','S'):{0},('V','S'):{0,1,2},('V','V'):{0,1}}
for (row,col), ds in orders.items():
    for d in ds: assert d<=weights[row]-weights[col]+1
# The leading matrices have no tangential differentiation. All residual
# terms carry w, and conjugation by w^-4 does not alter spatial order.
w=S.symbols('w',positive=True); F=S.Function('F'); D=lambda x:w*S.diff(x,w)/2
assert S.expand(D(w**4*F(w))/w**4-D(F(w))-2*F(w))==0
print('PASS Volevic order bounds without scalar lift or extra derivative variables')
# Interior residual radial-gauge vector, in mode k, from arbitrary initial
# data at r0. Its r dependence is analytic regardless of the x regularity.
r,r0,z=S.symbols('r r0 z',positive=True); x,y,v=S.symbols('x y v',real=True)
X=(r,v,x,y,z); screen=(x,y,z)
f=1-s*s/r**2
g=S.diag(0,f,r*r/z**2,r*r/z**2,r*r/z**2); g[0,1]=g[1,0]=-1
inv=g.inv(); assert S.simplify(inv[0,0]+f)==0
assert inv[2:5,2:5]==S.eye(3)*z*z/r**2
phase=S.exp(I*k*v)
a=S.Function('a')(*screen); b=S.Function('b')(*screen)
c=[S.Function('c'+str(j))(*screen) for j in range(3)]
Y=phase*S.Matrix([b-I*k*(r-r0)*a,a,*[c[j]+z*z*S.diff(a,screen[j])*(1/r0-1/r) for j in range(3)]])
for j in range(5):
    lie=sum(Y[l]*S.diff(g[0,j],X[l])+g[l,j]*S.diff(Y[l],r)+g[0,l]*S.diff(Y[l],X[j]) for l in range(5))
    assert S.simplify(lie)==0
for i,j in product(range(5),repeat=2):
    lie=S.expand(sum(Y[l]*S.diff(g[i,j],X[l])+g[l,j]*S.diff(Y[l],X[i])+g[i,l]*S.diff(Y[l],X[j]) for l in range(5))/phase)
    # Clear powers of r; remaining coefficients are arbitrary smooth screen jets.
    assert S.denom(S.cancel(lie)).subs(r,r0)!=0
print('PASS residual radial gauge explicit r-analytic formula, all five radial slots')
# Principal symbol in interior after mode separation; use u=s-r.
u=S.symbols('u',positive=True)
assert S.cancel((-f).subs(r,s-u)-u*(2*s-u)/(s-u)**2)==0
print('PASS elliptic principal signs on 0<r<s; local gauge solve only away from horizon')
