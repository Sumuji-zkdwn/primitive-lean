"""Metric-only homogeneous shear on the curved 5D compact-circle horizon.
Direct exact tensor calculation; no independent scalar stress tensor.
"""
from functools import lru_cache
import sympy as S

r, s, z = S.symbols('r s z', positive=True)
v, x, y = S.symbols('v x y', real=True)
coords = (r,v,x,y,z)
p = S.Function('p')(r,v)
f = 1-s**2/r**2
w = r**2/z**2
g = S.Matrix([[0,-1,0,0,0],[-1,f,0,0,0],[0,0,w*S.exp(2*p),0,0],[0,0,0,w*S.exp(-2*p),0],[0,0,0,0,w]])
N = len(coords)
G = S.simplify(g.inv())
assert S.simplify(g.det()+w**3)==0
@lru_cache(None)
def C(a,b,c):
    return S.simplify(sum(G[a,d]*(S.diff(g[d,c],coords[b])+S.diff(g[d,b],coords[c])-S.diff(g[b,c],coords[d]))/2 for d in range(N)))
@lru_cache(None)
def R(a,b,c,d):
    return S.simplify(S.diff(C(a,d,b),coords[c])-S.diff(C(a,c,b),coords[d])+sum(C(a,c,h)*C(h,d,b)-C(a,d,h)*C(h,c,b) for h in range(N)))
Ric = S.Matrix(N,N,lambda b,d:S.simplify(sum(R(a,b,a,d) for a in range(N))))
pr,pv = S.diff(p,r),S.diff(p,v)
L = f*S.diff(p,r,2)+(S.diff(f,r)+3*f/r)*pr+2*S.diff(p,r,v)+3*pv/r
expected = S.zeros(N)
for i in range(2):
    for j in range(2):
        expected[i,j]=-2*S.diff(p,coords[i])*S.diff(p,coords[j])
expected[2,2]=g[2,2]*L
expected[3,3]=-g[3,3]*L
for i in range(N):
    for j in range(N):
        assert S.simplify(Ric[i,j]-expected[i,j])==0,(i,j,Ric[i,j],expected[i,j])
print('PASS all 25 exact nonlinear Ricci components; linear vacuum iff L(p)=0')
# Exact parallel screen along the null curves with v,x,y,z constant.
assert all(C(i,0,0)==0 for i in range(N))
for j in (2,3,4):
    ej=1/S.sqrt(g[j,j])
    assert all(S.simplify((S.diff(ej,r) if i==j else 0)+C(i,0,j)*ej)==0 for i in range(N))
# R_{i r i r}/g_ii = R^i_{r i r}, for each parallel screen axis.
Tx,Ty,Tz=[R(j,0,j,0) for j in (2,3,4)]
assert S.simplify(Tx+S.diff(p,r,2)+2*pr/r+pr**2)==0
assert S.simplify(Ty-S.diff(p,r,2)-2*pr/r+pr**2)==0
assert Tz==0
assert S.simplify(Tx-Ty+2*(S.diff(p,r,2)+2*pr/r))==0
print('PASS affine radial null ray, parallel orthonormal screen, exact tidal split')
# Gauge test: background R_{a r j r}=0 for every a and fibre j;
# R_{i a j r} is pure trace on the fibre for every a.
# This annihilates the screen tracefree part of Lie_xi R for any smooth xi.
def lower_bg(a,b,c,d):
    return S.simplify(sum(g[a,h]*R(h,b,c,d) for h in range(N)).subs(p,0).doit())
for j in (2,3,4):
    for a in range(N):
        assert lower_bg(a,0,j,0)==0,(a,j)
for a in range(N):
    diag=[lower_bg(i,a,i,0) for i in (2,3,4)]
    assert diag[0]==diag[1]==diag[2],(a,diag)
    for i in (2,3,4):
        for j in (2,3,4):
            if i!=j:
                assert lower_bg(i,a,j,0)==0,(i,a,j)
print('PASS screen tracefree linear tidal tensor is invariant under smooth infinitesimal gauge')
# Fourier p=e^(ikv) h(r); use local x0=r-s (not spatial x).
k=S.symbols('k',real=True,nonzero=True)
h=S.Function('h')(r)
assert S.simplify(L.subs(p,S.exp(S.I*k*v)*h).doit()/S.exp(S.I*k*v)-(f*S.diff(h,r,2)+(S.diff(f,r)+3*f/r+2*S.I*k)*S.diff(h,r)+3*S.I*k*h/r))==0
# Normal form h''+P h'+Q h=0, regular singular at r=s.
P=(S.diff(f,r)+3*f/r+2*S.I*k)/f
Q=3*S.I*k/(r*f)
P0=S.simplify(S.limit((r-s)*P,r,s,dir='+'))
Q0=S.simplify(S.limit((r-s)**2*Q,r,s,dir='+'))
assert P0==1+S.I*k*s and Q0==0
alpha=S.symbols('alpha')
indicial=alpha*(alpha-1)+P0*alpha+Q0
assert S.simplify(indicial-alpha*(alpha+S.I*k*s))==0
bad=-S.I*k*s
coeff=S.simplify(bad*(bad-1))
assert S.simplify(S.expand_complex(coeff*S.conjugate(coeff))-k**2*s**2*(1+k**2*s**2))==0
print('PASS regular-singular indicial roots 0,-i*k*s; nonzero leading tidal coefficient')
# Formal first Frobenius coefficient for either branch, exact after factoring.
u=S.symbols('u',positive=True)
c=S.symbols('c')
for a in (S.Integer(0),bad):
    # h=u^a(1+c*u). Evaluate rescaled equation without complex power expansion.
    h0=1+c*u
    h1=a*h0+u*c
    h2=a*(a-1)*h0+2*a*u*c
    expr=(f.subs(r,s+u)/u)*h2+(S.diff(f,r)+3*f/r+2*S.I*k).subs(r,s+u)*h1+u*(3*S.I*k/r).subs(r,s+u)*h0
    assert S.simplify(S.limit(expr,u,0,dir='+'))==0
    first=S.simplify(S.limit(S.diff(expr,u),u,0,dir='+'))
    cs=S.solve(first,c)
    assert len(cs)==1 and S.simplify(first.subs(c,cs[0]))==0
    print('PASS first Frobenius coefficient',a,cs[0])
print('LIMITS local linear vacuum perturbation, not nonlinear instability or global initial-data theorem')
