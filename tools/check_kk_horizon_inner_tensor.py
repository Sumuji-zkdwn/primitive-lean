"""Exact identities for the interior tensor-sector spectral uniqueness lemma.
Analytic spectral theorem, estimates and ODE uniqueness are separate arguments.
"""
import sympy as S
from pathlib import Path
import hashlib

t,s=S.symbols('t s',positive=True)
chi=S.symbols('chi',real=True)
r=S.sqrt(s*s-t*t)
f=-t*t/r**2
p=S.Function('p')(t,chi)
Dr=lambda h: -r/t*S.diff(h,t)-S.diff(h,chi)/f
L=f*Dr(Dr(p))+(Dr(f)+3*f/r)*Dr(p)+2*Dr(S.diff(p,chi))+3*S.diff(p,chi)/r
expected=-(S.diff(p,t,2)+(1/t-2*t/r**2)*S.diff(p,t)-r**2/t**2*S.diff(p,chi,2))
assert S.simplify(L-expected)==0
# Include the screen operator C=(Delta_gamma+2)Q, treated symbolically.
C=S.symbols('C')
De=lambda h:t*S.diff(h,t)
a=r*r; b=t*t/r**2
assert S.simplify(-t*t*(L-C/r**2)-(De(De(p))-2*b*De(p)-a*S.diff(p,chi,2)+b*C))==0
assert S.simplify(De(a)+2*b*a)==0
assert S.simplify(De(b)-2*(1+b)*b)==0
assert S.simplify(Dr(r)-1)==0
assert S.simplify(t*t/(s+r)-(s-r))==0
print('PASS exact interior master operator, logarithmic time coefficients, horizon scale')
# P_eta at fixed chi equals -(t²/r) Q_r + r Q_v.
# Verify coordinate speed dr*/dr=1/f and d_eta r*=r.
rr=S.symbols('rr',positive=True)
rs=rr+s*S.log((s-rr)/(s+rr))/2
assert S.simplify(S.diff(rs,rr)-1/(1-s*s/rr**2))==0
assert S.simplify(De(rs.subs(rr,r))-r)==0
print('PASS regular-coordinate derivative transformation')
# Fourier k and rough-Laplacian eigenvalue lambda in a bounded spectral band.
k,lam=S.symbols('k lam',real=True)
c=1+s*s*k*k
rhs=a*(-k*k)+b*(lam-2)
assert S.expand(rhs+c-(1+t*t*k*k+b*(lam-2)))==0
# E=(y²+c p²)/2; derivative along P''=2b P'+rhs P.
y,x=S.symbols('y x',real=True)
E=(y*y+c*x*x)/2
Eprime=S.expand(y*(2*b*y+rhs*x)+c*x*y)
assert S.simplify(Eprime-(2*b*y*y+(rhs+c)*x*y))==0
# 2 sqrt(c) |xy| <= y²+c x²; 4b E >= 2b y².
cc,bb=S.symbols('cc bb',nonnegative=True)
assert S.expand(y*y+cc**2*x*x-2*cc*x*y-(y-cc*x)**2)==0
assert S.expand(y*y+cc**2*x*x+2*cc*x*y-(y+cc*x)**2)==0
assert S.expand(4*bb*(y*y+cc**2*x*x)/2-2*bb*y*y-2*bb*cc**2*x*x)==0
print('PASS bounded-spectral-band energy identities and Cauchy inequality')
# Principal sign: in logarithmic variables, the CTC-side screen term is +b Delta,
# unlike the exterior -b Delta. A radial evolution energy with all spatial
# derivative squares positive cannot cancel both spatial fluxes by the same sign.
print('LIMIT: fixed exact background, linear TT sector, global L2 horizon regularity; not general smooth nonlinear two-sided rigidity')
print('SHA256',hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
