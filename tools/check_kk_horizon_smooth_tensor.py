"""Exact algebra oracle for localized tensor-sector smooth horizon uniqueness.
The energy integration, smooth estimates and PDE theorem are analytic arguments.
"""
import sympy as S
from pathlib import Path
import hashlib

t,s=S.symbols('t s',positive=True)
chi=S.symbols('chi',real=True)
r=S.sqrt(s*s+t*t); f=t*t/r**2
p=S.Function('p')(t,chi)
# r derivative at fixed EF v; v=chi+r*(r), r*'=1/f.
def Dr(expr):
    return r/t*S.diff(expr,t)-S.diff(expr,chi)/f
fr=Dr(f)
L=f*Dr(Dr(p))+(fr+3*f/r)*Dr(p)+2*Dr(S.diff(p,chi))+3*S.diff(p,chi)/r
expected=S.diff(p,t,2)+(1/t+2*t/r**2)*S.diff(p,t)-S.diff(p,chi,2)/f
assert S.simplify(L-expected)==0
print('PASS exact EF-to-diagonal tensor master operator')
assert S.simplify(t*S.diff(r,t)-t*t/r)==0
assert S.simplify(t*S.diff(r,t)/f-r)==0
# eta=log(t/s), d_eta=t d_t. Check multiplication of operator by t^2.
a=r*r; b=t*t/r**2; d=2*b
De=lambda expr:t*S.diff(expr,t)
assert S.simplify(t*t*expected-(De(De(p))+d*De(p)-a*S.diff(p,chi,2)))==0
assert S.simplify(De(a)-2*b*a)==0
assert S.simplify(De(b)-2*(1-b)*b)==0
assert S.simplify(De(S.asinh(t/s))-S.sqrt(b))==0
assert S.simplify((r-s)*(r+s)-t*t)==0
print('PASS logarithmic time coefficients, finite screen propagation radius and horizon scale')
# Formal scalar inner-product algebra for a component in an orthonormal fiber.
# In the tensor case sum over components, and replace products by contractions.
a,b,x,y,z,g=S.symbols('a b x y z g',real=True)
e=(x*x+a*y*y+b*g*g+z*z)/2
source=-2*b*x*x+b*a*y*y+(1-b)*b*g*g+(1+2*b)*x*z
sos=(1+2*b)*(x-z)**2/2+(1+b)*x*x+(1-b)*z*z+(S.Rational(3,2)-b)*a*y*y+(S.Rational(1,2)+b)*b*g*g
assert S.expand(3*e-source-sos)==0
# The full flux through moving ball has normal component n and tangent norm j.
c,n,j=S.symbols('c n j',real=True)
eb=(x*x+a*y*y+c*c*(n*n+j*j)+z*z)/2
assert S.expand(c*eb-c*c*x*n-c*((x-c*n)**2+a*y*y+c*c*j*j+z*z)/2)==0
print('PASS energy growth and nonpositive moving-boundary flux square certificates')
print('LIMIT: linear tensor sector on exact background exterior; not a nonlinear metric uniqueness theorem')
print('SHA256',hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
