"""Exact Taub-NUT cutoff norms, not a global differential-geometric proof."""
import sympy as s
r,R,a=s.symbols('r R a',positive=True)
theta=s.symbols('theta', real=True)
H=1+a/r
# order r, theta, phi, psi; regular chart away from axes
G=s.diag(H,H*r*r,H*r*r*s.sin(theta)**2,0)
v=s.Matrix([0,0,a*s.cos(theta),1]); G+=v*v.T/H
assert s.simplify(G.det()-H**2*r**4*s.sin(theta)**2)==0
# 0<theta<pi: positive volume density
D=H*r*r*s.sin(theta)
# fibre integration in Hopf Euler coordinates: length 4pi*a
factor=2*s.pi*4*s.pi*a

def integ(expr):
    return s.simplify(factor*s.integrate(s.integrate(s.expand(expr*D),(theta,0,s.pi)),(r,0,R)))
vol=integ(1); fibre=integ(G[3,3]); axis=integ(G[2,2]); lower=integ(H*r*r*s.sin(theta)**2)
assert s.simplify(vol-16*s.pi**2*a*(R**3/3+a*R**2/2))==0
assert s.simplify(fibre-16*s.pi**2*a*R**3/3)==0
assert s.simplify(lower-32*s.pi**2*a/3*(R**5/5+a*R**4/2+a*a*R**3/3))==0
assert s.simplify(axis-lower-a*a*fibre/3)==0
assert s.limit(vol,R,s.oo)==s.oo and s.limit(fibre,R,s.oo)==s.oo and s.limit(axis,R,s.oo)==s.oo
# Cutoff Young inequality algebra (for nonnegative x,y: 2xy <= x²/2 + 2y²)
x,y=s.symbols('x y',real=True)
assert s.expand(x*x/2+2*y*y-2*x*y-(x-2*y)**2/2)==0
print('PASS determinant; cutoff Young identity; exact volume and fibre/axis norms; all divergences')
for name,value in [('volume',vol),('fibre',fibre),('axis lower',lower),('axis full',axis)]:print(name, '=',s.factor(value))
# Dropping completeness: radial spacelike Kasner vacuum with 4D Minkowski factor.
from itertools import product, combinations
coords=(r,*s.symbols('t x y z psi', real=True)); N=len(coords)
p=s.Rational(2,5); q=s.Rational(-3,5)
assert 4*p+q==1 and 4*p*p+q*q==1
G=s.diag(1,-r**(2*p),r**(2*p),r**(2*p),r**(2*p),r**(2*q)); inv=G.inv()
I=range(N)
Gamma={(i,j,k):s.simplify(sum(inv[i,l]*(s.diff(G[l,k],coords[j])+s.diff(G[l,j],coords[k])-s.diff(G[j,k],coords[l]))/2 for l in I)) for i,j,k in product(I,repeat=3)}
Rm={(i,j,k,l):s.simplify(s.diff(Gamma[i,l,j],coords[k])-s.diff(Gamma[i,k,j],coords[l])+sum(Gamma[i,k,m]*Gamma[m,l,j]-Gamma[i,l,m]*Gamma[m,k,j] for m in I)) for i,j,k,l in product(I,repeat=4)}
Ric=s.Matrix(N,N,lambda j,l:s.simplify(sum(Rm[i,j,i,l] for i in I)))
assert Ric==s.zeros(N)
K=s.simplify(sum(G[i,i]*inv[j,j]*inv[k,k]*inv[l,l]*v*v for (i,j,k,l),v in Rm.items() if v!=0))
assert s.simplify(K-768/(125*r**4))==0, K
exps=[p]*4+[q]
assert s.simplify(K-4*(sum((u*(u-1))**2 for u in exps)+sum((u*v)**2 for u,v in combinations(exps,2)))/r**4)==0
# Direct internal weighted equations on the incomplete two-dimensional base.
g=s.diag(1,r**(2*q)); f=-4*p*s.log(r)
RicK=s.diag(-q*(q-1)/r**2,-q*(q-1)*r**(2*q-2))
Hess=s.diag(s.diff(f,r,2),q*r**(2*q-1)*s.diff(f,r))
df=s.Matrix([s.diff(f,r),0])
assert (RicK+Hess-df*df.T/4).applyfunc(s.simplify)==s.zeros(2)
assert s.simplify(s.trace(g.inv()*Hess)-(df.T*g.inv()*df)[0])==0
assert s.limit(K,r,0,dir='+')==s.oo
print('PASS incomplete 6D metric: all 36 Ricci components zero; Kretschmann =',K,'; weighted residuals zero')
