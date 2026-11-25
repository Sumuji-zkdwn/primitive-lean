"""Exact algebraic checks for finite-support linear vacuum initial data.
The PDE existence, finite propagation and Frobenius theorems are analytic inputs,
not established by this script. See companion research note.
"""
import sympy as S
from itertools import product
x,y,z=S.symbols('x y z', real=True); X=(x,y,z)
a,b,c=S.symbols('a b c', real=True); xi=S.Matrix([a,b,c]); d=(xi.T*xi)[0]
P=d*S.eye(3)-xi*xi.T
A=S.Matrix(3,3,lambda i,j:S.Symbol(f'a{min(i,j)}{max(i,j)}'))
TT=P*A*P-P*S.trace(P*A)/2
assert all(S.expand(e)==0 for e in TT*xi)
assert S.expand(S.trace(TT))==0
assert S.simplify(TT-TT.T)==S.zeros(3)
D=S.diag(1,-1,0)
assert S.simplify((P*D*P-P*S.trace(P*D)/2).subs({a:0,b:0})-c**4*D)==S.zeros(3)
assert S.diff(z*S.log(z)/2,z,4)==z**-3
print('PASS TT differential symbol, local shear reproduction')
# Hyperbolic Christoffel and generic conformal TT transform
I=range(3)
def G(i,j,k):
    return -(int(i==j)*int(k==2)+int(i==k)*int(j==2)-int(j==k)*int(i==2))/z
T=S.Matrix(3,3,lambda i,j:S.Function(f't{min(i,j)}{max(i,j)}')(*X))
W=z*T
for j in I:
    div=S.expand(z**2*sum(S.diff(W[i,j],X[i])-sum(G(k,i,i)*W[k,j]+G(k,i,j)*W[i,k] for k in I) for i in I))
    expected=z**3*sum(S.diff(T[i,j],X[i]) for i in I)+z**2*int(j==2)*S.trace(T)
    assert S.simplify(div-expected)==0,(j,div-expected)
assert S.expand(S.trace(z**2*W)-z**3*S.trace(T))==0
print('PASS covariant TT conformal transform (all 3 divergence components)')
# Rough Laplacian on the homogeneous shear S0=z^-2 diag(1,-1,0)
U=z**-2*D
nabla={ (k,i,j):S.simplify(S.diff(U[i,j],X[k])-sum(G(l,k,i)*U[l,j]+G(l,k,j)*U[i,l] for l in I)) for k,i,j in product(I,repeat=3)}
rough=S.Matrix(3,3,lambda i,j:S.simplify(z**2*sum(S.diff(nabla[k,i,j],X[k])-sum(G(l,k,k)*nabla[l,i,j]+G(l,k,i)*nabla[k,l,j]+G(l,k,j)*nabla[k,i,l] for l in I) for k in I)))
assert rough==-2*U
assert all(S.simplify(sum(nabla[i,i,j] for i in I))==0 for j in I)
print('PASS homogeneous shear is hyperbolic TT with rough eigenvalue -2')
# Base causal radius and finite initial measure.
r,s,k=S.symbols('r s k',positive=True); f=1-s**2/r**2
assert S.simplify(S.diff(S.acosh(r/s),r)-1/S.sqrt(r*r-s*s))==0
assert S.limit(S.acosh(r/s),r,s,dir='+')==0
base=S.Matrix([[-1/f,0],[0,f]])
assert S.simplify(base.det())==-1
assert S.simplify((r**3*S.sqrt(f))**2-f*r**6)==0
# Wave normal-form indicial coefficients and nonzero amplitude.
P0=S.simplify(S.limit((r-s)*(S.diff(f,r)+3*f/r+2*S.I*k)/f,r,s,dir='+'))
Q0=S.simplify(S.limit((r-s)**2*3*S.I*k/(r*f),r,s,dir='+'))
assert P0==1+S.I*k*s and Q0==0
alpha=-S.I*k*s
assert S.simplify(S.expand_complex(alpha*(alpha-1)*S.conjugate(alpha*(alpha-1)))-k*k*s*s*(1+k*k*s*s))==0
print('PASS finite hyperbolic domain radius and irregular-mode tidal coefficient')
print('LIMIT: smooth compact-support linearized data, not exact nonlinear constraint data or a conserved gravitational energy')
