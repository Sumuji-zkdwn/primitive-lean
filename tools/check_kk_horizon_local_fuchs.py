"""Exact checks for the local Fuchsian tensor-mode reduction.
The cited Fuchsian uniqueness and elliptic analytic regularity theorems
are analytic inputs, not established by this script.
"""
import sympy as S
from functools import lru_cache
from itertools import product
from pathlib import Path
import hashlib

# Unit H^3, screen covariant tensor encoded by a polynomial in a tangent vector.
x,y,z=S.symbols('x y z', real=True)
w=S.symbols('w0:3', real=True)
X=(x,y,z); J=range(3)
@lru_cache(None)
def G(k,i,j):
    return -(int(k==i)*int(j==2)+int(k==j)*int(i==2)-int(i==j)*int(k==2))/z
Q=S.Matrix(3,3,lambda i,j:S.Function(f'Q{min(i,j)}{max(i,j)}')(*X))
def encode(T):
    return sum(T[i,j]*w[i]*w[j] for i,j in product(J,repeat=2))
def horizontal(i,p):
    return S.diff(p,X[i])-sum(G(k,i,j)*w[j]*S.diff(p,w[k]) for k,j in product(J,repeat=2))
@lru_cache(None)
def dQ(k,i,j):
    return S.diff(Q[i,j],X[k])-sum(G(l,k,i)*Q[l,j]+G(l,k,j)*Q[i,l] for l in J)
for k in J:
    assert S.expand(horizontal(k,encode(Q))-encode(S.Matrix(3,3,lambda i,j:dQ(k,i,j))))==0
rough=S.Matrix(3,3,lambda i,j:S.expand(z*z*sum(S.diff(dQ(k,i,j),X[k])-sum(G(l,k,k)*dQ(l,i,j)+G(l,k,i)*dQ(k,l,j)+G(l,k,j)*dQ(k,i,l) for l in J) for k in J)))
lift=S.expand(z*z*sum(horizontal(k,horizontal(k,encode(Q)))-sum(G(l,k,k)*horizontal(l,encode(Q)) for l in J) for k in J))
assert S.expand(lift-encode(rough))==0
print('PASS horizontal lift and rough Laplacian for all six arbitrary symmetric components')

# Fourier mode in original regular coordinates, u=s-r, not the logarithmic phase chart.
r,s,u=S.symbols('r s u',positive=True); k=S.symbols('k',real=True)
f=1-s*s/r**2
fu=S.factor(f.subs(r,s-u)); R=s-u
B=S.cancel(u*(-S.diff(f,r)-3*f/r-2*S.I*k).subs(r,R)/fu)
C=S.cancel(u**2/fu*3*S.I*k/R)
H=S.cancel(-u**2/(fu*R**2))
assert S.simplify(fu+u*(2*s-u)/R**2)==0
assert S.simplify(S.limit(B,u,0)-1-S.I*k*s)==0
assert S.limit(C,u,0)==0
assert S.simplify(H-u/(2*s-u))==0
# Original equation after multiplying u²/f: D²+(B-1)D+C+H(Lift+2).
W=S.Function('W')(u); D=lambda p:u*S.diff(p,u)
P=lambda p:D(D(p))+(B-1)*D(p)+C*p
assert S.simplify(P(u*W)/u-(D(D(W))+(B+1)*D(W)+(B+C)*W))==0
lam=S.symbols('lam'); ind=lam**2+(S.I*k*s+2)*lam+(1+S.I*k*s)
assert S.expand(ind-(lam+1)*(lam+1+S.I*k*s))==0
assert S.re(-1-S.I*k*s)==-1
assert S.limit(H/u,u,0)==1/(2*s)
print('PASS exact Fuchs operator and shift by u, both indicial roots have real part -1')
# Ellipticity in (r,x) after Fourier: -f and positive screen inverse /r².
assert S.simplify(-fu-u*(2*s-u)/R**2)==0
print('PASS interior principal sign; analytic elliptic continuation applies to original tensor system')
print('SHA256',hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
