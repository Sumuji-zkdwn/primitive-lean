"""Algebraic checks for compact exact nonlinear vacuum data and protected patch.
No numerical PDE evolution; geometry/domain-of-dependence proof in companion note.
"""
import sympy as S
from functools import lru_cache
from itertools import product

# Fixed product metric, general symmetric H^3 seed and spatially variable trace.
chi,x,y,z=S.symbols('chi x y z',real=True)
r,l,a,b=S.symbols('r l a b',positive=True)
e=S.symbols('epsilon',real=True)
X=(chi,x,y,z); I=range(4); J=range(1,4)
h=S.diag(l**2,r**2/z**2,r**2/z**2,r**2/z**2); G=h.inv()
T=S.zeros(4)
for i,j in product(J,repeat=2): T[i,j]=S.Function(f'T{min(i,j)}{max(i,j)}')(x,y,z)
d=S.Function('delta')(x,y,z)
K=S.diag((b-2*d)*h[0,0],*[(a+d)*h[i,i] for i in J])+e*T
@lru_cache(None)
def Gamma(i,j,k):
    return S.simplify(sum(G[i,m]*(S.diff(h[m,k],X[j])+S.diff(h[m,j],X[k])-S.diff(h[j,k],X[m]))/2 for m in I))
def tr(A): return S.trace(G*A)
def div(A,j):
    return S.expand(sum(G[i,i]*(S.diff(A[i,j],X[i])-sum(Gamma(m,i,i)*A[m,j]+Gamma(m,i,j)*A[i,m] for m in I)) for i in I))
# General trace and momentum formula (TT seed sets both remaining terms to zero).
assert S.simplify(tr(K)-(3*a+b+d+e*tr(T)))==0
for j in I:
    assert S.simplify(div(K,j)-S.diff(tr(K),X[j])-e*(div(T,j)-S.diff(tr(T),X[j])))==0
Q=S.trace(G*T*G*T)
H=S.expand(-6/r**2+tr(K)**2-S.trace(G*K*G*K))
expected=-6/r**2+6*a*(a+b)+6*(b*d-d**2)-e**2*Q+2*e*(2*a+b)*tr(T)+e**2*tr(T)**2
assert S.simplify(H-expected)==0
print('PASS general momentum and Hamiltonian identities on the product',flush=True)
# Check the background scalar constraint and exact correction with rationalized root.
beta=S.symbols('beta',positive=True)
f=1-beta/r**2
assert S.simplify(6*(f/r**2+S.diff(f,r)/(2*r))-6/r**2)==0
q=S.symbols('Q',nonnegative=True)
bnew=S.sqrt(b**2-S.Rational(2,3)*e**2*q)
dnew=(b-bnew)/2
assert S.simplify(6*(b*dnew-dnew**2)-e**2*q)==0
assert S.simplify((dnew*(b+bnew))-e**2*q/3)==0
assert S.simplify(dnew.subs(e,0))==0
assert S.simplify(S.diff(dnew,e).subs(e,0))==0
assert S.simplify(S.diff(dnew,e,2).subs(e,0)-q/(3*b))==0
print('PASS exact root, smooth small-amplitude correction, background constraint',flush=True)
# Inside ball T has eigenvalues (0,1,-1,0), norm squared 2; match #277 constants.
D,N,P,B=S.symbols('D N P B',positive=True)
w0=S.symbols('w0',real=True)
innerdelta=dnew.subs(q,2); innerb=b-2*innerdelta
assert S.simplify(innerb**2+S.Rational(4,3)*e**2-b**2)==0
assert S.simplify(2*(a+innerdelta)+innerb-(2*a+b))==0
# D0=N*b equals beta for original r0 slice, N=r^3 sqrt(f).
assert S.simplify(r**3*S.sqrt(f)*S.diff(f,r)/(2*S.sqrt(f))-beta)==0
# w first integral at initial slice: Hamiltonian fixes it; unchanged w' and w.
assert S.expand((N*(2*a+b))**2-(N*b)**2-4*N**2*a*(a+b))==0
assert S.simplify((r**3*S.sqrt(f)/r)**2-r**4*f)==0
print('PASS exact interior constants: D unchanged, anisotropy P=N epsilon',flush=True)
# w integration with q=q0 exp(D tau); local initial values and ODE first integral.
v=S.symbols('v',positive=True)
E=D*v/(1-v**2); wprime=D*(1+v**2)/(1-v**2)
assert S.simplify(D*v*S.diff(wprime,v)-4*E**2)==0
assert S.simplify(wprime**2-4*E**2-D**2)==0
v0,t=S.symbols('v0 t',real=True)
# algebraic ratio E(t)/[E(0) exp(D t)]; compare for t<=0, 0<v0<1 by hand.
assert S.simplify(E.subs(v,v0*S.exp(D*t))/(E.subs(v,v0)*S.exp(D*t))-(1-v0**2)/(1-v0**2*S.exp(2*D*t)))==0
print('PASS exact homogeneous evolution and exponential causal-speed bound factor',flush=True)
# Kasner coefficient identities, including strict positivity via z exponent.
M=(3*D-B)/2
ks=[B/M,((D-B)/2+P)/M,((D-B)/2-P)/M,(D-B)/(2*M)]
assert S.simplify(sum(ks)-1)==0
assert S.simplify((sum(k*k for k in ks)-1)*M**2-(-3*D**2+3*B**2+4*P**2)/2)==0
assert S.simplify(ks[-1]*(1-ks[-1])-2*D*(D-B)/(3*D-B)**2)==0
# D=beta, B^2=D^2-4P^2/3 => B<D for nonzero P, and D>|P|.
# All inequalities and finite-propagation integration are proved in companion note.
print('PASS Kasner curvature coefficient algebra',flush=True)
print('LIMIT: compact exact data + analytic local development; not global inextendibility or conserved gravitational energy',flush=True)
