"""Exact pure-vacuum 5D open-FRW x S1 example with asymptotic radius freezing.

Hyperbolic H3 metric in upper-half-space coordinates z>0,
ds5^2=-dt^2+(t^2+L^2)*(dx^2+dy^2+dz^2)/z^2
                 +t^2/(t^2+L^2)*dchi^2, t,L>0.
No independent gauge, scalar, flux or matter. The radion variable used in
4D is a definition from the 5D metric, NOT an additional primitive field.
All tensor components and inequalities checked in exact SymPy 1.14.0.
"""
from itertools import product
import sympy as sp

t,z,L=sp.symbols('t z L',positive=True)
x,y,chi=sp.symbols('x y chi',real=True)
a=sp.sqrt(t*t+L*L)
b=t/a
u=a*a

def geometry(diag,coords,include_riemann=False):
    """All Christoffels, all Ricci, optionally nonzero Riemann and K."""
    n=len(diag)
    inverse=[1/v for v in diag]
    gamma={}
    for i,j,k in product(range(n),repeat=3):
        w=(sp.diff(diag[i],coords[j])*int(i==k)
           +sp.diff(diag[i],coords[k])*int(i==j)
           -sp.diff(diag[j],coords[i])*int(j==k))
        if w!=0:
            v=sp.factor(inverse[i]*w/2)
            if v!=0: gamma[i,j,k]=v
    def G(i,j,k): return gamma.get((i,j,k),sp.S.Zero)
    def R(i,j,k,l):
        return sp.factor(sp.diff(G(i,l,j),coords[k])
            -sp.diff(G(i,k,j),coords[l])
            +sum(G(i,k,m)*G(m,l,j)-G(i,l,m)*G(m,k,j)
                 for m in range(n)))
    ric=sp.Matrix(n,n,lambda i,j:sp.factor(
        sum(R(k,i,k,j) for k in range(n))))
    if not include_riemann: return ric,gamma
    nonzero={(i,j,k,l):v for i,j,k,l in product(range(n),repeat=4)
             if (v:=R(i,j,k,l))!=0}
    K=sp.factor(sum((diag[i]*v)**2/
        (diag[i]*diag[j]*diag[k]*diag[l])
        for (i,j,k,l),v in nonzero.items()))
    return ric,gamma,nonzero,K

g5=(-1,u/z**2,u/z**2,u/z**2,b*b)
ric5,G5,riemann5,K5=geometry(g5,(t,x,y,z,chi),include_riemann=True)
assert all(v==0 for v in ric5)
assert sp.factor(K5-72*L**4/(t*t+L*L)**4)==0
assert len(G5)==19 and len(riemann5)==40
print("PASS 25 5D Ricci entries: exactly zero; Christoffels 19")
print("PASS 40 nonzero coordinate Riemann components: K=72L^4/(t^2+L^2)^4")

# Independent warped-FRW equations for k=-1:
# Ric_tt=-3(H'+H²)-(F'+F²), Ric_ii/a²=H'+H(3H+F)-2/a²,
# Ric_55/b²=F'+F(3H+F), H=a'/a, F=b'/b.
H=sp.factor(sp.diff(a,t)/a)
F=sp.factor(sp.diff(b,t)/b)
Theta=3*H+F
rtt=-3*(sp.diff(H,t)+H**2)-(sp.diff(F,t)+F**2)
rsp=sp.diff(H,t)+H*Theta-2/a**2
rchi=sp.diff(F,t)+F*Theta
assert all(sp.simplify(v)==0 for v in (rtt,rsp,rchi))
assert sp.simplify(H*(H+F)-1/a**2)==0
assert sp.simplify(sp.diff(a**2,t,2)-2)==0
assert sp.simplify(sp.diff(sp.diff(a,t)/b,t))==0
assert sp.simplify(sp.diff(a**3*sp.diff(b,t),t))==0
print("PASS separate FRW vacuum equations, Hamiltonian, exact first integrals")

# Reduce *same metric* into 4D Einstein frame: ds5²=b^-1 dsE²+b²dchi²
# and define phi=(sqrt(3)/2)*log b from g55 (NOT independent matter).
gE=(-b,b*u/z**2,b*u/z**2,b*u/z**2)
ricE,_=geometry(gE,(t,x,y,z))
phi_prime=sp.sqrt(3)/2*sp.diff(b,t)/b
for i,j in product(range(4),repeat=2):
    target=2*phi_prime**2 if (i,j)==(0,0) else 0
    assert sp.simplify(ricE[i,j]-target)==0,(i,j)
sqrt_minus_g=b**2*a**3/z**3
assert sp.simplify(sp.diff(sqrt_minus_g*(-1/b)*phi_prime,t))==0
alpha=a*sp.sqrt(b)
dtau_dt=sp.sqrt(b)
acc=sp.simplify(sp.diff(sp.diff(alpha,t)/dtau_dt,t)/dtau_dt/alpha)
assert sp.simplify(acc+F**2/(2*b))==0
assert sp.simplify(acc+L**4/(2*t**3*(t*t+L*L)**sp.Rational(3,2)))==0
assert sp.simplify(sp.diff(b,t)-L*L/a**3)==0
assert sp.limit(b,t,sp.oo)==1
assert sp.limit(sp.diff(b,t),t,sp.oo)==0
assert sp.limit(K5,t,sp.oo)==0
assert sp.limit(K5,t,0,dir='+')==72/L**4
assert sp.limit(b,t,0,dir='+')==0
print("PASS 16 Einstein-frame Ricci entries; □phi=0 and strictly negative acceleration")
print("PASS b(t) increases toward 1 and K stays nonzero for L>0")

# L=0 is exactly the flat Milne x S1 limit, and must not be confused
# with the L>0 curved Ricci-flat spacetime.
assert sp.simplify(K5.subs(L,0))==0
print("PASS distinguish L=0 flat Milne vs L>0 nonflat example")
print("LIMITS S1 collapses toward t=0; no global extension or stabilization proof")
