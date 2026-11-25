"""Exact test of unrestricted-time homogeneous 5D vacuum circle cosmology.

Only 5D Einstein metric; no independent matter, gauge field or flux.
The topological/ODE uniqueness argument is written in the research note,
not asserted to have been machine-formalized by this finite oracle.
"""
import sympy as s

t = s.symbols('t', real=True)
a, b = s.Function('a')(t), s.Function('b')(t)


def geom(diagonal):
    """Christoffels and all Ricci components from diagonal metric of t only."""
    n = len(diagonal)
    gamma = {}
    gamma[0, 0, 0] = s.diff(diagonal[0], t)/(2*diagonal[0])
    for i in range(1, n):
        gamma[0, i, i] = -s.diff(diagonal[i], t)/(2*diagonal[0])
        gamma[i, 0, i] = gamma[i, i, 0] = s.diff(diagonal[i], t)/(2*diagonal[i])
    def G(i, j, k):
        return gamma.get((i,j,k), s.S.Zero)
    def dd(expr, index):
        return s.diff(expr, t) if index == 0 else s.S.Zero
    def R(i,j,k,l):
        return dd(G(i,l,j), k) - dd(G(i,k,j), l) + sum(
            G(i,k,m)*G(m,l,j) - G(i,l,m)*G(m,k,j)
            for m in range(n))
    ric = s.Matrix(n,n,lambda i,j: s.factor(sum(R(k,i,k,j) for k in range(n))))
    return ric

ric = geom((-1, a**2, a**2, a**2, b**2))
H, F = s.diff(a,t)/a, s.diff(b,t)/b
Theta = 3*H+F
assert all(s.simplify(ric[i,j]) == 0 for i in range(5) for j in range(5) if i != j)
assert s.simplify(ric[0,0]+3*s.diff(a,t,2)/a+s.diff(b,t,2)/b)==0
assert s.simplify(ric[1,1]/a**2 - (s.diff(H,t)+H*Theta))==0
assert s.simplify(ric[4,4]/b**2 - (s.diff(F,t)+F*Theta))==0
constraint = s.factor(ric[0,0]+3*ric[1,1]/a**2+ric[4,4]/b**2)
assert s.simplify(constraint-6*H*(H+F))==0
V=a**3*b
assert s.simplify(s.diff(V,t,2)/V - (3*ric[1,1]/a**2+ric[4,4]/b**2))==0
assert s.simplify(s.diff(V*H,t) - V*ric[1,1]/a**2)==0
assert s.simplify(s.diff(V*F,t) - V*ric[4,4]/b**2)==0
print('PASS general a(t),b(t): all 25 Ricci entries, Hamiltonian and volume first-integral identities')

# Full expanding branch, arbitrary positive constants; time-shifted Kasner.
c,d,A,B=s.symbols('c d A B', positive=True)
u=c*t+d
as_, bs_=A*s.sqrt(u), B/s.sqrt(u)
def check(metric, n):
    out=geom(metric)
    assert all(s.simplify(out[i,j])==0 for i in range(n) for j in range(n)),out
check((-1,as_**2,as_**2,as_**2,bs_**2),5)
assert s.simplify(as_*bs_-A*B)==0
assert s.simplify(s.diff(as_**2,t,2))==0
assert s.simplify(s.diff(bs_,t))!=0
assert s.limit(bs_,t,s.oo)==0
print('PASS all 25 Ricci entries: a=A sqrt(c*t+d), b=B/sqrt(c*t+d), b -> 0')

# No external expansion (a constant), possible linear-radius Milne branch.
k, ell, m=s.symbols('k ell m', positive=True)
check((-1,k**2,k**2,k**2,(ell*t+m)**2),5)
check((-1,k**2,k**2,k**2,m**2),5)
print('PASS all 25 Ricci entries: static and Milne-circle branches')

# Exact Einstein-frame check. The radion phi is a definition from g_55.
metricE=(-bs_, *((bs_*as_**2,)*3))
ricE=geom(metricE)
phi_prime = s.sqrt(3)*s.diff(bs_,t)/(2*bs_)
assert s.simplify(phi_prime + s.sqrt(3)*c/(4*u))==0
for i in range(4):
    for j in range(4):
        rhs=2*phi_prime**2 if i==j==0 else 0
        assert s.simplify(ricE[i,j]-rhs)==0,(i,j)
sqrt_abs_det = bs_**2*as_**3
assert s.simplify(s.diff(sqrt_abs_det*phi_prime/metricE[0],t))==0
alpha = as_*s.sqrt(bs_)
dtau_dt=s.sqrt(bs_)
H_E=s.simplify(s.diff(alpha,t)/alpha/dtau_dt)
alpha_ddot_tau=s.simplify(s.diff(s.diff(alpha,t)/dtau_dt,t)/dtau_dt)
assert s.simplify(H_E-(c/(4*s.sqrt(B)*u**s.Rational(3,4))))==0
assert s.simplify(alpha_ddot_tau/alpha+H**2/(2*b)).subs({a:as_,b:bs_,s.diff(a,t):s.diff(as_,t)})==0
assert s.simplify(alpha_ddot_tau/alpha + c**2/(8*B*u**s.Rational(3,2)))==0
assert s.simplify(3*H_E**2 - (phi_prime/dtau_dt)**2)==0
print('PASS Einstein frame: Ric_E=2 grad phi^2, box phi=0, H^2 constraint, strictly negative acceleration')
print('PASS conclusion: expanding flat 3-space entails shrinking circle; no finite positive stabilized radius')
