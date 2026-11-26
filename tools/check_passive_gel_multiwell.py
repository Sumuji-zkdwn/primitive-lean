#!/usr/bin/env python3
"""Independent audit of PR #183's passive-gel no-go under multiwell W.

No network, GitHub writes or repository modifications.
Requires numpy, scipy, sympy. Run: python -B tools/check_passive_gel_multiwell.py
"""
from itertools import product
from math import comb
import numpy as np
import sympy as sp
from scipy.integrate import solve_ivp

q = sp.symbols('q', real=True)
W = q**2 * (q**2 - 1)**2
dW = sp.factor(sp.diff(W, q))
ddW = sp.factor(sp.diff(W, q, 2))
assert sp.factor(dW - 2*q*(q*q-1)*(3*q*q-1)) == 0
assert {u: sp.simplify(ddW.subs(q,u)) for u in (0, 1, -1)} == {0:2,1:8,-1:8}
assert sp.simplify(ddW.subs(q, sp.sqrt(3)/3)) == -sp.Rational(8,3)
assert sp.simplify(W.subs(q,sp.sqrt(3)/3)) == sp.Rational(4,27)


def path_incidence(n):
    arr = np.zeros((n-1,n), dtype=float)
    for i in range(n-1):
        arr[i,i] = -1
        arr[i,i+1] = 1
    return arr

B3 = sp.Matrix([[-1,1,0],[0,-1,1]])
X = sp.Matrix(sp.symbols('x0:3', real=True))
H = sp.Matrix(sp.symbols('h0:2', real=True))
V = sp.Matrix(sp.symbols('v0:3', real=True))
b,kappa,gamma,rho = sp.symbols('b kappa gamma rho', positive=True)
eps = B3*X
delta = eps-H
g = delta.applyfunc(lambda d: b*d + kappa*d**3)
E = rho*V.dot(V)/2 + sum(W.subs(q,e) for e in eps) + b*delta.dot(delta)/2 + kappa*sum(d**4 for d in delta)/4
sigma = sp.Matrix([dW.subs(q,e) for e in eps]) + g
Fv = -B3.T*sigma/rho
Fh = gamma*g
EDot = (sp.Matrix([sp.diff(E,z) for z in X]).dot(V) +
        sp.Matrix([sp.diff(E,z) for z in V]).dot(Fv) +
        sp.Matrix([sp.diff(E,z) for z in H]).dot(Fh))
assert sp.expand(EDot + gamma*g.dot(g)) == 0
sol = {X[0]:0,X[1]:1,X[2]:0,H[0]:1,H[1]:-1,V[0]:0,V[1]:0,V[2]:0}
assert sp.simplify(E.subs(sol)) == 0
assert all(sp.simplify(sp.diff(E,z).subs(sol)) == 0 for z in list(X)+list(H)+list(V))
Erel = sum(W.subs(q,e) for e in eps)
Hred = sp.simplify(sp.hessian(Erel, X).subs(sol))
assert Hred == 8*(B3.T*B3)
assert Hred.eigenvals() == {sp.Integer(0):1, sp.Integer(8):1,sp.Integer(24):1}
Hfull = sp.hessian(E, list(X)+list(H)).subs(sol).subs({b:1,kappa:8})
assert Hfull.eigenvals() == {sp.Integer(0):1, 5-sp.sqrt(17):1,5+sp.sqrt(17):1,14-2*sp.sqrt(43):1,14+2*sp.sqrt(43):1}
print('DERIVATIVES dW =', dW, '; W\'\' =', ddW)
print('3-node: E=0, grad E=0, reduced Hessian=',list(Hred.tolist()), 'eig=',sorted(Hred.eigenvals(), key=float))
print('3-node: full static (x,h) Hessian at b=1 eig=',sorted(Hfull.eigenvals(), key=float))
print('Dissipation identity: E_dot = -gamma * sum g_e^2 (symbolically verified)')


def central_trinomial(m):
    return sum(comb(m,k)*comb(m-k,k) for k in range(m//2+1))


def weighted_bump_hessian(n):
    B=path_incidence(n)
    x=np.zeros(n)
    x[1]=1.0
    eps=B@x
    weights=30*eps**4-24*eps**2+2
    Hess=B.T@np.diag(weights)@B
    eigen=np.linalg.eigvalsh(Hess)
    assert abs(eigen[0]) < 1e-11 and min(eigen[1:])>0
    return eigen

print('n | path ground states | cycle ground states | complete ground states | bump Hessian spectral gap | largest eigen')
for n in range(4,9):
    eigen = weighted_bump_hessian(n)
    print(f'{n} | {3**(n-1):>6} | {central_trinomial(n):>6} | {2**n-1:>6} | {eigen[1]:.9f} | {eigen[-1]:.9f}')

# Full independent enumeration of cube (8 vertices, 12 edges). Pin x[0]=0.
nodes = list(product((0,1), repeat=3))
idx = {node:i for i,node in enumerate(nodes)}
edges=[]
for i,node in enumerate(nodes):
    for j in range(3):
        if node[j] == 0:
            nbr=list(node);nbr[j]=1
            edges.append((i,idx[tuple(nbr)]))
dist = [sum(t) for t in nodes]
count=0
for vals in product(*(range(-d,d+1) for d in dist[1:])):
    xs=(0,)+vals
    if all(abs(xs[i]-xs[j])<=1 for i,j in edges):
        count+=1
print(f'8-site cube: edges={len(edges)}, exact distinct ground states modulo translation={count}')
# Cross-check using a spanning tree: 3^(8-1) independent edge increments.
parent={0:None}
from collections import deque
que=deque([0])
adj={i:[] for i in range(8)}
for i,j in edges:
    adj[i].append(j);adj[j].append(i)
while que:
    i=que.popleft()
    for j in adj[i]:
        if j not in parent:
            parent[j]=i;que.append(j)
order=[i for i in parent if i!=0]
tree_count=0
for increments in product((-1,0,1),repeat=7):
    height={0:0}
    for i,step in zip(order,increments):
        height[i]=height[parent[i]]+step
    if all(abs(height[i]-height[j])<=1 for i,j in edges):
        tree_count+=1
assert tree_count==count
Bc=np.zeros((len(edges),8))
for r,(i,j) in enumerate(edges):
    Bc[r,i]=-1;Bc[r,j]=1
xb=np.zeros(8);xb[0]=1
weights=30*(Bc@xb)**4-24*(Bc@xb)**2+2
cubeeig=np.linalg.eigvalsh(Bc.T@np.diag(weights)@Bc)
print('8-site cube bump Hessian: gap=',round(cubeeig[1],9),'largest=',round(cubeeig[-1],9),'one zero=',abs(cubeeig[0])<1e-10)

# Full linearized dynamics includes a neutral center-of-mass drift mode.
Bb=path_incidence(3)
K=np.diag([8.,8.]);ident=np.eye(3)
Alin=np.block([[np.zeros((3,3)),ident,np.zeros((3,2))],
              [-Bb.T@(K+np.eye(2))@Bb,np.zeros((3,3)),Bb.T],
              [Bb,np.zeros((2,3)),-np.eye(2)]])
spectrum=np.linalg.eigvals(Alin)
assert sum(abs(z)<1e-7 for z in spectrum)==2
assert all(z.real<0 for z in spectrum if abs(z)>=1e-7)
print('3-node linearized dynamics: nonneutral eigenvalues=', [complex(round(z.real,8),round(z.imag,8)) for z in spectrum if abs(z)>=1e-7], '2 neutral algebraic zeros')

# A concrete positive quadratic perturbation U_a = W + a*eps**2/2.
a=sp.symbols('a',nonnegative=True)
U=W+a*q*q/2
splus_sq=(sp.Integer(2)+sp.sqrt(1-sp.Rational(3,2)*a))/3
for aa in (sp.Rational(1,10),sp.Rational(1,2)):
    ss=sp.sqrt(splus_sq.subs(a,aa))
    U2=sp.simplify(sp.diff(U,q,2).subs({q:ss,a:aa}))
    Ub=sp.simplify(U.subs({q:ss,a:aa}))
    assert U2>0 and Ub>0
    print(f'Quadratic a={aa}: stable bump strain s+={float(ss):.9f}, U(s+)={float(Ub):.9f}, Wtotal(3-chain)={float(2*Ub):.9f}, U\'\'(s+)={float(U2):.9f}')
assert sp.simplify(sp.diff(U,q).subs(a,sp.Rational(2,3)) - 6*q*(q*q-sp.Rational(2,3))**2) == 0
print('Quadratic threshold a*=2/3: nonzero minimum branch disappears; at threshold nonzero stationary point is not extremum')

# Relative stability, no common-mode momentum: nonlinear relaxation about (0,1,0).
def numeric_perturb(kappa_val):
    B=path_incidence(3)
    xstar=np.array([0.,1.,0.])
    hstar=B@xstar
    x0=xstar+0.05*np.array([1.,-2.,1.])
    init=np.r_[x0,np.zeros(3),hstar]
    def rhs(t, state):
        x=state[:3];v=state[3:6];h=state[6:]
        e=B@x;d=e-h
        sigma=(6*e**5-8*e**3+2*e)+d+kappa_val*d**3
        return np.r_[v,-B.T@sigma,d+kappa_val*d**3]
    def energy(state):
        x=state[:3];v=state[3:6];h=state[6:]
        e=B@x;d=e-h
        return .5*np.dot(v,v)+np.sum(e*e*(e*e-1)**2)+.5*np.dot(d,d)+kappa_val*.25*np.sum(d**4)
    sol=solve_ivp(rhs,(0,240),init,method='DOP853',rtol=1e-10,atol=1e-12,max_step=.09,t_eval=np.linspace(0,240,1201))
    assert sol.success,sol.message
    en=np.array([energy(sol.y[:,j]) for j in range(sol.y.shape[1])])
    assert np.max(np.diff(en))<5e-12
    shape_error=np.linalg.norm(B@sol.y[:3,-1]-hstar)
    assert shape_error<1e-6
    print(f'Nonlinear local stability check kappa={kappa_val:g}: E0={en[0]:.9g} E240={en[-1]:.6g} final relative strain error={shape_error:.3g}')
for kap in (0,8):
    numeric_perturb(kap)
print('ALL INDEPENDENT AUDIT TESTS PASSED')
