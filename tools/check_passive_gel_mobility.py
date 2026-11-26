#!/usr/bin/env python3
"""Independent follow-up audit for primitive-lean PR #183, 2026-11-23.

Finite graphs with nonconvex edge potential W(s)=s^2(s^2-1)^2.

* Algebraic classification of every stationary point for a 4-site path with
  fixed endpoint displacements x0=x3=0 (two free interior coordinates u,v).
* Exact mountain-pass barrier to move a 1-site peak one lattice site.
* Exact fixed-end 3-site positive-energy metastability formula.
* Example of dissipative finite hopping and nonhopping under impulses.

No network or GitHub writes. Requires sympy, numpy, scipy.
"""
from __future__ import annotations

from itertools import permutations
from math import comb, sqrt
import numpy as np
import sympy as sp
from scipy.integrate import solve_ivp

# Polynomial edge energy and algebraic first/second derivatives.
z = sp.symbols('z', real=True)
W = z**2 * (z**2 - 1)**2
Wp = sp.factor(sp.diff(W, z))
Wpp = sp.factor(sp.diff(Wp, z))
assert sp.expand(Wp - (6*z**5 - 8*z**3 + 2*z)) == 0
w = sp.lambdify(z, W, 'numpy')
wp = sp.lambdify(z, Wp, 'numpy')

# Four vertices: (x0,x1,x2,x3)=(0,u,v,0).
# Edge strains (u, v-u, -v), and W is even.
u, v = sp.symbols('u v', real=True)
F = sp.expand(W.subs(z,u) + W.subs(z,v-u) + W.subs(z,-v))
Fu, Fv = sp.diff(F,u), sp.diff(F,v)
H = sp.hessian(F,(u,v))
Fnp = sp.lambdify((u,v),F,'numpy')

# Elementary classification lemma: for e1+e2+e3=0, let p be the sum of
# pairwise products and q the triple product, hence e_i^3+p*e_i-q=0.
# W'(e_i) modulo that cubic is a quadratic. If three e_i are distinct
# and W'(e_i) is the same, the coefficients of z,z^2 must vanish.
p, q = sp.symbols('p q', real=True)
rem = sp.rem(Wp, z**3 + p*z - q,z)
expected = (6*p*p+8*p+2)*z + 6*q*z*z -(6*p+8)*q
assert sp.expand(rem - expected)==0
assert sp.expand(6*p*p+8*p+2-2*(p+1)*(3*p+1))==0
# All-distinct stationary: q=0, p=-1 or -1/3, so permutations of
# (1,-1,0) or (1/sqrt(3),-1/sqrt(3),0).

# Two equal: (r,r,-2r), stationary iff r=0 or 33*r^4-12*r^2+1=0.
r = sp.symbols('r',real=True)
assert sp.factor(Wp.subs(z,r)+Wp.subs(z,2*r))==6*r*(33*r**4-12*r*r+1)
zminus=(6-sp.sqrt(3))/33
zplus=(6+sp.sqrt(3))/33
rminus=sp.sqrt(zminus)
rplus=sp.sqrt(zplus)
Efirst = sp.Rational(36,121)-4*sp.sqrt(3)/363
Elast = sp.Rational(36,121)+4*sp.sqrt(3)/363
Ecentral_saddle = sp.Rational(8,27)
for rr,Eexpect in [(rplus,Efirst),(rminus,Elast)]:
    e=2*W.subs(z,rr)+W.subs(z,2*rr)
    assert sp.simplify(e - Eexpect)==0
assert 0<float(Efirst)<float(Ecentral_saddle)<float(Elast)

# List all 25 critical points in strain coordinates. Map (e1,e2,e3)
# to (u,v)=(e1,-e3); the map is invertible under e1+e2+e3=0.
triples=[(sp.Integer(0),)*3]
for value in [sp.Integer(1),1/sp.sqrt(3)]:
    triples.extend(sorted(set(permutations((value,-value,sp.Integer(0)))), key=str))
for rr in [rminus,rplus]:
    for sgn in [-1,1]:
        triples.extend(sorted(set(permutations((sgn*rr,sgn*rr,-2*sgn*rr))),key=str))
assert len(triples)==25
points=[]
for e1,e2,e3 in triples:
    uu,vv=e1,-e3
    x,y=float(sp.N(uu,18)),float(sp.N(vv,18))
    grad=np.array([float(Fu.subs({u:x,v:y})),float(Fv.subs({u:x,v:y}))])
    assert np.linalg.norm(grad)<2e-12,(e1,e2,e3,grad)
    eig=np.linalg.eigvalsh(np.array(H.subs({u:x,v:y}),dtype=float))
    val=float(Fnp(x,y))
    points.append((val,int(np.sum(eig<0)),x,y))
from collections import Counter
summary=Counter((round(E,11),ind) for E,ind,_,_ in points)
assert summary[(0.0,0)]==7
assert summary[(round(float(Efirst),11),1)]==6
assert summary[(round(float(Ecentral_saddle),11),1)]==6
assert summary[(round(float(Elast),11),2)]==6
print('CRITICAL POINTS (4-site path, pinned ends):',sorted(summary.items()))
print('Exact first positive critical energy E* =',Efirst,'=',sp.N(Efirst,16))

# Complete exact mountain-pass proof:
# LOWER: F is coercive, critical points above form the complete list,
# and E* is first strictly positive critical value. All 7 zero wells are
# nondegenerate and isolated. Sublevel sets 0<=F<c<E* have 7
# components by deformation along -grad(F); A and B cannot connect there.
# UPPER: A=(1,0), C=(1,1), B=(0,1), S=(2r,r), r=rplus.
# Straight segments A-S-C and reflected C-S'-B are monotone
# (increasing on approach to S, decreasing after S).
# Monotonicity is proved in Bernstein basis with rational bounds.
T=sp.symbols('T',real=True)
U=1+(2*r-1)*T
V=r*T
seg=sp.expand(F.subs({u:U,v:V}))
poly_relation=33*r**4-12*r**2+1
segprime=sp.diff(seg,T)
spoly=sp.Poly(segprime,T)
reduced=sp.expand(sum(sp.rem(coef,poly_relation,r)*T**k for (k,),coef in spoly.terms()))
Qpoly=sp.Poly(sp.cancel(reduced/(T*(1-T))),T)
assert Qpoly.degree()==3
bern=[]
for i in range(4):
    beta=sp.factor(sum(Qpoly.nth(k)*sp.Rational(comb(i,k),comb(3,k)) for k in range(i+1)))
    bern.append(beta)
bernform=sp.expand(sum(bern[i]*comb(3,i)*T**i*(1-T)**(3-i) for i in range(4)))
assert sp.expand(Qpoly.as_expr()-bernform)==0
lo,hi=sp.Rational(484,1000),sp.Rational(485,1000)
assert bool(sp.simplify(rplus-lo).is_positive)
assert bool(sp.simplify(hi-rplus).is_positive)
lower_bounds=[]
for beta in bern:
    poly=sp.Poly(beta,r)
    lower=sum(c*(lo if c>0 else hi)**j for (j,),c in poly.terms())
    assert lower>0,lower
    lower_bounds.append(lower)
assert sp.simplify(seg.subs(T,0))==0
assert sp.simplify(seg.subs(T,1).subs(r,rplus)-Efirst)==0
assert sp.simplify(F.subs({u:1,v:1}))==0
assert sp.simplify(F.subs({u:0,v:1}))==0
print('Exact four-site hopping barrier =', Efirst, '; Bernstein certificate lower bounds',
      [round(float(y),6) for y in lower_bounds])

# Fixed-end 3-site positive-energy bump (x0=x2=0), U_a=W+a*e^2/2.
d=sp.symbols('d',real=True)
a=sp.symbols('a',real=True)
Uedge=W + a*z*z/2
za=(2+d)/3;zb=(2-d)/3
a_d=sp.Rational(2,3)*(1-d*d)
Uplus=sp.factor(Uedge.subs({z:sp.sqrt(za),a:a_d}))
Uminus=sp.factor(Uedge.subs({z:sp.sqrt(zb),a:a_d}))
assert sp.factor(Uminus-Uplus) == sp.Rational(4,27)*d**3
assert sp.expand(Uplus - 2*(1-d)*(2+d)**2/27)==0
assert sp.expand(Uminus - 2*(1+d)*(2-d)**2/27)==0
assert sp.expand(sp.diff(Uedge,z,2).subs({z:sp.sqrt(za),a:a_d})- 8*d*(d+2)/3)==0
aval=sp.Rational(1,10)
dval=sp.sqrt(1-sp.Rational(3,2)*aval)
splus=sp.sqrt(za.subs(d,dval))
Epeak=2*Uplus.subs(d,dval)
Ea_barrier=sp.Rational(8,27)*dval**3
print('a=0.1 pinned 3-site: peak',sp.N(splus,13), 'static energy',sp.N(Epeak,13),
      'annihilation excess barrier',sp.N(Ea_barrier,13))

# Dissipative 4-site path dynamics with x0=x3=0, b=1, gamma=5,
# kappa=0; start at A and apply a finite impulse in direction (-1,+1).
B = np.array([[1.,0.],[-1.,1.],[0.,-1.]])

def run_impulse(speed, horizon=150.):
    x0=np.array([1.,0.]); direction=np.array([-1.,1.])/np.sqrt(2)
    y0=np.r_[x0,speed*direction,B@x0]
    gamma=5.
    def rhs(_t,y):
        x,vel,h=y[:2],y[2:4],y[4:]
        strain=B@x;delta=strain-h;g=delta
        return np.r_[vel,-B.T@(wp(strain)+g),gamma*g]
    def energy(y):
        x,vel,h=y[:2],y[2:4],y[4:]
        ee=B@x;delta=ee-h
        return .5*np.dot(vel,vel)+np.sum(w(ee))+.5*np.dot(delta,delta)
    sol=solve_ivp(rhs,[0,horizon],y0,method='DOP853',rtol=2e-10,
                  atol=2e-12,max_step=.15,t_eval=np.linspace(0,horizon,1201))
    assert sol.success,sol.message
    en=np.array([energy(sol.y[:,j]) for j in range(sol.y.shape[1])])
    assert np.max(np.diff(en)) < 1e-8
    return sol.y[:2,-1],sol.y[2:4,-1],en[0],en[-1]

for speed, target in [(.7,np.array([1.,0.])),(1.4,np.array([0.,1.]))]:
    xf,vf,e0,eend=run_impulse(speed)
    assert np.linalg.norm(xf-target)<1e-5,(speed,xf)
    assert np.linalg.norm(vf)<1e-5,(speed,vf)
    assert abs(e0-speed**2/2)<2e-13
    print('IMPULSE speed',speed, 'initial E',round(e0,10), 'end E',eend,
          'end (u,v)',xf, 'end speed',np.linalg.norm(vf))

print('ALL FOLLOW-UP AUDIT CHECKS PASSED. No network or GitHub writes.')
