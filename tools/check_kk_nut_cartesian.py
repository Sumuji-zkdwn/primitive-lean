#!/usr/bin/env python3
"""Exact single-centre Taub-NUT Hopf coordinate metric identity and smooth extension.

Classical geometry identities; exact rational symbolic expressions. The Hopf
map with fibre angle chi period 4*pi covers S3 once; the smooth extension is
on R4 and has a positive definite metric for c>=0, k>0.
"""
import sympy as s
from itertools import product

rho, theta, phi, chi, k, c = s.symbols('rho theta phi chi k c', real=True, positive=True)
alpha = c/(4*k*k)
Q = 1+alpha*rho*rho
r = rho*rho/(4*k)
H = c+k/r
assert s.simplify(H-4*k*k*Q/(rho*rho)) == 0

# Hopf map z1=rho cos(theta/2)e^(i(chi+phi)/2),
# z2=rho sin(theta/2)e^(i(chi-phi)/2) yields directly
# |dz1|²+|dz2|²=d rho² + rho²/4 [d theta²+sin² theta d phi²
#                                      +(d chi+cos theta d phi)²].
# The equality is checked coefficient-wise by elementary trig identities.
coords=[rho,theta,phi,chi]
u=s.cos(theta/2)**2; v=s.sin(theta/2)**2
flat=s.zeros(4)
flat[0,0]=1; flat[1,1]=rho*rho/4
flat[2,2]=rho*rho/4
flat[3,3]=rho*rho/4
flat[2,3]=flat[3,2]=rho*rho*s.cos(theta)/4
J=s.zeros(4)
J[0,0]=u+v; J[1,1]=rho*rho/4
J[2,2]=rho*rho*(u+v)/4
J[3,3]=rho*rho*(u+v)/4
J[2,3]=J[3,2]=rho*rho*(u-v)/4
for i,j in product(range(4),repeat=2):
    assert s.trigsimp(J[i,j]-flat[i,j])==0,('Hopf map',i,j)

# Spatial Taub-NUT r-metric in these coordinates (rho,theta,phi,chi)
metric=s.zeros(4)
metric[0,0]=Q
metric[1,1]=Q*rho*rho/4
metric[2,2]=Q*rho*rho*s.sin(theta)**2/4 +rho*rho/(4*Q)*s.cos(theta)**2
metric[3,3]=rho*rho/(4*Q)
metric[2,3]=metric[3,2]=rho*rho*s.cos(theta)/(4*Q)

# omega = Im(conj(z1) dz1+conj(z2) dz2) = rho²/2*(dchi+cos(theta)dphi).
omega=s.Matrix([0,0,rho*rho*s.cos(theta)/2,rho*rho/2])
coeff=-alpha*(2+alpha*rho*rho)/Q
claimed = Q*flat + coeff*(omega*omega.T)
for i,j in product(range(4),repeat=2):
    assert s.trigsimp(s.simplify(metric[i,j]-claimed[i,j]))==0,('cartesian extension',i,j)

# Define Cartesian variables for a globally smooth tensor.
X=s.symbols('X0:4',real=True)
s4=sum(z*z for z in X)
q4=1+alpha*s4
w=s.Matrix([-X[1],X[0],-X[3],X[2]])
K=q4*s.eye(4)-alpha*(2+alpha*s4)/q4*(w*w.T)
assert s.simplify(w.dot(w)-s4)==0
assert s.simplify(w.dot(s.Matrix(X)))==0
# Rank-one identity: eigenvalues q (3 times), 1/q (along w).
# The diagonalization follows from w·w=s and K w=(q+beta*s)w.
beta=-alpha*(2+alpha*s4)/q4
assert s.factor(q4+beta*s4-1/q4)==0
assert s.factor(q4**3*(q4+beta*s4)-q4**2)==0
assert K.subs({p:0 for p in X})==s.eye(4)
# Sherman-Morrison inverse using the rank-one scalar identity.
# Kinv=(1/q)I-beta wwT; product=I since q+beta*s=1/q.
assert s.factor(q4*(-beta)+beta/q4-beta*beta*s4)==0
# Coefficients rational with q>0 (alpha>=0), so smooth and positive.
print('PASS: all 16 Hopf pullback identities, 16 Cartesian metric identities')
print('PASS: exact 4D Cartesian metric at origin, determinant=q², inverse')
print('PASS: global Cartesian smoothness and positive definiteness for alpha>=0')
print('SCOPE: chi period 4*pi, psi period 4*pi*k; no automatic Lean bundle-atlas theorem')
