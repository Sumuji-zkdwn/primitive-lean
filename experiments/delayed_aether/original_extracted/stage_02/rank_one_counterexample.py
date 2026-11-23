#!/usr/bin/env python3
"""Exact rank-one counterexample: naive linear scalar coupling has no lower bound.
q_n(x)=(cos(n f(r)),sin(n f(r)),0,0), f(r)=(1-r^2)^2 on r<1,
zero outside. The quartic Skyrme derivative term is identically zero.
"""
from fractions import Fraction
import csv,math
from pathlib import Path
import numpy as np
from scipy.integrate import quad
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
OUT=Path(__file__).resolve().parent
C=math.pi*float(Fraction(256,315))
D=math.pi*float(Fraction(524288,2297295))
alpha=0.25
rho=lambda r: 8*r*r*(1-r*r)**2 if 0<=r<=1 else 0.
mass=lambda r: 32*math.pi*(r**5/5-2*r**7/7+r**9/9) if 0<=r<=1 else C
Cn=quad(lambda r:4*math.pi*r*r*rho(r),0,1)[0]
Dn=quad(lambda r:2*r*rho(r)*mass(r),0,1)[0]
assert abs(Cn-C)<1e-12
assert abs(Dn-D)<1e-12
rows=[]
for n in (1,2,3,4,5,6,7,8,10,12,16,20):
    E2=C*n*n
    grav=-0.5*alpha*D*n**4
    rows.append(dict(winding_parameter=n,degree=0,quadratic_energy=E2,quartic_energy=0.,
                     scalar_elimination_energy=grav,total_linear_energy=E2+grav,
                     rigorous_positive_model_lower_bound=0.5*E2))
with open(OUT/'rank_one_no_go.csv','w',newline='') as f:
    w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
fig,ax=plt.subplots(figsize=(8.6,5.2))
ns=np.arange(1,21)
ax.plot(ns,C*ns**2-.5*alpha*D*ns**4,label='Naive linear coupling: energy -> -infinity')
ax.plot(ns,.5*C*ns**2,label='Positive-coupling model lower bound')
ax.axhline(0,lw=1,c='k')
ax.set(xlabel='Internal oscillation index n',ylabel='Energy (model units)',title='Exact counterexample and a pointwise-positive repair')
ax.grid(alpha=.25);ax.legend();fig.tight_layout();fig.savefig(OUT/'rank_one_no_go.png',dpi=160);plt.close(fig)
print('C=',C,'D=',D)
for row in rows: print(row)
