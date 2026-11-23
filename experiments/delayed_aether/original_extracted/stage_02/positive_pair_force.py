#!/usr/bin/env python3
"""First-order / separated-core force using the isolated dressed sources.
This is NOT the fully coupled two-soliton boundary value problem.
"""
import csv, math
from pathlib import Path
import numpy as np
from numpy.polynomial.legendre import leggauss
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

OUT=Path(__file__).resolve().parent
p=np.genfromtxt(OUT/'positive_profile_alpha_0p25.csv',delimiter=',',names=True)
r=np.asarray(p['radius']);rho=np.asarray(p['rho2']);h=np.asarray(p['h']);g=.5;K=1.
source=g*(1-g*h)*rho
m=4*math.pi*r*r*(r[1]-r[0])*source
M=np.cumsum(m)
Q=float(np.sum(m))

def mass_inside(s):
    s=np.asarray(s)
    ans=np.interp(s,r,M,left=0,right=Q)
    mask=s<r[0]
    ans[mask]=M[0]*(s[mask]/r[0])**3
    return ans

def force(d,ng=120):
    mu,wm=leggauss(ng)
    v=d+r[:,None]*mu[None,:]
    radius=np.sqrt(d*d+r[:,None]**2+2*d*r[:,None]*mu[None,:])
    inside=mass_inside(radius)
    field_force=(inside/(4*math.pi*K*radius**3))*v
    return float(np.dot(m,np.dot(field_force,wm)/2))

rows=[]
for d in (3.,4.,5.,6.,8.,10.,12.,16.,24.,32.):
    actual=force(d)
    ideal=Q*Q/(4*math.pi*K*d*d)
    rows.append(dict(distance=d,force_dressed=actual,far_field_inverse_square=ideal,ratio=actual/ideal))
for d in (4.,10.,24.):
    v120=force(d,120);v220=force(d,220)
    assert abs(v120-v220)/abs(v220)<3e-5
with open(OUT/'positive_pair_force.csv','w',newline='') as f:
    w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
fig,ax=plt.subplots(figsize=(8.6,5.2))
ax.plot([d['distance'] for d in rows],[d['ratio'] for d in rows],'o-',lw=2)
ax.axhline(1,ls='--',c='k',label='Inverse-square far-field limit')
ax.set(xlabel='Separation (model units)',ylabel='Force / inverse-square limit',title='Dressed positive-energy defect: long-range force (separated-core approximation)')
ax.grid(alpha=.25);ax.legend();fig.tight_layout();fig.savefig(OUT/'positive_pair_force.png',dpi=160);plt.close(fig)
print('Total dressed charge Q',Q)
for d in rows:print(d)
