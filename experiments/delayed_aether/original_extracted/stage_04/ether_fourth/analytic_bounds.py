#!/usr/bin/env python3
"""Pointwise degree/energy bound and exact radial-affine deformation identity.

For c(h)>=1/2, rho2=0.5 sum lambda_i^2,
    rho4=0.5 sum_{i<j}lambda_i^2lambda_j^2,
    c rho2 + rho4 >= 3 sqrt(c) |lambda1 lambda2 lambda3|.
Thus E >= 3 sqrt(1/2) * 2*pi^2*abs(degree) = 3 sqrt(2) pi^2 abs(B).
"""
from pathlib import Path
from math import sqrt,pi,cosh
import csv
import numpy as np
from radial_profile_positive import Radial
P=Path(__file__).resolve().parent
BOUND=3*sqrt(2)*pi*pi
r=Radial(L=16,dr=.16,alpha=.25)
opt=r.optimize(maxiter=2500)
d=r.evaluate(opt.x,details=True)
rr=r.r; w=r.w; h=d['h'];v=r.g*h
# Reconstruct radial energy including h, not just envelope reduction.
cf=1-v+.5*v*v
S=np.dot(w,cf*d['rho2'])+.5*np.dot(h,r.diag*h)+np.dot(h[:-1]*h[1:],r.sub)
Q=np.dot(w,d['rho4'])
assert abs(S+Q-d['energy'])<1e-8,(S,Q,d['energy'])
rows=[]
for eps in (0,.05,.10,.15,.20,.30):
    # A=diag(exp(eps),exp(-eps),1); det A=1.
    factor=(1+2*cosh(2*eps))/3
    predicted=factor*(S+Q)
    rows.append(dict(epsilon=eps,analytic_energy=predicted,energy_ratio=factor,deltaE=predicted-(S+Q)))
    assert predicted>=S+Q-1e-9
with (P/'affine_analytic.csv').open('w',newline='') as f:
    wri=csv.DictWriter(f,fieldnames=list(rows[0]));wri.writeheader();wri.writerows(rows)
# Random pointwise audit of the AM-GM argument (not a proof; the formula above is).
rng=np.random.default_rng(93010)
lam=np.exp(rng.uniform(-6,6,size=(200000,3)))
t=rng.uniform(-1,1,size=len(lam))
c=1-t+.5*t*t
rho2=.5*np.sum(lam*lam,axis=-1)
rho4=.5*((lam[:,0]*lam[:,1])**2+(lam[:,0]*lam[:,2])**2+(lam[:,1]*lam[:,2])**2)
J=np.prod(lam,axis=-1)
relative_slack=(c*rho2+rho4)/(3*np.sqrt(c)*J)-1
assert np.min(relative_slack)>=-1e-12
assert (S+Q)>=BOUND-1e-9
print(f'FULL NONRADIAL LOWER BOUND E >= {BOUND:.12f} |B|')
print(f'Radial static E = {d["energy"]:.12f}; topological B = {d["degree"]:.1f}')
print(f'E(Sigma2+scalar)={S:.10f}, E(Skyrme quartic)={Q:.10f}')
print(f'200k positive singular-value triples: min relative AMGM slack {np.min(relative_slack):.3e}')
print(f'Anisotropic vol-preserving eps=0.15: E/E0={rows[3]["energy_ratio"]:.9f}, delta E={rows[3]["deltaE"]:.9f}')
