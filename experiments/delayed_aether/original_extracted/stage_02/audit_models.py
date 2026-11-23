#!/usr/bin/env python3
"""Independent algebraic checks for the discrete positive-energy model."""
import math, csv
import numpy as np
from pathlib import Path
from radial_profile_positive import Radial
OUT=Path(__file__).resolve().parent
model=Radial(L=16,dr=.08,alpha=.25)
x=model.init(R=1.142)
d=model.evaluate(x,details=True)
r=model.r;w=model.w;g=model.g
m=w*d['rho2'];h=d['h']

# Directly check the linear Euler-Lagrange equation for h.
Ah=model.diag*h
Ah[:-1]+=model.sub*h[1:]
Ah[1:]+=model.sub*h[:-1]
res=Ah+g*g*m*h-g*m
assert np.linalg.norm(res,np.inf)<1e-10
# Discrete uneliminated energy equals the integrated-out reduced energy.
c=1-g*h+.5*(g*h)**2
Eraw=float(np.dot(c,m)+np.dot(w,d['rho4'])+.5*np.dot(h,Ah))
assert abs(Eraw-d['energy'])<2e-10
assert min(c)>=.5
# Charge equals exterior radial flux; same law used in the field solver.
Q=g*float(np.dot(m,1-g*h))
Qflux=4*math.pi*r[-1]*h[-1]
assert abs(Q-Qflux)<3e-10
# Check the mesh refinement of optimized energies and charges.
with open(OUT/'positive_radial_results.csv') as f:
 rows=list(csv.DictReader(f))
energies={};charges={}
for row in rows:
 key=(float(row['alpha']),float(row['dr']))
 energies[key]=float(row['energy']);charges[key]=float(row['effective_charge'])
for a in (0.,.25):
 assert abs(energies[a,.08]-energies[a,.12])/energies[a,.08]<2e-4
assert abs(charges[.25,.08]-charges[.25,.12])/charges[.25,.08]<2e-4

out=[
 'AUDIT PASSED',
 f'Field EL residual infinity norm = {np.linalg.norm(res,np.inf):.3e}',
 f'Eliminated-vs-uneliminated E difference = {abs(Eraw-d["energy"]):.3e}',
 f'Pointwise c(h) minimum on tested ansatz = {min(c):.6f} (global analytic bound 0.5)',
 f'Far-field Q from source = {Q:.10f}, from field flux = {Qflux:.10f}',
 f'Optimized energies across dr 0.12/0.08, alpha 0 = {energies[0.,.12]:.8f}/{energies[0.,.08]:.8f}',
 f'Optimized energies across dr 0.12/0.08, alpha 0.25 = {energies[.25,.12]:.8f}/{energies[.25,.08]:.8f}',
 f'Optimized effective charges across dr = {charges[.25,.12]:.8f}/{charges[.25,.08]:.8f}',
 'IMPORTANT: no full 3D or real-time evolution was simulated; only radial-static source and far-field frozen-core pair interaction.',
]
(OUT/'audit.txt').write_text('\n'.join(out)+'\n')
print('\n'.join(out))
