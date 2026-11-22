#!/usr/bin/env python3
"""Weak scalar-field charge versus total rest energy under shape changes."""
from pathlib import Path
import csv
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from radial_profile_positive import Radial
P=Path(__file__).resolve().parent
r=Radial(L=16,dr=.08,alpha=.25)
opt=r.optimize(maxiter=4000)
F=np.r_[np.pi,opt.x,0.]
rn=np.arange(len(F))*r.dr
rows=[]
for factor in (.65,.75,.85,1.,1.15,1.30,1.45):
    distorted=np.interp(rn/factor,rn,F,left=np.pi,right=0.)
    distorted[0]=np.pi;distorted[-1]=0.
    d=r.evaluate(distorted[1:-1],details=True)
    rows.append(dict(scale=factor,E=d['energy'],Q=d['effective_charge'],Q_over_E=d['effective_charge']/d['energy'],
                     E2=d['E2'],E4=d['E4'],B=d['degree']))
with (P/'source_vs_rest_energy.csv').open('w',newline='') as f:
    w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
print('Radial off-shell scaled profiles, not distinct equilibria:')
for row in rows:print(row)
fig,ax=plt.subplots(figsize=(8.8,5.1))
ax.plot([x['scale'] for x in rows],[x['Q_over_E'] for x in rows],'o-')
ax.set(xlabel='Radius scaling of the same degree-one profile',ylabel='Effective scalar charge / total static energy',
       title='Source density rho2 is not the entire rest energy')
ax.grid(alpha=.2);fig.tight_layout();fig.savefig(P/'charge_energy_mismatch.png',dpi=165);plt.close(fig)
from scipy.optimize import brentq
# Construct two finite-energy configurations of equal static E but different scalar charge.
Etarget=rows[0]['E']
def compute_scale(factor):
    distorted=np.interp(rn/factor,rn,F,left=np.pi,right=0.)
    distorted[0]=np.pi;distorted[-1]=0.
    return r.evaluate(distorted[1:-1],details=True)
f_high=brentq(lambda f:compute_scale(f)['energy']-Etarget,1.25,1.5,xtol=1e-12)
lo=compute_scale(.65);hi=compute_scale(f_high)
print('EQUAL ENERGY COUNTEREXAMPLE:',
      'Rsmall',.65,'Rlarge',f_high,'Esmall',lo['energy'],'Elarge',hi['energy'],
      'Qsmall',lo['effective_charge'],'Qlarge',hi['effective_charge'],
      'charge ratio',hi['effective_charge']/lo['effective_charge'])
with (P/'equal_energy_counterexample.csv').open('w',newline='') as f:
    w=csv.DictWriter(f,fieldnames=['scale','E','scalar_charge','topological_degree','E2','E4']);w.writeheader()
    for scale,d in [(0.65,lo),(f_high,hi)]:
        w.writerow(dict(scale=scale,E=d['energy'],scalar_charge=d['effective_charge'],
                        topological_degree=d['degree'],E2=d['E2'],E4=d['E4']))
