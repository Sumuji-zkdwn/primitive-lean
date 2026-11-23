#!/usr/bin/env python3
"""Regression audit of precomputed V4 CSVs and math identities."""
from pathlib import Path
from math import pi,sqrt
import csv
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
P=Path(__file__).resolve().parent

def readcsv(name):
    with (P/name).open(newline='') as f:
        return [{k:(float(v) if v not in ('','None','nan','NaN') else np.nan) if k not in ('kind','case','tag') else v for k,v in r.items()} for r in csv.DictReader(f)]

non=readcsv('nonradial_tests_coarse_medium.csv')+readcsv('nonradial_tests_fine.csv')
non.sort(key=lambda r:(r['n'],r['kind'],r['epsilon']))
with (P/'nonradial_tests_all.csv').open('w',newline='') as f:
    w=csv.DictWriter(f,fieldnames=list(non[0]));w.writeheader();w.writerows(non)

bases={int(r['n']):r for r in non if r['kind']=='baseline'}
assert list(sorted(bases))==[49,61,91],list(sorted(bases))
assert all(bases[n]['E']>3*sqrt(2)*pi*pi*abs(bases[n]['B']) for n in bases)
assert all(bases[n]['solver_rel_residual']<2e-9 for n in bases)
assert all(x['delta_E']>0 for x in non if x['kind'] not in ('baseline','translation'))
assert all(x['curvature']>0 for x in non if x['kind'] not in ('baseline',))
translation={int(x['n']):x['delta_E'] for x in non if x['kind']=='translation' and x['epsilon']>0}
assert translation[91]<translation[61]<translation[49]
assert abs(1-bases[91]['B'])<abs(1-bases[61]['B'])<abs(1-bases[49]['B'])
scalar=readcsv('equal_energy_counterexample.csv')
assert len(scalar)==2
assert abs(scalar[0]['E']-scalar[1]['E'])<1e-8
assert abs(scalar[0]['topological_degree']-1)<1e-12 and abs(scalar[1]['topological_degree']-1)<1e-12
ratio=scalar[1]['scalar_charge']/scalar[0]['scalar_charge']
assert ratio>2

disp=readcsv('dispersion.csv')
tuned=[r for r in disp if r['case']=='front_matched']
assert len(tuned)>200
assert max(abs(x['c_front_q']-x['c_front_h']) for x in tuned)<1e-14
assert max(abs(x['c_front_q']-1) for x in tuned)<1e-14
assert min(x['attenuation'] for x in tuned)>=0
summary=readcsv('saturated_dynamics_summary.csv')
assert len(summary)==2
for row in summary:
    assert row['energy_final']<=row['energy_initial']
    assert row['energy_balance_max_abs']<1e-6
    assert row['gradient_rel_error']<1e-5
    assert row['power_rel_error']<1e-5
bounded=[r for r in summary if r['tag']=='bounded_memory_tuned'][0]
assert bounded['max_extra_modulus']<6.9+1e-8
for tag in ('quartic_tuned','bounded_memory_tuned'):
    times=readcsv(tag+'_timeseries.csv')
    E=np.array([r['E'] for r in times]);D=np.array([r['cumulative_dissipation'] for r in times])
    assert len(times)==161
    assert np.max(np.diff(E))<1e-5
    assert np.max(np.abs(E+D-E[0]))<1e-6

# Actual-grid refined overview.
fig,axs=plt.subplots(1,2,figsize=(11.2,4.5))
for k,eps,label in [('affine',.15,'Volume-preserving ellipsoid'),('quadrupole',.04,'Quadrupole'),('random',.04,'Smooth random')]:
    pick=[r for r in non if r['kind']==k and r['epsilon']>0 and (k!='affine' or r['n']>=61)]
    pick.sort(key=lambda r:r['dx'],reverse=True)
    axs[0].plot([r['dx'] for r in pick],[r['delta_E'] for r in pick],'o-',label=label)
axs[0].axhline(0,color='black',lw=1)
axs[0].set(xlabel='Grid spacing',ylabel='Energy increase',title='Non-spherical energy tests across grids')
axs[0].legend(fontsize=8);axs[0].grid(alpha=.2)
axs[1].plot([bases[n]['dx'] for n in sorted(bases)],[bases[n]['B'] for n in sorted(bases)],'o-',label='Discrete topological degree')
axs[1].axhline(1,color='black',lw=1,ls='--',label='Continuum degree 1')
axs[1].set(xlabel='Grid spacing',ylabel='Numerical winding',title='Degree approximation improves with resolution',ylim=(.88,1.012))
axs[1].legend(fontsize=8);axs[1].grid(alpha=.2)
fig.tight_layout();fig.savefig(P/'nonradial_resolution_audit.png',dpi=165);plt.close(fig)

msg=f'''MODEL V4 INDEPENDENT DATA AUDIT: PASS
Symmetry-free continuum lower bound: E >= {3*sqrt(2)*pi*pi:.12f} |B| for smooth q:S^3 and c(h)>=0.5.
3D Cartesian baseline: {', '.join(f'{n}^3 E={bases[n]["E"]:.9f} B_discrete={bases[n]["B"]:.9f}' for n in sorted(bases))}
All sampled non-radial shape perturbations have positive energy difference: yes.
Translation artifacts decreasing with resolution: {translation}
Static h solver maximum relative residual: {max(x['solver_rel_residual'] for x in non):.3e}
Equal-energy degree-one configurations: E={scalar[0]['E']:.12f} and {scalar[1]['E']:.12f}; Q ratio={ratio:.12f}.
Vacuum wave fronts tuned to 1 for q and h; relaxation dispersion persists.
No global causal cone follows: quartic memory and fixed-inertia Skyrme-gradient modulus can be unbounded.
Time-dependent bounded-memory model: 161 samples; H+D balance max={bounded['energy_balance_max_abs']:.3e}; max memory modulus={bounded['max_extra_modulus']:.9f} (<6.9).
All results are limited to their stated mathematical assumptions; no verified general relativity or equivalence principle.
'''
(P/'audit.txt').write_text(msg)
print(msg)
