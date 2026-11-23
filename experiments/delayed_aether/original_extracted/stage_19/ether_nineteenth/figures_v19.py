#!/usr/bin/env python3
"""Charts from auditable csv/json output for v19."""
import json
from pathlib import Path
import numpy as np
import matplotlib.pyplot as plt
from scipy.interpolate import PchipInterpolator
from scipy.linalg import eigh
from verify_v19 import Radial,projected_matrices,bases
OUT=Path(__file__).resolve().parent
DAT=json.loads((OUT/'audit_v19.json').read_text())
ROB=json.loads((OUT/'robustness_v19.json').read_text())
IND=json.loads((OUT/'independent_audit_v19.json').read_text())
m=Radial(320); oldf,oldc=m.unpack(m.initial())
data=np.genfromtxt(OUT/'radial_profile_n320.csv',delimiter=',',names=True)
r=data['r'];f=data['f'];chi=data['chi']
fig,axs=plt.subplots(2,1,figsize=(8.2,6.7),sharex=True)
for ax,name,old,new in [(axs[0],'profile f(r)',oldf,f),(axs[1],'memory field chi(r)',oldc,chi)]:
 ax.plot(r,old,'--',label='v18 initial field')
 ax.plot(r,new,label='v19 optimized equilibrium')
 ax.set_ylabel(name);ax.grid(alpha=.25)
axs[1].set_xlabel('radius r (model units)');axs[0].legend(loc='best');axs[0].set_xlim(0,4.0)
fig.tight_layout();fig.savefig(OUT/'profile_old_vs_equilibrium_v19.png',dpi=160);plt.close(fig)

fig,ax=plt.subplots(figsize=(7.8,4.7))
con=DAT['equilibrium']+[{"n":r['n'],"energy_equilibrium":r['energy']} for r in ROB['continuation']]
x=np.array([i['n'] for i in con]);y=np.array([i['energy_equilibrium'] for i in con])
ax.plot(x,y,'o-',label='discrete stationary energy')
ax.axhline(6*np.pi**2*np.sqrt(.2),linestyle='--',label='degree-1 analytic lower bound')
ax.set_xlabel('radial intervals N');ax.set_ylabel('E (dimensionless)')
ax.set_ylim(24,40);ax.grid(alpha=.25);ax.legend();fig.tight_layout()
fig.savefig(OUT/'equilibrium_resolution_v19.png',dpi=160);plt.close(fig)

fig,ax=plt.subplots(figsize=(8.0,4.9))
rad=IND['radial_180']['six_smallest_omega_squared']
l2,l3=[],[]
for row in ROB['basis_stress']:
 if row['family']=='expanded_10':
  if row['l']==2:l2=[row['minimum_omega_squared'],row['second_omega_squared']]
  if row['l']==3:l3=[row['minimum_omega_squared'],row['second_omega_squared']]
ax.scatter(np.arange(1,7),rad,label='radial modes l=0 (6 smallest)')
ax.scatter(np.arange(1,3),l2,label='restricted l=2 modes (2 smallest)')
ax.scatter(np.arange(1,3),l3,label='restricted l=3 modes (2 smallest)')
ax.axhline(0,color='gray',linewidth=1);ax.set_ylabel(r'generalized eigenvalue $\omega^2$')
ax.set_xlabel('lowest eigenvalue rank within tested subspace');ax.grid(alpha=.25);ax.legend()
fig.tight_layout();fig.savefig(OUT/'projected_mode_eigenvalues_v19.png',dpi=160);plt.close(fig)

# Show first l=2 lowest restricted eigenvector in f and chi channels.
sf=PchipInterpolator(r,f);sc=PchipInterpolator(r,chi)
rg=np.linspace(1e-4,12.,2401)
widths=(.38,.55,.8,1.15,1.6,2.2,3.,4.2,5.8,8.2)
K,M,ew,vec=projected_matrices(rg,sf,sc,l=2,widths=widths)
bs=bases(rg,2,widths,Rbox=12.);
a=sum(vec[j,0]*bs[j][0] for j in range(len(bs)))
b=sum(vec[j+len(bs),0]*bs[j][0] for j in range(len(bs)))
scale=max(np.max(abs(a)),np.max(abs(b)))
fig,ax=plt.subplots(figsize=(8,4.7))
ax.plot(rg,a/scale,label='delta f radial envelope')
ax.plot(rg,b/scale,label='delta chi radial envelope')
ax.set_xlabel('radius r');ax.set_ylabel('relative mode amplitude')
ax.set_xlim(0,10);ax.grid(alpha=.25);ax.legend();fig.tight_layout()
fig.savefig(OUT/'lowest_l2_trial_mode_v19.png',dpi=160);plt.close(fig)
print('figures written')
