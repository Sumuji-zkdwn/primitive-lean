#!/usr/bin/env python3
"""Plots of executed v18 data. No synthetic/generated figure contents."""
import numpy as np,csv
import matplotlib.pyplot as plt
from pathlib import Path
OUT=Path(__file__).resolve().parent

def csvs(name):return list(csv.DictReader(open(OUT/name)))

def nums(rows,key):return np.array([float(r[key]) for r in rows])

rows=[r for r in csvs('affine_gravity_energy.csv') if r['n']=='96' and r['lag_amplitude']=='0.0']
s=nums(rows,'s'); em=nums(rows,'Emat'); eg=nums(rows,'Ugravity'); et=nums(rows,'Etotal')
fig,ax=plt.subplots(figsize=(7.6,4.3))
ax.plot(s,em-em[0],'o-',label='Matter energy change')
ax.plot(s,eg-eg[0],'o-',label='Newtonian binding-energy change')
ax.plot(s,et-et[0],'o-',label='Total change')
ax.axhline(0,linewidth=.8)
ax.set(xlabel='Anisotropic stretch parameter s',ylabel='Energy difference from spherical seed',title='Ellipsoidal deformation: restoring cost vs gravity')
ax.grid(alpha=.23);ax.legend();fig.tight_layout();fig.savefig(OUT/'affine_weak_gravity_stability_v18.png',dpi=190);plt.close(fig)

rows=csvs('nonaffine_quadrupole.csv')
fig,ax=plt.subplots(figsize=(7.6,4.4))
for sig in (2.5,4.5,7.0):
    rr=sorted([r for r in rows if int(r['n'])==96 and float(r['sigma'])==sig],key=lambda x:float(x['eps']))
    eps=nums(rr,'eps');E=nums(rr,'Etotal');
    E0=E[np.argmin(abs(eps))]
    ax.plot(eps,E-E0,'o-',label=f'Localized quadrupole width {sig:g}')
ax.axhline(0,linewidth=.8)
ax.set(xlabel='Local deformation amplitude',ylabel='Matter energy above spherical seed',title='Spatially localized non-spherical deformations')
ax.grid(alpha=.23);ax.legend();fig.tight_layout();fig.savefig(OUT/'nonaffine_energy_v18.png',dpi=190);plt.close(fig)

p0=np.loadtxt(OUT/'psi_slice_n81_s0p0.csv',delimiter=',',skiprows=1)
p1=np.loadtxt(OUT/'psi_slice_n81_s0p16.csv',delimiter=',',skiprows=1)
fig,ax=plt.subplots(figsize=(7.6,4.4))
ax.plot(p0[:,0],p0[:,1]-1,label='Spherical seed (x direction)')
ax.plot(p1[:,0],p1[:,1]-1,label='Distorted seed (x direction)')
ax.plot(p1[:,0],p1[:,2]-1,label='Distorted seed (y direction)')
ax.set(xlabel='Cartesian coordinate',ylabel='Conformal factor ψ − 1',title='Non-spherical Einstein-constraint initial data')
ax.grid(alpha=.23);ax.legend();fig.tight_layout();fig.savefig(OUT/'einstein_nonspherical_psi_v18.png',dpi=190);plt.close(fig)

rows=csvs('non_spherical_adm_initial_data.csv')
fig,ax=plt.subplots(figsize=(7.6,4.3))
for s0 in (0.,.16):
    rr=sorted([r for r in rows if float(r['s'])==s0 and float(r['lag_amplitude'])==0.],key=lambda x:int(x['n']))
    ax.plot([float(r['h'])**2 for r in rr],nums(rr,'ADM_mass'),'o-',label=f's={s0:g}')
ax.set(xlabel='Grid spacing squared',ylabel='Constraint-sourced ADM mass estimate',title='Non-spherical Hamiltonian initial data: grid refinement')
ax.grid(alpha=.23);ax.legend();fig.tight_layout();fig.savefig(OUT/'ADM_mass_resolution_v18.png',dpi=190);plt.close(fig)

osci=np.loadtxt(OUT/'collective_shape_oscillation.csv',delimiter=',',skiprows=1)
fig,ax=plt.subplots(figsize=(7.6,4.3))
ax.plot(osci[:,0],osci[:,1],label='Shape coordinate s(t)')
ax.set(xlabel='Model time',ylabel='Ellipsoidal shape coordinate',title='Restricted quadrupole oscillation (1-DOF ansatz)')
ax.grid(alpha=.23);fig.tight_layout();fig.savefig(OUT/'shape_oscillation_v18.png',dpi=190);plt.close(fig)

fig,ax=plt.subplots(figsize=(7.6,4.1))
ax.plot(osci[:,0],(osci[:,3]-osci[0,3])/osci[0,3])
ax.set(xlabel='Model time',ylabel='Relative reduced-energy drift',title='Restricted Hamiltonian evolution: energy audit')
ax.grid(alpha=.23);fig.tight_layout();fig.savefig(OUT/'collective_energy_audit_v18.png',dpi=190);plt.close(fig)
print('6 v18 figures written')
