#!/usr/bin/env python3
"""Plots of data actually generated from v12 finite lattice runs."""
from pathlib import Path
import numpy as np, pandas as pd
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
ROOT=Path(__file__).resolve().parent

def load(s):return pd.read_csv(ROOT/(s+'_timeseries.csv'))

base=load('finite_n12');un=load('control_n12');long=load('late_n12');protected=load('protected_long_n12')
protected16=load('protected_long_n16')
fig,axs=plt.subplots(2,2,figsize=(10,7))
ax=axs[0,0]
ax.plot(base.time,base.core_x,label='coupled');ax.plot(un.time,un.core_x,ls='--',label='uncoupled');ax.set(title='Freely evolving localized field',xlabel='time',ylabel='q-texture centroid x');ax.legend()
ax=axs[0,1]
ax.plot(base.time,base.max_abs_b,label='geometry |b| max');ax.plot(base.time,base.max_abs_z,label='memory |z| max');ax.set(title='Geometry responds; memory follows',xlabel='time',ylabel='amplitude');ax.legend()
ax=axs[1,0]
ax.plot(base.time,base.max_memory_modulus,label='coupled');ax.axhline(.55,ls='--',label='baseline');ax.set(title='Delayed nonlinear stiffening',xlabel='time',ylabel='maximum tangent modulus');ax.legend()
ax=axs[1,1]
ax.plot(base.time,base.E2+base.E4,label='texture gradient energy');ax.plot(base.time,base['T'],label='kinetic energy');ax.plot(base.time,base.Emetric+base.Ememory,label='geometry + memory');ax.set(title='Energy exchanged between fields',xlabel='time',ylabel='dimensionless energy');ax.legend()
for ax in axs.flat:ax.grid(alpha=.25)
fig.tight_layout();fig.savefig(ROOT/'self_consistent_dynamics.png',dpi=150);plt.close(fig)

fig,axs=plt.subplots(2,1,figsize=(9,6.7),sharex=True)
for label in ['late_n12','late_n16','late_n20']:
 df=load(label);axs[0].step(df.time,df.charge,where='post',label=f'unprotected {label.split("_")[-1]}')
axs[0].step(protected.time,protected.charge,where='post',label='protected n12',linestyle='--')
axs[0].step(protected16.time,protected16.charge,where='post',label='protected n16',linestyle=':')
axs[0].set(ylabel='winding number B',title='Unprotected lattice loses degree; local barrier preserves it');axs[0].legend(ncol=2,fontsize=8,loc='lower left')
axs[1].plot(long.time,long.min_pair_dot,label='unprotected n12');axs[1].plot(protected.time,protected.min_pair_dot,label='protected n12');axs[1].plot(protected16.time,protected16.min_pair_dot,label='protected n16')
axs[1].axhline(0,ls='--',label='inadmissibility threshold, s=0')
axs[1].set(xlabel='time',ylabel='minimum edge dot product');axs[1].legend(ncol=2,fontsize=8)
for ax in axs:ax.grid(alpha=.2)
fig.tight_layout();fig.savefig(ROOT/'topology_admissibility.png',dpi=150);plt.close(fig)

f=load('fine_dt_n12')
fig,ax=plt.subplots(figsize=(8.5,4.3))
ax.plot(base.time,base.balance_error,label='time step .002');ax.plot(f.time,f.balance_error,label='time step .001');ax.axhline(0,color='gray',lw=.8)
ax.set(title='Relative energy balance residual H(t)+D(t)-H(0)',xlabel='time',ylabel='relative residual');ax.legend();ax.grid(alpha=.25)
fig.tight_layout();fig.savefig(ROOT/'energy_balance_convergence.png',dpi=150);plt.close(fig)

z=np.load(ROOT/'coupled_snapshot_n12_t024.npz')
q=z['q'];b=z['b'];n=q.shape[0]
fig,axs=plt.subplots(1,2,figsize=(9.7,4.2))
extent=[-1,1,-1,1]
for ax,arr,title in [(axs[0],q[:,:,n//2,0],'Internal state q0'),(axs[1],.15*b[:,:,n//2],'Intrinsic metric log-scale αb')]:
 im=ax.imshow(arr.T,origin='lower',extent=extent,aspect='equal')
 ax.set(title=title,xlabel='x',ylabel='y');fig.colorbar(im,ax=ax,shrink=.85)
fig.suptitle('Self-consistent field and geometry at model time 0.24')
fig.tight_layout();fig.savefig(ROOT/'field_metric_slice.png',dpi=150);plt.close(fig)
print('created four plots')
