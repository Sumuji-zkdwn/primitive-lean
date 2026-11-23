#!/usr/bin/env python3
"""Gauge-compatible curvature-memory toy on v8 linear canonical lattice.

Prototype only. It preserves linear constraints because local spatial Einstein
operator annihilates gauge strain and has a vanishing discrete divergence.
Coupling to curvature adds fourth spatial derivatives and is NOT uniformly causal
as a continuum model. It is neither a GR derivation nor a realistic fluid model.
"""
import json
import csv
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from verify_v8 import (G3, h_velocity, hamiltonian, physical_initial_data,
                       scalar_constraint, momentum_constraint, maxabs)
OUT=Path(__file__).resolve().parent

def experiment(N=17, dt=.09, steps=240, tau=.8, kappa=.5):
    h,p,xi=physical_initial_data(N)
    z=G3(h)
    e0=hamiltonian(h,p)+.5*kappa*np.sum((G3(h)-z)**2)
    data=[]
    max_h,max_p=0.,0.
    for it in range(steps+1):
        C=maxabs(scalar_constraint(h)); P=maxabs(momentum_constraint(p))
        energy=hamiltonian(h,p)+.5*kappa*np.sum((G3(h)-z)**2)
        strain=float(np.max(np.sqrt(np.sum((G3(h)-z)**2,axis=(0,1)))))
        if it%4==0 or it==steps:
            data.append([it*dt,energy/e0,C,P,strain])
        max_h=max(max_h,C);max_p=max(max_p,P)
        if it==steps:break
        # Exact memory relaxation half-step at fixed h.
        ex=np.exp(-dt/(2*tau))
        z=ex*z+(1-ex)*G3(h)
        def force(h0,z0):return -G3(h0)-kappa*G3(G3(h0)-z0)
        p=p+.5*dt*force(h,z)
        h=h+dt*h_velocity(p)
        p=p+.5*dt*force(h,z)
        z=ex*z+(1-ex)*G3(h)
    arr=np.array(data)
    with (OUT/'memory_dynamics.csv').open('w',newline='') as f:
        w=csv.writer(f);w.writerow(['t','normalized_total_energy','scalar_constraint_max',
                                    'momentum_constraint_max','max_curvature_memory_mismatch'])
        w.writerows(data)
    fig,axs=plt.subplots(2,1,figsize=(8.8,6.4),sharex=True,layout='constrained')
    axs[0].plot(arr[:,0],arr[:,1]);axs[0].set_ylabel('total energy / initial');axs[0].grid(alpha=.2)
    axs[1].plot(arr[:,0],arr[:,4]);axs[1].set_ylabel('max |curvature - memory|')
    axs[1].set_xlabel('time');axs[1].grid(alpha=.2)
    fig.suptitle('Gauge-compatible but higher-gradient curvature memory')
    fig.savefig(OUT/'curvature_memory.png',dpi=160);plt.close(fig)
    assert max_h<1e-11 and max_p<1e-11
    return {'grid':N,'dt':dt,'steps':steps,'tau':tau,'kappa':kappa,
            'initial_energy':e0,'final_energy':float(energy),
            'energy_ratio':float(energy/e0),
            'maximum_scalar_constraint':max_h,'maximum_momentum_constraint':max_p,
            'maximum_memory_mismatch':float(max(arr[:,4])),
            'warning':'Spatial curvature-gradient memory has k^4 dispersion, so no universal continuum wavefront speed follows.'}
if __name__=='__main__':
    result=experiment()
    (OUT/'memory_audit_v8.json').write_text(json.dumps(result,indent=2))
    print(json.dumps(result,indent=2))
