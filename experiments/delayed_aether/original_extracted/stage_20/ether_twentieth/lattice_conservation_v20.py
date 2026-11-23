#!/usr/bin/env python3
"""Spatially local source-conservation test on a periodic 1+1 lattice.
No GR assumed; this is a discrete matter Hamiltonian and a Ward source test.
"""
import json
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

OUT=Path(__file__).resolve().parent
N=128
L=20.
dx=L/N
k=.9
lam=.35

def forw(a):
    return (np.roll(a,-1)-a)/dx
def lap(a):
    return (np.roll(a,-1)-2*a+np.roll(a,1))/(dx*dx)
def pot(q,z):
    d=q-z
    return k*d*d/2 + lam*d**4/4
def force(q,z):
    d=q-z
    return k*d + lam*d**3

def hamiltonian_density(q,z,v,w):
    dq=forw(q); dz=forw(z)
    return (.5*(v*v+w*w)+.25*(dq*dq+np.roll(dq*dq,1)
              +dz*dz+np.roll(dz*dz,1))+pot(q,z))

def flux(q,z,v,w):
    # flux at the interface between i and i+1
    return (-.5*(v+np.roll(v,-1))*forw(q)
            -.5*(w+np.roll(w,-1))*forw(z))

def rates(q,z):
    F=force(q,z)
    return lap(q)-F,lap(z)+F

def local_derivative(q,z,v,w):
    av,aw=rates(q,z)
    dq=forw(q); dz=forw(z)
    dv=forw(v); dw=forw(w)
    return (v*av+w*aw +.5*(dq*dv+np.roll(dq*dv,1)
               +dz*dw+np.roll(dz*dw,1)) +force(q,z)*(v-w))

def source_identity(q,z,v,w):
    edot=local_derivative(q,z,v,w)
    J=flux(q,z,v,w)
    divJ=(J-np.roll(J,1))/dx
    return float(np.max(np.abs(edot+divJ)))

def total_energy(q,z,v,w):
    return float(dx*np.sum(hamiltonian_density(q,z,v,w)))

def test_random():
    rng=np.random.default_rng(20261122)
    errs=[]
    for _ in range(100):
        q=rng.normal(size=N)
        z=rng.normal(size=N)
        v=rng.normal(size=N)
        w=rng.normal(size=N)
        errs.append(source_identity(q,z,v,w))
    assert max(errs)<2e-12,max(errs)
    return max(errs)

def velocity_verlet(q,z,v,w,dt):
    av,aw=rates(q,z)
    vh=v+.5*dt*av;wh=w+.5*dt*aw
    q1=q+dt*vh;z1=z+dt*wh
    av1,aw1=rates(q1,z1)
    return q1,z1,vh+.5*dt*av1,wh+.5*dt*aw1

def run_case(dt):
    x=np.arange(N)*dx
    q=.7*np.exp(-((x-6.0)/.9)**2)
    z=-.35*np.exp(-((x-7.1)/1.1)**2)
    v=.31*np.exp(-((x-5.5)/.7)**2)
    w=.16*np.exp(-((x-8.0)/.8)**2)
    E0=total_energy(q,z,v,w)
    T=6.
    n=round(T/dt)
    maxdrift=0.
    states=[]
    rows=[]
    stride=max(1,n//120)
    for i in range(n+1):
        if i%stride==0 or i==n:
            energy=total_energy(q,z,v,w)
            drift=(energy-E0)/E0
            maxdrift=max(maxdrift,abs(drift))
            err=source_identity(q,z,v,w)
            rows.append([i*dt,energy,drift,err])
            if i in {0,n//2,n}:
                states.append((i*dt,x.copy(),hamiltonian_density(q,z,v,w).copy(),flux(q,z,v,w).copy()))
        if i<n:
            q,z,v,w=velocity_verlet(q,z,v,w,dt)
    return {'time_step':dt,'steps':n,'initial_energy':E0,
            'max_abs_relative_energy_drift':maxdrift,
            'max_instantaneous_local_balance_residual':max(x[3] for x in rows),
            'history':np.array(rows),'states':states}

def main():
    random_err=test_random()
    coarse=run_case(.004)
    fine=run_case(.002)
    assert fine['max_abs_relative_energy_drift']<coarse['max_abs_relative_energy_drift']
    ratio=coarse['max_abs_relative_energy_drift']/fine['max_abs_relative_energy_drift']
    assert 3.0<ratio<5.0,ratio
    for tag,rr in [('coarse',coarse),('fine',fine)]:
        np.savetxt(OUT/f'local_energy_{tag}.csv',rr['history'],delimiter=',',comments='',
                   header='t,E_total,relative_E_error,local_balance_max_residual')
    fig,ax=plt.subplots(figsize=(8.8,4.7))
    for tag,rr in [('dt=0.004',coarse),('dt=0.002',fine)]:
        ax.plot(rr['history'][:,0],rr['history'][:,2],label=tag)
    ax.set(xlabel='model time',ylabel='relative global energy drift',
           title='Hamiltonian spatial lattice: time-step refinement')
    ax.legend();ax.grid(alpha=.2);fig.tight_layout();fig.savefig(OUT/'spatial_energy_convergence_v20.png',dpi=165);plt.close(fig)
    fig,ax=plt.subplots(figsize=(9,4.5))
    for t,x,e,j in fine['states']:
        ax.plot(x,e,label=f't={t:.2f}')
    ax.set(xlabel='space x',ylabel='local energy density',title='Spatial exchange of energy: finite lattice')
    ax.legend();ax.grid(alpha=.2);fig.tight_layout();fig.savefig(OUT/'spatial_energy_transport_v20.png',dpi=165);plt.close(fig)
    audit={'model':'two coupled wave fields q,z on periodic 1D spatial lattice; nonlinear local potential; site kinetic and shared bond gradient energy',
           'Hamiltonian_energy_balance_equation':'dot(e_i)+(J_(i+1/2)-J_(i-1/2))/dx=0',
           'exact_lattice_current':'J_(i+1/2)=-[ (v_i+v_(i+1))*(q_(i+1)-q_i) + (w_i+w_(i+1))*(z_(i+1)-z_i) ]/(2 dx)',
           'max_residual_for_100_independent_random_states':random_err,
           'coarse':{k:v for k,v in coarse.items() if k not in ('history','states')},
           'fine':{k:v for k,v in fine.items() if k not in ('history','states')},
           'time_step_refinement_error_ratio':ratio,
           'coupling_source_exchange':'q subsystem: dot e_q+div J_q=-F*v; z subsystem: dot e_z+div J_z=+F*w; potential: dot V=F*(v-w)',
           'limits':'A periodic spatial lattice toy model, not 4D Einstein equations. Exact semidiscrete continuity does not imply exact conservation by time integrator.'}
    (OUT/'lattice_audit_v20.json').write_text(json.dumps(audit,indent=2,ensure_ascii=False)+'\n')
    print(json.dumps(audit,indent=2,ensure_ascii=False))
if __name__=='__main__':main()
