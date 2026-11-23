#!/usr/bin/env python3
"""Plots for v13; uses only saved CSV numeric results."""
import csv, json
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from verify_v13 import ShearModel

HERE=Path(__file__).resolve().parent

def load(name):
    with (HERE/name).open() as f:
        rows=list(csv.DictReader(f))
    return {k:np.array([float(r[k]) for r in rows]) for k in rows[0]}


def curvature_series(tag,full,coupled,kick=0.1,dt=0.002,T=0.2):
    m=ShearModel(n=8,full=full,coupled=coupled)
    state=m.prepare(kick=kick)
    rows=[]
    for step in range(round(T/dt)+1):
        if step%10==0:
            q,B,Z,_,_,_=state
            g=m.regge(B)
            shear,off=m.shear_stats(B)
            rows.append(dict(t=step*dt,charge=m.degree(q),shear=shear,offdiag=off,
                       curvature=g['max_regge_deficit'],min_metric_eig=g['min_vertex_metric_eig'],
                       min_tet_gram=g['min_tet_gram_eig']))
        if step<round(T/dt):state,_=m.step(state,dt)
    with (HERE/f'curvature_{tag}.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
    return rows


def main():
    a={}
    for tag,full,coupled in [('full',True,True),('trace',False,True),('uncoupled',True,False)]:
        a[tag]=curvature_series(tag,full,coupled)
    fig,ax=plt.subplots(figsize=(8.4,4.6))
    for tag,label in [('full','Full internal metric'),('trace','Trace-only metric'),('uncoupled','No q-metric coupling')]:
        rows=a[tag]
        ax.plot([r['t'] for r in rows],[r['curvature'] for r in rows],label=label,lw=2)
    ax.set(xlabel='Model time',ylabel='Max absolute Regge deficit (rad)',title='Intrinsic curvature from coupled field evolution')
    ax.legend(loc='upper left');ax.grid(alpha=.25)
    fig.tight_layout();fig.savefig(HERE/'intrinsic_curvature_comparison.png',dpi=165);plt.close(fig)
    fig,ax=plt.subplots(figsize=(8.4,4.6))
    for tag,label in [('full','Full internal metric'),('trace','Trace-only metric'),('uncoupled','No q-metric coupling')]:
        rows=a[tag]
        ax.plot([r['t'] for r in rows],[r['shear'] for r in rows],label=label,lw=2)
    ax.set(xlabel='Model time',ylabel='Max traceless metric norm',title='Dynamically generated internal shear')
    ax.legend(loc='upper left');ax.grid(alpha=.25)
    fig.tight_layout();fig.savefig(HERE/'dynamical_shear_comparison.png',dpi=165);plt.close(fig)
    fig,ax=plt.subplots(figsize=(8.4,4.6))
    for n in (8,12):
        rows=load(f'contract_n{n}.csv')
        ax.step(rows['time'],rows['degree'],where='post',label=f'{n} subdivisions')
    data=json.loads((HERE/'audit_v13.json').read_text())
    for n in (8,12):
        wit=data[f'topology_{n}']['witness']
        ax.axvline(wit['t'],ls=':',alpha=.7)
    ax.set(xlabel='Homotopy parameter',ylabel='Degree of normalized affine interpolation',title='Topology slip: all vertex states stay on S³',xlim=(0,1),ylim=(-.08,1.1))
    ax.legend();ax.grid(alpha=.25)
    fig.tight_layout();fig.savefig(HERE/'topology_slip_path.png',dpi=165);plt.close(fig)
    fig,ax=plt.subplots(figsize=(8.4,4.6))
    for lab,label in [('full_n8_dt0p002','dt = 0.002'),('full_n8_dt0p001','dt = 0.001')]:
        d=load(lab+'.csv')
        ax.plot(d['time'],np.abs(d['energy_balance_rel']),label=label)
    ax.set(xlabel='Model time',ylabel='Absolute relative energy budget error',title='Action + Rayleigh energy-budget convergence',yscale='log')
    ax.grid(alpha=.25);ax.legend();fig.tight_layout();fig.savefig(HERE/'energy_budget_convergence.png',dpi=165);plt.close(fig)
    # Site-specific shear, evaluated from the finite simulation (not generated image content).
    m=ShearModel(n=8,full=True)
    state=m.prepare()
    for s in range(round(.2/.001)):
        state,_=m.step(state,.001)
    B=state[1]
    fig,ax=plt.subplots(figsize=(6.4,5.5))
    ims=ax.imshow(B[:,:,m.N//2,0,1].T,origin='lower',extent=[-1,1,-1,1],interpolation='nearest',cmap='coolwarm')
    ax.set(xlabel='x',ylabel='y',title='Induced shear component Bxy at z=0, t=0.2')
    fig.colorbar(ims,ax=ax,label='Bxy (dimensionless)')
    fig.tight_layout();fig.savefig(HERE/'shear_field_slice.png',dpi=165);plt.close(fig)

if __name__=='__main__':main()
