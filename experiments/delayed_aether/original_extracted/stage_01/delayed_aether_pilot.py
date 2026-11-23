#!/usr/bin/env python3
"""Reproducible finite one-dimensional delayed-hardening 'aether' pilot.

Nonrelativistic dissipative toy, NOT a derivation of particles, gravity or GR.
The phi^4 double well is an intentionally added structural ingredient.

Internal edge strain e_i = (phi[i+1] - phi[i])/dx; memory m_i >=0.
  d(phi_i)/dt = (G(m_i)e_i - G(m_{i-1})e_{i-1})/dx - dV/dphi
  tau*d(m_i)/dt = e_i^2 - m_i
  V = (phi^2-1)^2/4 (optional)
  G = 1 + beta*m^4/(mc^4 + m^4)
At beta=0, this is phi^4 gradient flow. Time is relaxation time.

Boundary: kink (-1, +1); bubble/kink-antikink (-1, -1).
"""
import csv
import json
import math
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
SQRT2 = math.sqrt(2)
M_KINK = 2*SQRT2/3


def field_profile(x, mode='bubble', separation=4.0):
    if mode == 'bubble':
        return np.tanh((x+separation/2)/SQRT2) - np.tanh((x-separation/2)/SQRT2) - 1.
    if mode == 'kink':
        return np.tanh(x/SQRT2)
    raise ValueError(mode)


def field_energy(phi, dx, include_potential=True):
    # Periodic assumption not used: cell-centered edge discretization with
    # flat boundary states, endpoint potential trapezoidal integration.
    edge = np.diff(phi)/dx
    return float(0.5*np.sum(edge*edge)*dx + (np.trapezoid(0.25*(phi*phi-1)**2, dx=dx) if include_potential else 0.0))


def roots_linear(x, phi):
    ix = np.flatnonzero(phi[:-1]*phi[1:] < 0.)
    return [float(x[i] - phi[i]*(x[i+1]-x[i])/(phi[i+1]-phi[i])) for i in ix]


def simulate(mode, beta=0, tau=2, dx=0.1, dt=0.001, duration=30,
             potential=True, record_step=1.0, separation=4., mc=0.2):
    xmax=25.; steps=round(duration/dt)
    x=np.linspace(-xmax,xmax,round(2*xmax/dx)+1)
    phi=field_profile(x,mode,separation)
    initial=phi.copy()
    left=-1.; right=+1. if mode=='kink' else -1.
    m=(np.diff(phi)/dx)**2
    result=[]; first_merged=None
    record_every=max(1,round(record_step/dt))
    if dt > dx**2/(2*(1+beta)):
        raise ValueError('Explicit step violates conservative diffusion CFL')
    for k in range(steps+1):
        if k%record_every == 0 or k==steps:
            root=roots_linear(x,phi)
            # kink root at the center is exactly zero on a symmetric grid,
            # hence exact zeros are not counted by strict-sign detector.
            center=float(phi[len(phi)//2]); e=np.diff(phi)/dx
            G=1.+beta*m**4/(mc**4+m**4)
            result.append({
                't':round(k*dt,8),'center_phi':center,
                'pair_separation':root[1]-root[0] if len(root)==2 else None,
                'n_zero_crossings':len(root), 'peak_memory':float(max(m)),
                'peak_modulus':float(max(G)), 'max_abs_gradient':float(max(abs(e))),
                'field_energy_excluding_memory':field_energy(phi,dx,potential),
            })
        if k == steps: break
        strain=np.diff(phi)/dx
        G=1+beta*m**4/(mc**4+m**4)
        flux=G*strain
        force=(flux[1:]-flux[:-1])/dx
        if potential:
            force-=phi[1:-1]*(phi[1:-1]**2-1.)
        phi[1:-1] += dt*force
        phi[0]=left; phi[-1]=right
        m += dt/tau*(strain*strain - m)
        if mode=='bubble' and first_merged is None and phi[len(phi)//2]<=0:
            first_merged=(k+1)*dt
    return {'mode':mode,'beta':beta,'tau':tau,'dx':dx,'dt':dt,
            'duration':duration,'potential':potential,
            'collapse_time':first_merged,'history':result,
            'x':x,'phi':phi,'m':m,'phi_initial':initial}


def write_csv(fname, rows):
    with (HERE/fname).open('w',newline='',encoding='utf-8') as f:
        writer=csv.DictWriter(f,fieldnames=list(rows[0].keys()))
        writer.writeheader(); writer.writerows(rows)


def main():
    # High-precision continuum profile test: phi^4 kink analytic energy.
    fine_x=np.linspace(-35.,35.,70001)
    fine_dx=float(fine_x[1]-fine_x[0])
    phi_k=field_profile(fine_x, 'kink')
    kink_numeric=field_energy(phi_k,fine_dx)
    sep=[2.5,3.,3.5,4.,4.5,5.,6.,7.,8.,10.]
    pair_energies=[]
    for s in sep:
        f=field_profile(fine_x,'bubble',s)
        e=field_energy(f,fine_dx)
        pair_energies.append({'separation':s,'energy':e,
                              'binding_vs_two_kinks':2*M_KINK-e})
    write_csv('delayed_aether_pair_energy.csv',pair_energies)

    # Baseline and hardening experiments.
    specs=[
        ('kink_no_hardening',dict(mode='kink',beta=0,duration=50)),
        ('kink_hardening',dict(mode='kink',beta=2,duration=50)),
        ('pair_no_hardening',dict(mode='bubble',beta=0,duration=15)),
        ('pair_hardening',dict(mode='bubble',beta=2,duration=15)),
        ('kink_hardening_without_doublewell',dict(mode='kink',beta=2,
                                                   duration=100,potential=False)),
        ('pair_no_hardening_refined',dict(mode='bubble',beta=0,
                                       dx=.05,dt=.00025,duration=15)),
        ('pair_hardening_refined',dict(mode='bubble',beta=2,
                                    dx=.05,dt=.00025,duration=15)),
    ]
    outputs={name:simulate(**kwargs) for name,kwargs in specs}
    rows=[]; histories=[]
    for name,r in outputs.items():
        h=r['history'][-1]
        rows.append({'case':name,'dx':r['dx'],'dt':r['dt'],
                     'duration':r['duration'], 'collapse_time':r['collapse_time'],
                     'center_phi':h['center_phi'],
                     'peak_modulus':h['peak_modulus'],
                     'peak_memory':h['peak_memory'],
                     'max_abs_gradient':h['max_abs_gradient'],
                     'field_energy_excluding_memory':h['field_energy_excluding_memory']})
        for rec in r['history']:
            histories.append({'case':name,**rec})
    write_csv('delayed_aether_summary.csv',rows)
    write_csv('delayed_aether_history.csv',histories)

    # Data visualization (plain matplotlib, default colors/styles).
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    fig,ax=plt.subplots(figsize=(8,4.5))
    ax.plot([r['separation'] for r in pair_energies],
            [r['energy'] for r in pair_energies],'.-',label='Pair profile energy')
    ax.axhline(2*M_KINK,linestyle='--',label='Twice the isolated kink energy')
    ax.set(xlabel='Separation R (dimensionless)',ylabel='Field energy',
           title='Attraction in a one-dimensional double-well toy model')
    ax.legend();fig.tight_layout();fig.savefig(HERE/'delayed_aether_pair_energy.png',dpi=180);plt.close(fig)

    fig,ax=plt.subplots(figsize=(8,4.5))
    for name,label in [('pair_no_hardening','No hardening (beta=0)'),
                       ('pair_hardening','Memory-dependent hardening (beta=2)')]:
        hist=outputs[name]['history']
        ax.plot([r['t'] for r in hist],[r['center_phi'] for r in hist],label=label)
    ax.axhline(0,linestyle='--',label='Two-zero-crossing merger threshold')
    ax.set(xlabel='Relaxation time (dimensionless)',ylabel='Field at the center',
           title='Kink–antikink region disappears; hardening is not stabilizing')
    ax.legend();fig.tight_layout();fig.savefig(HERE/'delayed_aether_pair_dynamics.png',dpi=180);plt.close(fig)

    out={'parameters':{'memory_time_tau':2.,'hardening_threshold_mc':.2,
                        'hardening_power':4,'x_domain':[-25,25],
                        'pair_initial_separation':4.},
         'analytic_isolated_kink_energy':M_KINK,
         'numeric_isolated_kink_energy':kink_numeric,
         'numeric_minus_analytic':kink_numeric-M_KINK,
         'pair_profile_energies':pair_energies,
         'runs':rows}
    (HERE/'delayed_aether_results.json').write_text(json.dumps(out,indent=2,ensure_ascii=False),encoding='utf-8')
    print(json.dumps(out,indent=2,ensure_ascii=False))


if __name__=='__main__': main()
