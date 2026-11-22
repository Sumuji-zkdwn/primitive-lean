#!/usr/bin/env python3
"""Generate standalone figures and CSV for a reproducible gravitating-model audit."""
import json, csv, sys
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from verify_v17 import run

OUT=Path(__file__).resolve().parent


def make():
    fine=[]
    for n in [64,96,144,192,288]:
        m,s,d,v=run(n=n,G=.002,T=.9,dt=.015)
        fine.append(v)
    with (OUT/'spatial_convergence.csv').open('w',newline='') as file:
        w=csv.DictWriter(file,fieldnames=list(fine[0].keys()));w.writeheader();w.writerows(fine)
    n=np.array([x['n'] for x in fine]); mom=np.array([x['independent_momentum_residual_rel_l2'] for x in fine]); mass=np.array([x['max_relative_total_mass_drift'] for x in fine]); H=np.array([x['max_radial_hamiltonian_residual'] for x in fine]);
    fig,ax=plt.subplots(figsize=(7.1,4.7)); ax.loglog(n,mom,'o-',label='Independent momentum evolution residual');ax.loglog(n,H,'s-',label='Hamiltonian radial residual');ax.loglog(n,mass,'^-',label='Relative ADM-mass drift')
    ax.loglog(n,mom[-1]*(n[-1]/n)**2,linestyle='--',label='Second-order reference')
    ax.set(xlabel='Radial grid intervals N',ylabel='Relative error',title='Constraint and conservation convergence (G = 0.002, t = 0.9)');ax.legend(fontsize=8);ax.grid(alpha=.25);fig.tight_layout();fig.savefig(OUT/'constraint_convergence_v17.png',dpi=180);plt.close(fig)

    m0,sol0,d0,s0=run(n=192,G=0.,T=.9,dt=.015)
    m1,sol1,d1,s1=run(n=192,G=.00065,T=.9,dt=.015)
    m2,sol2,d2,s2=run(n=192,G=.002,T=.9,dt=.015)
    te=sol2.t
    with (OUT/'dynamic_gravity_timeseries.csv').open('w',newline='') as f:
        writer=csv.writer(f)
        writer.writerow(['time','lapse_center_G00065','lapse_center_G002','areal_mass_at_r2_G002',
                         'ADM_mass_G002','max_memory_A_G002','max_lag_G002','r2_mass_G00065'])
        for i,t in enumerate(te):
            writer.writerow([t,d1[i]['center_lapse'],d2[i]['center_lapse'],d2[i]['radial_mass_center'],d2[i]['total_mass'],d2[i]['max_hardening'],d2[i]['max_memory_lag'],d1[i]['radial_mass_center']])
    fig,ax=plt.subplots(figsize=(7.1,4.4));ax.plot(te,[d1[i]['center_lapse'] for i in range(len(te))],label='G = 0.00065');ax.plot(te,[d2[i]['center_lapse'] for i in range(len(te))],label='G = 0.002');ax.set(xlabel='Model time',ylabel='Central lapse alpha(t,0)',title='Gravitational time factor evolves with moving matter');ax.grid(alpha=.25);ax.legend();fig.tight_layout();fig.savefig(OUT/'dynamic_lapse_v17.png',dpi=180);plt.close(fig)
    fig,ax=plt.subplots(figsize=(7.1,4.4));r=m2.r
    for j in [0,len(te)//2,len(te)-1]:
        f=m2.full(*m2.unpack(sol2.y[:,j])[:2])[0]
        ax.plot(r,f,label=f't={te[j]:.3f}')
    ax.set_xlim(0,7);ax.set(xlabel='Areal radius r',ylabel='Hedgehog profile f(r,t)',title='Self-evolving topological profile, G=0.002');ax.legend();ax.grid(alpha=.25);fig.tight_layout();fig.savefig(OUT/'hedgehog_evolution_v17.png',dpi=180);plt.close(fig)
    fig,ax=plt.subplots(figsize=(7.1,4.4));ax.plot(te,[d2[i]['max_hardening'] for i in range(len(te))],label='Max A(chi-cos f)');ax.plot(te,[d1[i]['max_hardening'] for i in range(len(te))],label='G = 0.00065');ax.set(xlabel='Model time',ylabel='Memory-dependent response coefficient A',title='Temporary hardening in coupled motion');ax.legend();ax.grid(alpha=.25);fig.tight_layout();fig.savefig(OUT/'memory_hardening_v17.png',dpi=180);plt.close(fig)
    fig,ax=plt.subplots(figsize=(7.1,4.4));ax.plot(te,[d2[i]['radial_mass_center']-d2[0]['radial_mass_center'] for i in range(len(te))],label='Mass inside r=2')
    ax.plot(te,[d2[i]['total_mass']-d2[0]['total_mass'] for i in range(len(te))],label='Total ADM mass (numerical drift)')
    ax.set(xlabel='Model time',ylabel='Change in mass aspect m',title='Redistribution inside a sphere vs global conservation');ax.legend();ax.grid(alpha=.25);fig.tight_layout();fig.savefig(OUT/'mass_transport_v17.png',dpi=180);plt.close(fig)
    data={'long_runs':[s0,s1,s2],'G002_spatial_refinement':fine}
    (OUT/'extended_summary.json').write_text(json.dumps(data,indent=2)+'\n')
    print('figures saved. max compactness=',s2['max_compactness'],'lapse change=',s2['center_lapse_change'],'momentum residual=',s2['independent_momentum_residual_rel_l2'])

if __name__=='__main__':make()
