#!/usr/bin/env python3
"""Driven geometric memory: source is explicitly imposed, no backreaction claimed."""
import csv,json
import numpy as np
from pathlib import Path
from verify_v11 import make_mesh,hedgehog,source_texture,degree_preimage,unique_edges,metric_geometry
ROOT=Path(__file__).resolve().parent

def centroid_x(coords,weights):
    s=np.sum(weights)
    return float((coords[:,0]@weights)/s) if s else 0.


def main():
    n=12
    coords,tets=make_mesh(n)
    edges,inv=unique_edges(tets)
    alpha=.06;dt=.05;T_move=4.;T=8.;k0=.8;delta=3.;width=.012
    def phi(y):return .5*(k0+delta)*y*y-delta*width*width*np.log(np.cosh(y/width))
    def phi_prime(y):return (k0+delta)*y-delta*width*np.tanh(y/width)
    rows=[]; audit=[]
    for tau in (.2,.8):
        c0=np.array([-.20,.03,-.03])
        q=hedgehog(coords,center=c0,radius=.62)
        s=source_texture(coords,n,q)
        sigma=alpha*s.copy()
        prev_target=alpha*s.copy()
        cumulative_work=0.;cumulative_diss=0.
        for step in range(int(T/dt)+1):
            t=step*dt
            center=c0+np.array([.4*min(t/T_move,1.),0,0])
            q=hedgehog(coords,center=center,radius=.62)
            target=alpha*source_texture(coords,n,q)
            if step>0:
                before_work=float(np.sum(phi(prev_target-sigma)))
                after_work=float(np.sum(phi(target-sigma)))
                cumulative_work+=after_work-before_work
                sig_old=sigma.copy()
                sigma=sigma+(dt/(k0*tau))*phi_prime(target-sigma)
                after_relax=float(np.sum(phi(target-sigma)))
                loss=after_work-after_relax
                assert loss>=-1e-12  # conditional dissipation at frozen source
                cumulative_diss+=max(loss,0.)
            prev_target=target
            y=target-sigma
            maxK=float(k0+delta*np.max(np.tanh(y/width)**2))
            rec={'tau':tau,'time':round(t,5),'center_x':float(center[0]),
                 'source_centroid_x':centroid_x(coords,target),
                 'metric_centroid_x':centroid_x(coords,sigma),
                 'lag_l2':float(np.linalg.norm(y)/np.sqrt(len(y))),
                 'max_tangent_stiffness':maxK,
                 'source_max':float(target.max()),'metric_max':float(sigma.max()),
                 'memory_energy':float(np.sum(phi(y))),
                 'external_work':cumulative_work,'dissipation':cumulative_diss,
                 'energy_balance_error':abs(float(np.sum(phi(y)))-(cumulative_work-cumulative_diss))}
            if step%20==0 or step==int(T/dt):
                rec['topological_charge']=-degree_preimage(coords,tets,q)
                geom=metric_geometry(coords,tets,edges,inv,sigma)
                rec['curvature_proxy_core']=geom['regge_scalar_proxy_core']
                rec['max_deficit']=geom['max_flat_residual']
                assert geom['min_gram_eigenvalue']>0
                assert rec['topological_charge']==1
                audit.append(rec)
            rows.append(rec)
        # At late time the geometry should approach static source with no hardening.
        assert rows[-1]['lag_l2']<.0005
        assert max(r['energy_balance_error'] for r in rows if r['tau']==tau)<1e-8
    with (ROOT/'memory_dynamics.csv').open('w',newline='') as f:
        keys=['tau','time','center_x','source_centroid_x','metric_centroid_x','lag_l2',
              'max_tangent_stiffness','source_max','metric_max','topological_charge','curvature_proxy_core','max_deficit','memory_energy','external_work','dissipation','energy_balance_error']
        w=csv.DictWriter(f,fieldnames=keys);w.writeheader()
        for r in rows:w.writerow(r)
    (ROOT/'memory_audit.json').write_text(json.dumps(audit,indent=2,ensure_ascii=False),encoding='utf8')
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    fig,axs=plt.subplots(2,1,figsize=(7.8,6.2),sharex=True)
    for tau in (.2,.8):
        rr=[r for r in rows if r['tau']==tau]
        t=[r['time'] for r in rr]
        axs[0].plot(t,[r['source_centroid_x']-r['metric_centroid_x'] for r in rr],label=f'tau={tau}')
        axs[1].plot(t,[r['max_tangent_stiffness'] for r in rr],label=f'tau={tau}')
    axs[0].set(ylabel='source minus geometry centroid',title='Dissipative geometric memory follows a moving topological core')
    axs[1].set(ylabel='max effective stiffness',xlabel='time (prescribed driving)')
    axs[1].axvline(T_move,color='gray',ls='--',alpha=.6,label='core stops')
    for ax in axs:ax.legend(fontsize=8);ax.grid(alpha=.25)
    fig.tight_layout();fig.savefig(ROOT/'memory_lag.png',dpi=160);plt.close(fig)
    print(json.dumps({'audit_samples':len(audit),
                      'max_stiffness_by_tau':{str(tau):max(r['max_tangent_stiffness'] for r in rows if r['tau']==tau) for tau in (.2,.8)},
                      'final_lag_by_tau':{str(tau):[r for r in rows if r['tau']==tau][-1]['lag_l2'] for tau in (.2,.8)}},indent=2))

if __name__=='__main__':main()
