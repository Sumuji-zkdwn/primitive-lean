"""V9 Regge–memory–SO(3) toy verifications. Python >=3.10; numpy, matplotlib."""
from pathlib import Path
import json, csv, hashlib
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import regge_v9 as R
import gauge_memory_v9 as G
import geometry_memory_v9 as M

HERE=Path(__file__).resolve().parent
rng=np.random.default_rng(20261122)


def eigen_report():
    r0=R.BASE.copy();r1=r0.copy();r1[0]*=1.08
    J0=R.J(r0,1e-5);J1=R.J(r1,1e-5)
    D=np.array([-v / np.linalg.norm(v) for v in R.OUT])
    # exact rank/J0 = 3 ones verified via finite differences.
    flat=R.deficit(r0);curve=R.deficit(r1)
    samples=[]
    max_flat=0.;max_curved_shift=0.
    for n in range(256):
        vec=rng.normal(size=3);vec=vec/np.linalg.norm(vec)*rng.uniform(0,.25)
        nr=np.linalg.norm(R.OUT-vec[None,:],axis=1)
        max_flat=max(max_flat,max(abs(R.deficit(nr))))
        naive=r1+(nr-r0)
        max_curved_shift=max(max_curved_shift,max(abs(R.deficit(naive)-curve)))
        samples.append([n,*vec,max(abs(R.deficit(nr))),max(abs(R.deficit(naive)-curve))])
    np.savetxt(HERE/'vertex_shift_tests.csv',samples,delimiter=',',comments='',header='trial,x,y,z,flat_max_deficit,curved_naive_deficit_change')
    gr=np.array([(R.action(r1+np.eye(4)[i]*1e-5)-R.action(r1-np.eye(4)[i]*1e-5))/(2e-5) for i in range(4)])
    summary={'num_tetrahedra':len(R.TETS),'interior_edges':4,'boundary_edges':6,
        'flat_curvature_max':float(max(abs(flat))),
        'flat_jacobian_vs_all_threes':float(np.max(np.abs(J0-3))),
        'flat_eigenvalues':np.linalg.eigvalsh(J0).tolist(),
        'flat_translation_kernel_residual':float(np.max(np.abs(J0@D))),
        'curved_radius_change_percent':8.,
        'curved_deficits_rad':curve.tolist(),
        'curved_eigenvalues':np.linalg.eigvalsh((J1+J1.T)*.5).tolist(),
        'curved_symmetry_residual':float(np.max(np.abs(J1-J1.T))),
        'regge_action_gradient_error':float(max(abs(gr-curve))),
        'flat_vertex_move_trials':len(samples),
        'max_flat_vertex_shift_deficit':max_flat,
        'max_naive_curved_shift_deficit_change':max_curved_shift,
        'warning':'curved configuration is off-shell; NOT a proof of loss of diffeomorphism invariance on curved solutions'}
    plt.figure(figsize=(7,4.1))
    for lab,js in [('flat',J0),('8% intrinsic length change',J1)]:
        plt.plot(range(1,5),np.linalg.eigvalsh((js+js.T)/2),marker='o',label=lab)
    plt.axhline(0,linewidth=.8,linestyle='--')
    plt.xticks([1,2,3,4]);plt.xlabel('Eigenvalue index');plt.ylabel('Eigenvalue of deficit response matrix')
    plt.legend();plt.tight_layout();plt.savefig(HERE/'regge_symmetry_spectrum.png',dpi=180);plt.close()
    return summary

def group_report():
    maxE=0.;maxF=0.;maxM=0.;maxgrad=0.;maxstepL=0.;maxstepM=0.;maxorth=0.
    for it in range(128):
        U={e:G.rot(rng.normal(size=3)*rng.uniform(.05,1.1)) for e in G.EDGES}
        Mem={f:rng.normal(size=3)*rng.uniform(.05,.5) for f in G.FACES}
        gauges={i:G.rot(rng.normal(size=3)*1.6) for i in range(5)}
        U2,M2=G.transformed(U,Mem,gauges)
        maxE=max(maxE,abs(G.energy(U,Mem)[0]-G.energy(U2,M2)[0]))
        for f in G.FACES:
            maxF=max(maxF,np.linalg.norm(G.F_vector(U2,f)-gauges[f[0]]@G.F_vector(U,f)))
            maxM=max(maxM,abs(np.linalg.norm(G.F_vector(U,f)-Mem[f])-np.linalg.norm(G.F_vector(U2,f)-M2[f])))
        grad=G.gradients(U,Mem);grad2=G.gradients(U2,M2)
        maxgrad=max(maxgrad,max(np.linalg.norm(grad2[e]-gauges[e[0]]@grad[e]) for e in G.EDGES))
        dt=.015;lam=.19
        unext={e:G.rot(-dt*grad[e])@U[e] for e in G.EDGES}
        unext2={e:G.rot(-dt*grad2[e])@U2[e] for e in G.EDGES}
        mnext={f:(1-lam)*Mem[f]+lam*G.F_vector(unext,f) for f in G.FACES}
        mnext2={f:(1-lam)*M2[f]+lam*G.F_vector(unext2,f) for f in G.FACES}
        maxstepL=max(maxstepL,max(np.linalg.norm(unext2[e]-gauges[e[0]]@unext[e]@gauges[e[1]].T) for e in G.EDGES))
        maxstepM=max(maxstepM,max(np.linalg.norm(mnext2[f]-gauges[f[0]]@mnext[f]) for f in G.FACES))
        maxorth=max(maxorth,max(np.linalg.norm(unext[e].T@unext[e]-np.eye(3)) for e in G.EDGES))
    data={}
    for rate in [.05,.12,.3]:
        out,_,_=G.run(np.random.default_rng(1122),steps=90,rate=rate)
        label=str(rate).replace('.','p')
        np.savetxt(HERE/f'gauge_memory_rate_{label}.csv',out,delimiter=',',comments='',header='step,energy,wilson_energy,memory_energy,max_gap,max_stiffness')
        data[str(rate)]={'initial_energy':float(out[0,1]),'final_energy':float(out[-1,1]),'max_hardening':float(max(out[:,5])), 'end_stiffness':float(out[-1,5]),'energy_rises':int(np.sum(np.diff(out[:,1])>1e-11))}
    return {'num_vertices':5,'num_edges':len(G.EDGES),'num_faces':len(G.FACES),'gauge_random_trials':128,
            'energy_invariance_abs_max':maxE,'curvature_covariance_L2_max':maxF,
            'memory_gap_invariance_max':maxM,'gradient_covariance_max':maxgrad,
            'one_step_link_covariance_max':maxstepL,'one_step_memory_covariance_max':maxstepM,
            'orthogonality_error_max':maxorth,'rates':data,
            'interpretation':'exact internal SO(3) frame symmetry; NOT discrete spacetime diffeomorphisms'}

def geo_memory_report():
    out=M.simulate(n=240)
    coarse=M.simulate(n=120,eta=.014,gamma=.12)
    fine=M.simulate(n=480,eta=.0035,gamma=.03)
    # same duration in gradient time, different resolutions; optional coarse may be stable
    np.savetxt(HERE/'geometry_memory_timeseries.csv',out,delimiter=',',header='step,energy,curvature_l2,max_curvature,memory_gap_l2,max_stiffness,r0,r1,r2,r3',comments='')
    np.savetxt(HERE/'geometry_memory_fine.csv',fine,delimiter=',',header='step,energy,curvature_l2,max_curvature,memory_gap_l2,max_stiffness,r0,r1,r2,r3',comments='')
    return {'steps':240,'initial_energy':float(out[0,1]),'final_energy':float(out[-1,1]),
            'initial_max_curvature':float(out[0,3]),'final_max_curvature':float(out[-1,3]),
            'max_hardness_initial':float(out[0,5]), 'max_hardness_final':float(out[-1,5]),
            'energy_upward_steps':int(np.sum(np.diff(out[:,1])>1e-12)),
            'fine_steps':480,'fine_final_energy':float(fine[-1,1]),'fine_final_max_curvature':float(fine[-1,3]),
            'coarse_final_energy':float(coarse[-1,1]),'coarse_final_max_curvature':float(coarse[-1,3]),
            'phi_is_nonnegative_analytic':True,
            'theoretical_dissipation':'for continuous rdot=-eta grad_r H, mdot=-gamma grad_m H, dH/dt=-eta|grad_r H|^2-gamma|grad_m H|^2 <=0',
            'caveat':'dissipative smoothing of intrinsic curvature, not Lorentz-covariant causal gravitational dynamics'}

def visuals():
    out=np.genfromtxt(HERE/'geometry_memory_timeseries.csv',delimiter=',',names=True)
    fig,axs=plt.subplots(3,1,figsize=(7,8),sharex=True)
    axs[0].semilogy(out['step'],out['energy']);axs[0].set_ylabel('Positive energy')
    axs[1].semilogy(out['step'],out['max_curvature']);axs[1].set_ylabel('Maximum deficit (rad)')
    axs[2].plot(out['step'],out['max_stiffness']);axs[2].set_ylabel('Max memory stiffness');axs[2].set_xlabel('Update steps')
    fig.tight_layout();fig.savefig(HERE/'regge_memory_relaxation.png',dpi=170);plt.close(fig)
    fig,axs=plt.subplots(2,1,figsize=(7,6),sharex=True)
    for rate in [.05,.12,.3]:
        ar=np.genfromtxt(HERE/f'gauge_memory_rate_{str(rate).replace(".","p")}.csv',delimiter=',',names=True)
        axs[0].semilogy(ar['step'],ar['energy'],label=f'rate {rate}')
        axs[1].plot(ar['step'],ar['max_stiffness'],label=f'rate {rate}')
    axs[0].set_ylabel('Gauge + memory energy')
    axs[1].set_xlabel('Update steps');axs[1].set_ylabel('Maximum hardening coefficient')
    axs[0].legend();axs[1].legend();fig.tight_layout();fig.savefig(HERE/'nonlinear_gauge_memory.png',dpi=170);plt.close(fig)

if __name__=='__main__':
    data={'model':'V9 finite tetrahedral Regge plus two memory tests','date':'2026-11-22','regge':eigen_report(),'so3_gauge':group_report(),'regge_memory':geo_memory_report()}
    visuals()
    (HERE/'audit_v9.json').write_text(json.dumps(data,ensure_ascii=False,indent=2))
    print(json.dumps(data,indent=2))
