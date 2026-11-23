#!/usr/bin/env python3
"""Independent consistency and failure-mode audit for v12."""
from pathlib import Path
import json, numpy as np
from verify_v12 import Model, simulate
ROOT=Path(__file__).resolve().parent

def load(label):return json.loads((ROOT/(label+'_audit.json')).read_text())
def assert_le(a,b,reason):
 if a>b: raise AssertionError((reason,a,b))

def main():
 M=Model(n=8,gamma=0)
 initial=M.prepare()
 state=tuple(a.copy() for a in initial)
 for j in range(12):state=M.step(state,.001)
 for j in range(12):state=M.step(state,-.001)
 rev=max(float(np.max(np.abs(x-y))) for x,y in zip(state,initial))
 assert_le(rev,1e-10,'time reversibility')
 main=load('finite_n12');small=load('fine_dt_n12');c=load('control_n12')
 checks=[load('finite_n12'),load('finite_n16'),load('finite_n20')]
 for item in checks:
   assert item['degree_initial']==1 and item['degree_final']==1 and item['charge_observations']==[1]
   assert item['metric']['min_gram_eigenvalue']>0
   assert item['metric']['max_deficit']>0.02
   assert item['max_memory_modulus']>0.55
   assert_le(item['max_norm_error'],1e-9,'norm constraint')
   assert_le(item['max_tangent_error'],1e-8,'tangent constraint')
   assert_le(max(v['relative_error'] for v in item['gradient_audit'].values()),1e-7,'variational gradients')
 assert c['max_b']==0
 assert c['metric']['max_deficit']<1e-10
 ratio=main['max_abs_energy_balance_error']/small['max_abs_energy_balance_error']
 if not (3.5<ratio<4.5):raise AssertionError(('time convergence ratio',ratio))
 protected=load('protected_long_n12');protected16=load('protected_long_n16')
 prot_coarse=load('protected_convergence_coarse');prot_fine=load('protected_convergence_fine')
 for row in (protected,protected16,prot_coarse,prot_fine):
    assert row['degree_final']==1 and row['charge_observations']==[1]
    assert row['minimum_edge_dot']>0
    lower=row['s_cut']/(1+np.sqrt(row['initial_energy']/row['admissibility_barrier']))
    assert row['minimum_edge_dot']>=lower
    assert row['metric']['min_gram_eigenvalue']>0
    assert_le(max(v['relative_error'] for v in row['gradient_audit'].values()),1e-7,'barrier gradients')
 barrier_ratio=prot_coarse['max_abs_energy_balance_error']/prot_fine['max_abs_energy_balance_error']
 if not (3<barrier_ratio<5):raise AssertionError(('protected convergence',barrier_ratio))
 slip=json.loads((ROOT/'topology_slip_witness.json').read_text())
 assert slip['charge_pre']==1 and slip['charge_post']==0
 assert slip['witness_count']>0
 for v in slip['witnesses']:
    assert abs(sum(v['barycentric'])-1)<1e-10
    assert min(v['barycentric'])>0
    assert_le(v['residual'],1e-12,'tetra singularity')
 # Compare q trajectories rather than only their geometric observables.
 Mc=Model(n=12,coupled=True); M0=Model(n=12,coupled=False)
 sc,rc=simulate(Mc,.002,.24,60)
 su,ru=simulate(M0,.002,.24,60)
 qdiff=float(np.sqrt(np.mean(np.sum((sc[0]-su[0])**2,axis=-1))))
 if qdiff<1.e-7:raise AssertionError(('coupling has no effect',qdiff))
 q0=sc[0];b=sc[1];z=sc[2]
 np.savez_compressed(ROOT/'coupled_snapshot_n12_t024.npz',q=q0,b=b,z=z,grid_n=12,
                     dx=Mc.dx,time=.24)
 audit={'reversibility_max_abs_error':rev,
        'energy_balance_error_ratio_dt_vs_half':ratio,
        'q_coupled_vs_control_rms_final':qdiff,
        'coupled_topological_degree_t024':Mc.degree(q0),
        'control_topological_degree_t024':M0.degree(su[0]),
        'coupled_final_b_max_abs':float(np.max(np.abs(b))),
        'control_final_b_max_abs':float(np.max(np.abs(su[1]))),
        'max_q_norm_error_t024':float(np.max(np.abs(np.sum(q0*q0,axis=-1)-1))),
        'topological_slip_time_bracket':[slip['time_pre'],slip['time_post']],
        'topological_slip_witness_residual':slip['witnesses'][0]['residual'],
        'protected_n12_final_charge_t060':protected['degree_final'],
        'protected_n12_min_edge_dot':protected['minimum_edge_dot'],
        'protected_n12_rigorous_lower_bound':protected['s_cut']/(1+np.sqrt(protected['initial_energy']/protected['admissibility_barrier'])),
        'protected_n16_final_charge_t045':protected16['degree_final'],
        'protected_convergence_ratio':barrier_ratio,
        'resolution_audits':{str(a['grid_n']):{'degree':a['degree_final'],
                    'metric_curvature_max_abs':a['metric']['max_deficit'],
                    'maximum_local_memory_modulus':a['max_memory_modulus'],
                    'maximum_energy_balance_relative_error':a['max_abs_energy_balance_error']}
                    for a in checks},
        'classification':'Self-coupled finite-dimensional model, not GR. Unprotected lattice exhibits charge slip; added local barrier proves topological preservation in the ideal ODE.'}
 (ROOT/'audit_v12.json').write_text(json.dumps(audit,indent=2,ensure_ascii=False))
 print(json.dumps(audit,indent=2,ensure_ascii=False))

if __name__=='__main__':main()
