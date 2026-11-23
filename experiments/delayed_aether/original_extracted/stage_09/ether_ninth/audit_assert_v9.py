"""Independent threshold assertions against fresh finite numerical checks (not proof of GR)."""
import json
from pathlib import Path
import numpy as np

P=Path(__file__).resolve().parent
a=json.loads((P/'audit_v9.json').read_text())
r=a['regge'];g=a['so3_gauge'];m=a['regge_memory']
assert r['num_tetrahedra']==4 and r['interior_edges']==4
assert r['flat_curvature_max']<1e-12
assert r['flat_jacobian_vs_all_threes']<1e-7
assert max(abs(x) for x in r['flat_eigenvalues'][:3])<1e-7
assert abs(r['flat_eigenvalues'][3]-12)<1e-7
assert min(abs(x) for x in r['curved_eigenvalues'])>.1
assert r['regge_action_gradient_error']<1e-7
assert r['max_flat_vertex_shift_deficit']<1e-12
assert r['max_naive_curved_shift_deficit_change']>.01
for key in ['energy_invariance_abs_max','curvature_covariance_L2_max','memory_gap_invariance_max','gradient_covariance_max','one_step_link_covariance_max','one_step_memory_covariance_max','orthogonality_error_max']:
    assert g[key]<1e-10,(key,g[key])
assert all(x['energy_rises']==0 for x in g['rates'].values())
assert m['energy_upward_steps']==0 and m['final_energy']<m['initial_energy']/1e4
assert m['final_max_curvature']<m['initial_max_curvature']/100
for x in ['geometry_memory_timeseries.csv','geometry_memory_fine.csv']:
    a=np.genfromtxt(P/x,delimiter=',',names=True)
    assert (a['energy']>=-1e-12).all()
    assert (np.diff(a['energy'])<=1e-10).all()
    assert (a['max_stiffness']>=.8-1e-12).all()
    assert (a['max_stiffness']<=3.8+1e-12).all()
for x in ['gauge_memory_rate_0p05.csv','gauge_memory_rate_0p12.csv','gauge_memory_rate_0p3.csv']:
    a=np.genfromtxt(P/x,delimiter=',',names=True)
    assert (np.diff(a['energy'])<=1e-10).all()
    assert (a['max_stiffness']>=1-1e-12).all()
    assert (a['max_stiffness']<=4+1e-12).all()
print('PASS: Regge rank and gradient, exact local SO(3) checks, and all monotonic numerical energy tests')
