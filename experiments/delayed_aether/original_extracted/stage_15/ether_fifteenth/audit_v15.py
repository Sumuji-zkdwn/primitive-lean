"""External checks against the CSV and JSON outputs, separate from simulations."""
from pathlib import Path
import csv,json
p=Path(__file__).parent
load=lambda fn: list(csv.DictReader((p/fn).open()))
rs=load('graph_constraints.csv');k=load('kasner_benchmark.csv');iv=load('kasner_IVP_convergence.csv')
checked={}
for t in ('0.0','0.37','0.91'):
    group=[r for r in rs if r['t']==t]
    assert len(group)==4
    for name in ('H','M','gamma_evo','K_evo'):
        ys=[float(r[name]) for r in group]
        ratios=[ys[i]/ys[i+1] for i in range(len(ys)-1)]
        assert 3.5<ratios[-1]<4.4, (t,name,ratios)
    checked['convergence_t'+t]=True
last=[r for r in rs if r['t']=='0.37' and r['n']=='192'][0]
assert float(last['exact_R'])>.2
assert float(last['metric_shear_component'])>.02
assert float(last['min_metric_eig'])>.7
assert float(last['H'])<.001 and float(last['M'])<.001
assert float(last['naive_memory_H'])>.10 and float(last['naive_memory_M'])>.004
checked['inhomogeneous_curvature_nonzero']=True
checked['memory_violation_persists']=True
assert max(float(r['Hamiltonian']) for r in k)<1e-13
assert max(float(r['K_evolution']) for r in k)<1e-13
assert max(float(r['log_metric_err']) for r in k)<1e-13
assert min(float(r['min_metric_eig']) for r in k)>0
assert max(float(r['shear']) for r in k)>.7
checked['Kasner_exact_nonlinear_equations']=True
err=[float(r['maxH']) for r in iv]
ratios=[err[i]/err[i+1] for i in range(len(err)-1)]
assert min(ratios)>14,ratios
assert err[-1]<3e-9
assert min(float(r['min_g_eig']) for r in iv)>0
checked['Kasner_IVP_RK4_order4']=True
cov=json.loads((p/'conserved_memory_v15.json').read_text())
assert cov['energy_momentum_divergence_symbolic']==['0','0']
assert cov['max_variation_total_energy_over_time']<1e-12
checked['covariant_matter_stress_conservation']=True
result={'status':'PASS','checked':checked,'RK4_H_reduction':ratios,'finest_graph_H':float(last['H']),'finest_graph_M':float(last['M']),'naive_memory_H':float(last['naive_memory_H']),'naive_memory_M':float(last['naive_memory_M']),'warnings':['Exact vacuum GR used as benchmark; no emergence shown','Nonzero 3D curvature on graph slices of globally flat Minkowski is not gravity','Naive memory term is intentionally off-shell and has no corresponding matter stress','Homogeneous Kasner IVP only; inhomogeneous graph data sampled from analytic exact family','No standalone matter+gravity+memory constrained evolution']}
(p/'independent_audit_v15.json').write_text(json.dumps(result,ensure_ascii=False,indent=2),encoding='utf-8')
print(json.dumps(result,ensure_ascii=False,indent=2))
