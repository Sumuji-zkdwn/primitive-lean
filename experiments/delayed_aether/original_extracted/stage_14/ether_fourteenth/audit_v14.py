#!/usr/bin/env python3
"""Independent spot checks of v14 model. Does not substitute for a proof of GR."""
import json
from pathlib import Path
import numpy as np
from scipy.linalg import expm
from verify_v14 import spd_exp_and_frechet_pullback, sym, finite_tetra_counterexample

HERE=Path(__file__).resolve().parent
rng=np.random.default_rng(140022)
errors=[]
for i in range(80):
    B=sym(rng.normal(size=(3,3)))*.65
    H=sym(rng.normal(size=(3,3)))
    G=sym(rng.normal(size=(3,3)))
    _,_,_,back=spd_exp_and_frechet_pullback(B,G)
    eps=2e-6
    measured=np.sum(G*(expm(B+eps*H)-expm(B-eps*H)))/(2*eps)
    predicted=np.sum(back*H)
    errors.append(float(abs(measured-predicted)))
audit=json.loads((HERE/'audit_v14.json').read_text())
coarse=audit['exp_n10_dt0p002']['max_abs_energy_budget']
import csv
rows=list(csv.DictReader((HERE/'exp_n10_dt0p001.csv').open()))
fine=max(abs(float(r['relative_energy_budget'])) for r in rows)
ratio=coarse/fine
assert max(errors)<5e-9, max(errors)
assert 3.5<ratio<4.5, ratio
assert finite_tetra_counterexample()['triangle_inequality_gap']<0
for key in ('exp_n10_dt0p002','exp_n12_dt0p002'):
    r=audit[key]
    assert r['initial_degree']==r['final_degree']==1
    assert r['min_stepwise_certificate']>0
    assert r['uniform_sufficiency_verified_at_saved_times']
    assert r['final_regge']['min_tet_gram_eig']>0
report={'status':'PASS','random_frechet_trials':len(errors),
   'max_frechet_adjoint_abs_error':max(errors),
   'dt_refinement_energy_budget_ratio_n10':ratio,
   'n10_n12_topology_certified_on_computed_intervals':True,
   'simplex_geometric_guarantee_on_all_stepwise_paths':True,
   'limitation':'Checks do not prove unconstrained all-time dynamics or Einstein constraints.'}
(HERE/'independent_audit_v14.json').write_text(json.dumps(report,indent=2,ensure_ascii=False))
print(json.dumps(report,indent=2))
