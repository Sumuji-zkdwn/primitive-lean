#!/usr/bin/env python3
"""Independent checks against the saved output of verify_v13.py, plot_v13.py."""
import csv,json,math,hashlib
from pathlib import Path
import numpy as np
P=Path(__file__).resolve().parent
r=json.loads((P/'audit_v13.json').read_text())
c=json.loads((P/'extra_controls.json').read_text())

def assert_ok(cond,label):
    if not cond:raise AssertionError(label)
    print('PASS',label)

for n in (8,12):
    t=r[f'topology_{n}']
    assert_ok(t['degree_initial']==1 and t['degree_final']==0,f'continuous nodal contraction changes degree on n={n}')
    wit=t['witness']
    assert_ok(min(wit['barycentric'])>0 and abs(sum(wit['barycentric'])-1)<1e-12 and wit['zero_residual']<1e-12, f'singular affine tetra witness n={n}')
for key in ['full_n8_dt0p002','full_n8_dt0p001','full_n12_dt0p002','trace_n8_dt0p002']:
    a=r[key]
    assert_ok(max(v['abs_error'] for v in a['grad_checks'].values())<1e-8, key+' energy derivative check')
    assert_ok(a['last']['charge']==1 and a['minimum_charge']==1,key+' short-time topology')
    assert_ok(a['geometry']['min_vertex_metric_eig']>0 and a['geometry']['min_tet_gram_eig']>0,key+' realized positive 3D geometry')
    assert_ok(a['maximum_abs_energy_balance_error']<2e-5,key+' energy budget')
assert_ok(r['full_n8_dt0p002']['last']['shear_norm_max']>.02,'nonzero full-metric shear')
assert_ok(r['trace_n8_dt0p002']['last']['shear_norm_max']<1e-13,'trace-only shear identically zero')
assert_ok(c['uncoupled']['geometry']['max_regge_deficit']<1e-10,'decoupled metric stays flat')
assert_ok(c['zero_kick']['last']['shear_norm_max']>.02,'no initial q velocity still induces shear')
ratio=r['full_n8_dt0p002']['maximum_abs_energy_balance_error']/r['full_n8_dt0p001']['maximum_abs_energy_balance_error']
assert_ok(3.9<ratio<4.1,'second-order time-step energy budget convergence')
assert_ok(c['full_long']['unique_charges']==[1] and c['full_long']['geometry']['min_tet_gram_eig']>0,'t=.2 remains admissible in this sample')
for n in ('contract_n8.csv','contract_n12.csv','full_n8_dt0p002.csv','full_n8_dt0p001.csv','full_n12_dt0p002.csv','trace_n8_dt0p002.csv'):
    assert_ok((P/n).exists() and (P/n).stat().st_size>50,n+' file exists')
info={'all_checks':'PASS','time_error_ratio':ratio,'shorttime_n8_full_shear':r['full_n8_dt0p002']['last']['shear_norm_max'],
      'late_n8_full_shear':c['full_long']['last']['shear_norm_max'],
      'topology_witness_n8':r['topology_8']['witness'],
      'topology_witness_n12':r['topology_12']['witness']}
(P/'independent_audit.json').write_text(json.dumps(info,indent=2,ensure_ascii=False))
