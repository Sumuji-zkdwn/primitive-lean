#!/usr/bin/env python3
"""Regression audit of the finite experiment, including independent degree targets."""
import csv,json
from pathlib import Path
import numpy as np
from verify_v11 import make_mesh,hedgehog,degree_preimage,source_texture,unique_edges,metric_geometry
P=Path(__file__).resolve().parent
J=json.loads((P/'audit_v11.json').read_text())
assert J['coordinate_warp_negative_control']['max_flat_residual']<1e-10
for n in (8,12,16,20):
    c=[r for r in J['degree_cases'] if r['n']==n]
    expected={'vacuum':0,'single':-1,'translated':-1,'elliptical':-1,'orientation_reverse':1}
    if n>=12:expected['two_disjoint']=-2
    assert {r['case']:r['degree'] for r in c}==expected
    assert all(r['boundary_error']<1e-13 for r in c)
for n in (8,12,16):
    geom=[r for r in J['metric_cases'] if r['n']==n]
    assert geom[0]['alpha']==0
    assert geom[0]['max_flat_residual']<1e-10
    assert all(r['min_gram_eigenvalue']>0 for r in geom)
    assert geom[-1]['regge_abs_curvature']>0.9
    assert [r['regge_abs_curvature'] for r in geom]==sorted(r['regge_abs_curvature'] for r in geom)
# Independent regular values give identical integer degree.
coords,tets=make_mesh(16);q=hedgehog(coords)
for target in [(-1,.1,-.04,.12),(-1,-.07,.13,-.05),(-1,.031,.06,-.11),
               (-1,.18,.07,.06),(-1,-.09,-.17,.12)]:
    assert degree_preimage(coords,tets,q,target=target)==-1
# Coarse-grid shrinking failure must be detected, not presented as a true soliton death.
reduced={n:{r['radius']:r['degree'] for r in J['resolution_failure'] if r['n']==n} for n in (8,12,16,20)}
assert reduced[8][.3]==0 and reduced[20][.3]==-1
A=json.loads((P/'energy_audit.json').read_text())
assert abs(A['predicted_minimum_radius']-.48)<1e-12
for n in ('80','100','120'):
    assert abs(A['grid_minima'][n]['radius']-.48)<1e-12
assert A['grid_minima']['20']['radius']==.24
with (P/'memory_dynamics.csv').open() as f:
    mem=list(csv.DictReader(f))
for tau in (.2,.8):
    R=[r for r in mem if float(r['tau'])==tau]
    assert len(R)==161
    assert float(R[0]['lag_l2'])<1e-14
    assert float(R[-1]['lag_l2'])<2e-5
    for x in R:
        assert .8-1e-12 <= float(x['max_tangent_stiffness']) <= 3.8+1e-12
    checkpoints=[r for r in R if r['topological_charge']]
    assert all(int(c['topological_charge'])==1 for c in checkpoints)
peak20=max(float(r['max_tangent_stiffness']) for r in mem if float(r['tau'])==.2)
peak80=max(float(r['max_tangent_stiffness']) for r in mem if float(r['tau'])==.8)
assert peak80>peak20+.5
print(json.dumps({'status':'PASS','independent_targets':5,'degree_meshes':4,
                   'flat_control_max_deficit':J['coordinate_warp_negative_control']['max_flat_residual'],
                   'physical_gravity_derived':False,
                   'peak_stiffness_tau_0p2':peak20,'peak_stiffness_tau_0p8':peak80},indent=2))
