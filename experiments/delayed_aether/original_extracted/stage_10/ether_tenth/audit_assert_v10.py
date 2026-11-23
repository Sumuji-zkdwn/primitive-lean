"""Independent post-run consistency audit for generated V10 artifacts."""
from pathlib import Path
import json,csv,sys
import numpy as np
ROOT=Path(__file__).parent
V=json.loads((ROOT/'audit_v10.json').read_text())
assert V['spatial_2x2x2']['betti_mod2']==[1,3,3,1]
assert V['spatial_3x3x3']['betti_mod2']==[1,3,3,1]
assert V['spacetime_cylinder_2x2x2_times_2_intervals']['betti_mod2']==[1,3,3,1,0]
assert V['periodic_time_4torus']['betti_mod2']==[1,4,6,4,1]
assert V['open_spatial_box']['betti_mod2']==[1,0,0,0]
assert V['spacetime_full_cochain_exact_audit']['exact_cube_failures']==0
assert V['spacetime_full_cochain_exact_audit']['one_uncompensated_face_flip_cube_failures']==4
cases={}
for q in [0,1]:
    for rate in ['0p06','0p15']:
        path=ROOT/f'dynamics_charge_{q}_rate_{rate}.csv'
        raw=np.genfromtxt(path,delimiter=',',names=True)
        cases[(q,rate)]=raw
        assert len(raw)==141
        assert int(raw['excited_plaquettes'][-1])==3*q
        assert np.all(np.diff(raw['energy'])<1e-8)
        assert np.all(raw['Q01']==q)
        assert np.all(raw['Q02']==0) and np.all(raw['Q12']==0)
        assert abs(raw['energy'][-1]-6*q)<.001
        assert float(raw['max_tangent_stiffness'].max())>3
        assert float(raw['max_tangent_stiffness'].min())>=.3-1e-12
        assert float(raw['max_tangent_stiffness'].max())<3.3+1e-12
for q in [0,1]:
    slow=cases[(q,'0p06')]['energy'][-1]
    fast=cases[(q,'0p15')]['energy'][-1]
    assert abs(fast-6*q)<abs(slow-6*q), (q,slow,fast)
with (ROOT/'sector_area_bounds.csv').open() as f:
    rows=list(csv.DictReader(f))
assert len(rows)==12
assert all(int(r['proven_lower_bound'])==int(r['explicit_saturating_area'])
            and r['one_flux_in_each_transverse_slice']=='True' for r in rows)
print('PASS: GF2 topology, full spacetime cochain, Bianchi violation counterexample,')
print('      4 dissipative trajectories, conserved charges, area lower bounds, memory rates')
