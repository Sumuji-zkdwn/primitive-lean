#!/usr/bin/env python3
"""Crosscheck independently generated JSON/CSVs, image existence, and source hashes."""
from pathlib import Path
import csv, hashlib, json, math
P=Path(__file__).resolve().parent
main=json.loads((P/'audit_v29.json').read_text())
ind=json.loads((P/'independent_audit_v29.json').read_text())
hard=json.loads((P/'hardening_rank_audit_v29.json').read_text())
assert main['algebra']['metric_map_rank']==ind['exact_link_metric_rank']==6
assert main['algebra']['TT_projector_rank']==ind['TT_rank']==2
assert main['algebra']['strain_gauge_rank']==ind['gauge_rank']==3
assert main['algebra']['scalar_curvature_constraint_rank']==ind['curvature_rank']==1
assert main['algebra']['phase_space_dof_after_four_first_class_constraints']==ind['constrained_phase_space_dimension']==4
assert ind['flat_embedding_seven_edge_residual']=='1/3200'
assert abs(main['numeric']['false_mismatch_scaling_slope']-3)<.015
assert main['numeric']['max_gauge_curvature_residual_17cube']<1e-12
assert max(main['numeric']['local_wave_energy_relative_max_drifts'].values())<1e-12
assert all(x['kinetic_rank']==6 for x in hard['scan'])
with (P/'embedding_mismatch.csv').open() as f: assert len(list(csv.DictReader(f)))==8
with (P/'wave_counterexample.csv').open() as f: assert len(list(csv.DictReader(f)))==700*3
for name in ['flat_embedding_false_defect.png','six_mode_no_go.png']:
    assert (P/name).stat().st_size>10000
summary={'status':'PASS','main_exact_rank_checks':True,'independent_rational_checks':True,
         'embedding_false_curvature_counterexample':'1/3200 at epsilon=1/100, a=1/4',
         'wave_three_sector_duration_steps':700,
         'max_energy_relative_drift':max(main['numeric']['local_wave_energy_relative_max_drifts'].values()),
         'positive_hardening_preserves_six_modes':True,
         'source_files_hashed':None}
paths=sorted(p for p in P.iterdir() if p.is_file() and p.name not in ['SHA256SUMS.txt','final_audit_v29.json'])
(P/'SHA256SUMS.txt').write_text(''.join(f'{hashlib.sha256(p.read_bytes()).hexdigest()}  {p.name}\n' for p in paths))
summary['source_files_hashed']=len(paths)
(P/'final_audit_v29.json').write_text(json.dumps(summary,indent=2,ensure_ascii=False)+'\n')
print(json.dumps(summary,indent=2,ensure_ascii=False))
