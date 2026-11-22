#!/usr/bin/env python3
"""Standalone artifact checks, no hidden state required."""
from pathlib import Path
import json,csv,hashlib,math
import numpy as np
P=Path(__file__).resolve().parent
main=json.loads((P/'audit_v28.json').read_text())
lag=json.loads((P/'lag_hardening_audit_v28.json').read_text())
scale=json.loads((P/'polarization_amplitude_audit_v28.json').read_text())
assert main['symbolic']['transverse_metric_determinant']=='exp(4*s)'
assert main['curvature_audit']['max_difference']<1e-8
for mode in ['standard','reverse_shear','strong_memory','nonzero_cross']:
    rows=[r for r in main['off_shell_brackets'] if r['mode']==mode]
    assert len(rows)==4
    assert abs(rows[-1]['correct_error'])<abs(rows[-2]['correct_error'])/3.0
    assert abs(rows[-1]['broken_error'])>50*abs(rows[-1]['correct_error'])
assert main['independent_numpy']['absolute_difference']<1e-8
for mode in ['standard','reverse_shear','strong_memory']:
    rows=[r for r in lag['rows'] if r['mode']==mode]
    assert len(rows)==5
    assert abs(rows[-1]['correct_bracket_residual']) < abs(rows[-2]['correct_bracket_residual'])/3.0
    assert abs(rows[-1]['frame_H_difference'])<abs(rows[-2]['frame_H_difference'])/3.5
    assert abs(rows[-1]['omit_both_momentum_mixings'])>10*abs(rows[-1]['correct_bracket_residual'])
assert 1.95<scale['quadratic_scaling_exponent']<2.05
assert scale['homogeneous_memory_control']['max_generated_plus']<1e-9
assert max(abs(r['energy_relative_error']) for r in scale['all_rows'])<1e-8
assert main['shape_wave']['max_relative_energy_error']<1e-8
required=['verify_v28.py','verify_bounded_stiffening_v28.py','polarization_amplitude_audit_v28.py','RESEARCH_NOTE_2026-11-23_v28.md','offdiagonal_bracket_convergence_v28.csv','lag_hardening_brackets_v28.csv','polarization_scaling_v28.csv','nonlinear_polarization_scaling_v28.png']
for f in required: assert (P/f).is_file(),f
report={'status':'PASS','main_metric_curvature_error':main['curvature_audit']['max_difference'],'independent_bracket_difference':main['independent_numpy']['absolute_difference'],'primary_n256_constraint_residual':next(r['correct_error'] for r in main['off_shell_brackets'] if r['mode']=='standard' and r['n']==256),'lag_n512_constraint_residual':next(r['correct_bracket_residual'] for r in lag['rows'] if r['mode']=='standard' and r['n']==512),'nonlinear_polarization_power':scale['quadratic_scaling_exponent'],'checks':len(required)+4+3+6}
(P/'final_audit_v28.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(report,ensure_ascii=False,indent=2))
