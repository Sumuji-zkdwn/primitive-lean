#!/usr/bin/env python3
"""Independent CSV/JSON cross checks for the published V5 results."""
import csv, json, math
from pathlib import Path
import numpy as np
P=Path(__file__).resolve().parent
with (P/'audit_results.json').open() as f: a=json.load(f)
with (P/'monopole_benchmark.json').open() as f: m=json.load(f)
cone=np.genfromtxt(P/'matched_cones.csv',delimiter=',',names=True)
assert np.all(cone['stiffness_A']>=1.)
assert np.max(cone['stiffness_A'])<=4.00000001
assert np.max(np.abs(cone['new_front_speed']-1))<1e-13
assert np.max(cone['old_fixed_inertia_speed'])>1.9
scat=a['frozen_interface_scattering']
assert abs(scat['R_numeric']-.25)<1e-3
assert abs(scat['T_numeric']-.75)<1e-3
assert abs(scat['R_numeric']+scat['T_numeric']-1)<1e-4
for s in ('nonlinear_dynamics','nonlinear_dynamics_fine'):
    dat=np.genfromtxt(P/(s+'.csv'),delimiter=',',names=True)
    assert len(dat)==121
    assert np.max(np.abs(dat['relative_energy_error']))<2e-9
    assert np.max(dat['max_A'])>3.8
    assert abs(dat['energy'][0]-dat['energy'][-1])<2e-9
assert a['refinement_difference']['peak_A_difference']<.001
r=np.genfromtxt(P/'scaling_obstruction.csv',delimiter=',',names=True)
assert np.all(np.diff(r['two_derivative_plus_potential_E'])>0)
assert np.min(r['with_fourth_derivative_E'])>2.8
lens=np.genfromtxt(P/'conformal_lensing_audit.csv',delimiter=',',names=True)
assert np.max(np.abs(lens['optical_index']-1))==0.
assert 1.75<a['lensing_no_go']['gr_solar_limb_deflection_arcsec']<1.76
b=np.genfromtxt(P/'monopole_profile.csv',delimiter=',',names=True)
assert np.max(np.abs(b['dH_dr']-(1-b['K']**2)/b['r']**2))<5e-11
assert np.max(np.abs(b['dK_dr']+b['H']*b['K']))<5e-12
assert abs(m['energy_at_R_25']/(4*math.pi)-.96)<1e-9
wf=np.genfromtxt(P/'weak_field_lensing.csv',delimiter=',',names=True)
assert abs(wf['analytic_deflection_arcsec'][0])<1e-15
assert abs(wf['analytic_deflection_arcsec'][3]-1.75119032556)<1e-10
assert np.max(np.abs(wf['analytic_deflection_arcsec']-wf['quadrature_deflection_arcsec']))<1e-12
print('PASS all independent V5 CSV+JSON crosschecks')
