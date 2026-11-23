#!/usr/bin/env python3
"""Fail-closed minimal quality gate for v19 archival results."""
import json, pathlib, numpy as np
p=pathlib.Path(__file__).resolve().parent
main=json.loads((p/'audit_v19.json').read_text())
rob=json.loads((p/'robustness_v19.json').read_text())
ind=json.loads((p/'independent_audit_v19.json').read_text())
checks={}
checks['6_distinct_starts_converge_to_same_n120_energy']=float(max(x['final_energy'] for x in rob['multistart'])-min(x['final_energy'] for x in rob['multistart']))<1e-8
checks['n320_is_lower_than_old_profile']=rob['continuation'][-1]['energy'] < 0.6*main['equilibrium'][-1]['energy_old']
checks['fine_grid_energy_close_to_n240']=abs(rob['continuation'][-1]['energy']-rob['continuation'][0]['energy'])<.02
checks['all_optimizer_runs_report_success']=all(x['success'] for x in main['equilibrium']) and all(x['optimizer_success'] for x in rob['multistart']+rob['continuation'])
checks['analytic_gradient_agrees_with_torch']=max(ind[f'gradient_{n}']['gradient_max_abs_difference'] for n in [80,120,180]) <1e-11
checks['radial_hessians_symmetric']=max(ind[f'radial_{n}']['hessian_symmetry_residual'] for n in [80,120,180])<2e-6
checks['radial_sampled_modes_have_positive_omega2']=all(ind[f'radial_{n}']['lowest_radial_omega_squared']>0 for n in [80,120,180])
checks['all_projected_nonradial_omega2_positive']=all(x['lowest_omega_squared']>0 for x in main['projected_modes']) and all(x['minimum_omega_squared']>0 for x in rob['basis_stress'])
c=ind['angular_independent_quadrature']
e8=c['abs_error_eps_0.008'];e4=c['abs_error_eps_0.004'];e2=c['abs_error_eps_0.002']
checks['angular_quadrature_second_variation_O_eps2']=3.7<e8/e4<4.3 and 3.7<e4/e2<4.3
summary={'checks':checks,'passed':all(checks.values()),'counts':{'spherical_resolution_tests':len(main['equilibrium'])+len(rob['continuation']),'multistarts':len(rob['multistart']),'nonradial_projected_matrix_cases':len(main['projected_modes'])+len(rob['basis_stress'])},'limits':['flat spacetime; G=0','finite radial box with Dirichlet boundary','hedgehog equilibrium only','nonradial modes restricted to angular perturbations of f and chi; internal orientation modes excluded','finite-dimensional basis, not complete spectrum','static reversible chi field is not irreversible delay']}
(p/'final_audit_v19.json').write_text(json.dumps(summary,indent=2,ensure_ascii=False))
print(json.dumps(summary,indent=2,ensure_ascii=False))
if not summary['passed']:raise SystemExit(1)
