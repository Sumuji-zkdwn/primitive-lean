#!/usr/bin/env python3
"""Independent 80-digit symmetric-family audit of the complete 4D Regge action.
No imports from verify_v30.py; no numerical matrices or fitted Hessians.
"""
import json
from pathlib import Path
import mpmath as mp
import sympy as sp
mp.mp.dps=80
O=Path(__file__).resolve().parent
x0=mp.sqrt(mp.mpf(2)/5)
A_boundary=mp.sqrt(3)/4

def theta_internal(x):
    t=x*x
    return mp.acos((2*t-1)/(2*(3*t-1)))

def theta_boundary(x):
    # For a central vertex joined to four of the five regular boundary vertices.
    # Gram = 1/2 I + (x²-1/2) 11^T. Let G^-1 = 2I - c 11^T.
    t=x*x
    c=2*(t-mp.mpf('.5'))/(4*t-mp.mpf('1.5'))
    return mp.acos((2-4*c)/mp.sqrt((8-16*c)*(2-c)))

def area_internal(x):
    return mp.sqrt(4*x*x-1)/4

def deficit(x):
    return 2*mp.pi-3*theta_internal(x)

def full_action(x):
    return 10*area_internal(x)*deficit(x) + 10*A_boundary*(mp.pi-2*theta_boundary(x))

original_boundary_angle=mp.acos(mp.mpf(1)/4)
assert mp.almosteq(theta_boundary(x0)*2,original_boundary_angle)
assert abs(deficit(x0))<mp.mpf('1e-70')
# An independent calculation: 2nd derivative of the FULL action, including
# the boundary Gibbons-Hawking-Regge term, along x on ALL five inner edges.
second=mp.diff(full_action,x0,2)
expected=200*mp.sqrt(5) # 1ᵀ H 1, where H_{ij}=8 sqrt(5)
assert abs(second-expected)<mp.mpf('1e-60')
first=mp.diff(full_action,x0,1)
assert abs(first)<mp.mpf('1e-60')
# Differentiating direct S and the Schlaefli-reduced expression agree off-shell.
x1=x0+mp.mpf('0.002')
reduced_first=10*mp.diff(area_internal,x1)*deficit(x1)
assert abs(mp.diff(full_action,x1)-reduced_first)<mp.mpf('1e-60')
exact={
 'numeric_precision_decimal_digits':80,
 'radial_edge_length':'sqrt(2/5)',
 'bulk_deficit_at_flat_center':mp.nstr(deficit(x0),12),
 'two_boundary_subsimplex_angles_equal_original':True,
 'first_derivative_full_action_at_flat':mp.nstr(first,16),
 'second_derivative_full_action_at_flat':mp.nstr(second,45),
 'exact_expected_second_derivative':'200 sqrt(5)',
 'hessian_one_entry':'8 sqrt(5)',
 'full_action_schlaefli_first_derivative_offshell_delta':mp.nstr(mp.diff(full_action,x1)-reduced_first,16),
 'assertion_passed':True,
 'caveats':'5-1 flat Euclidean 4D configuration, fixed boundary edges, Regge-Einstein action INPUT; no gravitons, no time evolution and no emergent Einstein-Hilbert dynamics.'
}
(O/'independent_audit_v30.json').write_text(json.dumps(exact,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(exact,ensure_ascii=False,indent=2))
