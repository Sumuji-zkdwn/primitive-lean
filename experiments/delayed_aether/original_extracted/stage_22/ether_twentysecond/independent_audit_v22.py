#!/usr/bin/env python3
"""Off-shell EL audit, independent construction from Lagrangian, not from hand EOM."""
import json
import csv
import numpy as np
import sympy as sp
from pathlib import Path
from importlib.machinery import SourceFileLoader

ROOT=Path(__file__).resolve().parent
# The primary module is loaded ONLY to compare the independently derived acceleration.
model=SourceFileLoader('model_v22',str(ROOT/'verify_v22.py')).load_module()
b1,b2,b3,q,z = xs=sp.symbols('b1 b2 b3 q z',real=True)
v1,v2,v3,vq,vz = vs=sp.symbols('v1 v2 v3 vq vz',real=True)
D=sp.Rational(3); width=sp.Rational(45,100); mu=sp.Rational(12,10)
y=z-q
A=1+D*sp.tanh(y/width)**2
Q=sum(v*v for v in vs[:3])-sum(vs[:3])**2
K=(A*vq**2+vz**2)/2
V=mu**2*y**2/2
L=sp.exp(b1+b2+b3)*(Q+K-V)
# E_j = d/dt(∂L/∂v_j) - ∂L/∂x_j = M_jk a_k + J_ji v_i - ∂L/∂x_j.
ps=sp.Matrix([sp.diff(L,v) for v in vs])
M=ps.jacobian(vs)
J=ps.jacobian(xs)
b=sp.Matrix([sp.diff(L,x) for x in xs]) - J*sp.Matrix(vs)
assert M.shape==(5,5)
Mfun=sp.lambdify([*xs,*vs],M,'numpy',cse=True)
bfun=sp.lambdify([*xs,*vs],b,'numpy',cse=True)
rs=np.random.default_rng(22023)
maximum=0
pars=model.model_parameters()
for i in range(100):
    coords=rs.uniform(-.6,.6,5)
    vels=rs.uniform(-.42,.42,5)
    xx=np.r_[coords,vels]
    expected=np.linalg.solve(np.asarray(Mfun(*xx),dtype=float),np.asarray(bfun(*xx),dtype=float).reshape(5))
    w=np.r_[coords[:3],coords[3:],vels[:3],vels[3:]]
    got=model.rhs(0,w,pars)[5:]
    diff=float(np.max(abs(expected-got)))
    maximum=max(maximum,diff)
assert maximum<2e-12,maximum

with (ROOT/'coupled_bianchiI_v22.csv').open() as f:
    rows=list(csv.DictReader(f))
A=np.array([float(row['A']) for row in rows]);C=np.array([float(row['constraint_C']) for row in rows]);E=np.array([float(row['lapse_EL_E_N']) for row in rows]);t=np.array([float(row['time']) for row in rows])
check_C=[];check_A=[]
for row in rows:
    v=np.array([float(row[f'vbeta{i}']) for i in (1,2,3)])
    q=float(row['q']);z=float(row['z']);vq=float(row['vq']);vz=float(row['vz'])
    yy=z-q
    Ai=1+3*np.tanh(yy/.45)**2
    Qi=np.dot(v,v)-np.sum(v)**2
    Ki=.5*(Ai*vq**2+vz**2)
    Vi=.5*1.2**2*yy**2
    check_C.append(Qi+Ki+Vi);check_A.append(Ai)
err_A=max(abs(np.array(check_A)-A))
err_C=max(abs(np.array(check_C)-C))
assert err_C<4e-15,err_C
assert err_A<3e-15,err_A
assert abs(E[0])<1e-13

with (ROOT/'inconsistent_friction_v22.csv').open() as f:
    rowsbad=list(csv.DictReader(f))
source=np.array([float(row['integrated_missing_source']) for row in rowsbad])
actual=np.array([float(row['minus_expS_C']) for row in rowsbad])
assert actual[-1]>.1
max_discrep=float(max(abs(source-actual)))
assert max_discrep<1e-5

out={'exact_lagrangian_independent_EL_acceleration_max_diff':maximum,
     'independent_reconstructed_A_max_diff':float(err_A),
     'independent_reconstructed_constraint_max_diff':float(err_C),
     'max_abs_constraint_from_saved_trajectory':float(max(abs(C))),
     'max_bad_constraint_violation':float(max(abs(actual))),
     'max_bad_source_integral_diff':max_discrep,
     'random_offshell_checks':100,
     'all_assertions_passed':True}
(ROOT/'independent_audit_v22.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
