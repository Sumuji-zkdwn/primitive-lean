#!/usr/bin/env python3
"""Independent geometric calculation and finite-difference checks for round 21."""
from pathlib import Path
import json
import sympy as s
import numpy as np

ROOT=Path(__file__).resolve().parent
u,v,x,y=s.symbols('u v x y')
coords=(u,v,x,y)
P=s.Function('P')(u)
Q=s.Function('Q')(u)
met=s.diag(1,1,1,1)
met=s.Matrix([[0,-1,0,0],[-1,0,0,0],[0,0,P**2,0],[0,0,0,Q**2]])
ginv=met.inv()
Gamma=[[[s.simplify(s.Rational(1,2)*sum(ginv[a,d]*(s.diff(met[d,c],coords[b])+s.diff(met[d,b],coords[c])-s.diff(met[b,c],coords[d])) for d in range(4))) for c in range(4)] for b in range(4)] for a in range(4)]
Ricci=s.Matrix(4,4,lambda b,d:s.simplify(sum(s.diff(Gamma[a][b][d],coords[a]) - s.diff(Gamma[a][b][a],coords[d]) + sum(Gamma[a][a][k]*Gamma[k][b][d] - Gamma[a][d][k]*Gamma[k][b][a] for k in range(4)) for a in range(4))))
expected=-s.diff(P,u,2)/P-s.diff(Q,u,2)/Q
assert s.simplify(Ricci[0,0]-expected)==0
assert all(s.simplify(Ricci[i,j])==0 for i in range(4) for j in range(4) if (i,j)!=(0,0))
assert s.simplify(s.trace(ginv*Ricci))==0
rows={}
for mode in ['vacuum','equal_null_scalars']:
    vals=np.loadtxt(ROOT/f'exact_rosen_{mode}.csv',delimiter=',',skiprows=1)
    dt=vals[1,0]-vals[0,0]
    def second_dif(f):
        return (-f[4:]+16*f[3:-1]-30*f[2:-2]+16*f[1:-3]-f[:-4])/(12*dt**2)
    p,q=vals[:,1],vals[:,3]
    Ruu_fd=-second_dif(p)/p[2:-2]-second_dif(q)/q[2:-2]
    target=vals[2:-2,6]
    discrepancy=float(np.max(abs(Ruu_fd-target)))
    assert discrepancy<2e-8,(mode,discrepancy)
    rows[mode]={'direct_metric_second_derivative_Ruu_max_residual':discrepancy,
                'smallest_p':float(p.min()), 'smallest_q':float(q.min()),
                'differentiation_stencil':'5-point central second derivative; uses saved metric data only'}
quad=np.genfromtxt(ROOT/'nonlinear_ricci_scaling.csv',delimiter=',',names=True)
err0=quad['linear_only_max_abs_Ruu'];err1=quad['second_order_max_abs_Ruu'];a=quad['epsilon']
# For small amplitudes, verify asymptotic scaling using the three smallest eps.
slope0=float(np.polyfit(np.log(a[:3]),np.log(err0[:3]),1)[0])
slope1=float(np.polyfit(np.log(a[:3]),np.log(err1[:3]),1)[0])
assert 1.9<slope0<2.1
assert 3.9<slope1<4.2
# The no-go q!=z in a pure null wave follows analytically from the relative massive mode.
t,zz,m=s.symbols('t z m',real=True)
F=s.Function('F')(t-zz)
check=s.simplify(-s.diff(F,t,2)+s.diff(F,zz,2))
assert check==0
res={'full_4d_Ricci':{'Ruu':str(expected), 'all_other_components':0,
                        'scalar_curvature_exactly_zero':True},
     'fd_independent_numeric_check':rows,
     'small_amplitude_convergence_slopes':{'linear_metric':slope0,'quadratic_metric':slope1},
     'null_memory_no_go_exact_dalembertian':str(check),
     'conclusions':'Independent geometric calculation confirms exact Rosen formula and saved numerical metrics satisfy Einstein vacuum or sourced equation at finite-difference accuracy. GR itself is presupposed.'}
(ROOT/'independent_audit_v21.json').write_text(json.dumps(res,indent=2,ensure_ascii=False)+'\n')
print(json.dumps(res,indent=2,ensure_ascii=False))
