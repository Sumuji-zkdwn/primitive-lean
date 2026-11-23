#!/usr/bin/env python3
"""Stage 31: exact 3D bipyramid 2->3 Pachner geometry and curvature lag.

No 4D Regge equations, Einstein constraints, or gravity emergence are asserted.
All combinatorial and rational algebra claims are verified exactly with Fraction.
The finite-time dissipative dynamics tests a deliberately additional model.
"""
from __future__ import annotations
from collections import Counter
from fractions import Fraction as F
from itertools import combinations
from math import acos, pi, sqrt
import csv
import json
from pathlib import Path

A, B, C, D, E = range(5)
BEFORE = [(A, B, C, D), (A, B, C, E)]
AFTER = [(A, B, D, E), (A, C, D, E), (B, C, D, E)]
OUTDIR = Path(__file__).resolve().parent


def incidence(tetrahedra):
    edges = {e for t in tetrahedra for e in combinations(sorted(t), 2)}
    triangles = Counter(f for t in tetrahedra for f in combinations(sorted(t), 3))
    boundary = {t for t, count in triangles.items() if count == 1}
    interior = {t for t, count in triangles.items() if count == 2}
    assert set(triangles.values()) <= {1, 2}
    return edges, boundary, interior


def cos_dihedral(s):
    """cos dihedral angle at the unique edge with squared length s.

    All five remaining edges of one tetrahedron have length 1.
    The Gram projection on the plane normal to that edge gives the ratio.
    """
    return (2 - s) / (4 - s)


def gram_minors(s):
    """Leading principal minors of the Gram matrix of E,A,B based at D."""
    return s, s * (4 - s) / 4, s * (3 - s) / 4


def deficit(x):
    if not 0 < x < sqrt(3):
        raise ValueError('3D tetrahedra require 0<x<sqrt(3)')
    return 2 * pi - 3 * acos(float(cos_dihedral(x*x)))


def deficit_derivative(x):
    if not 0 < x < sqrt(3):
        raise ValueError('outside nondegenerate tetrahedron domain')
    return -6*x / ((4-x*x)*sqrt(3-x*x))


def exact_checks():
    e0, b0, i0 = incidence(BEFORE)
    e1, b1, i1 = incidence(AFTER)
    assert len(e0) == 9 and len(e1) == 10
    assert e1 - e0 == {(D, E)} and not (e0 - e1)
    assert b0 == b1 and len(b0) == 6
    assert i0 == {(A, B, C)}
    assert i1 == {(A, D, E), (B, D, E), (C, D, E)}
    assert len(AFTER) == 3 and len(BEFORE) == 2

    for s in [F(1), F(8,3), F(11,4)]:
        assert all(v > 0 for v in gram_minors(s)), (s,gram_minors(s))
    assert cos_dihedral(F(1)) == F(1,3)
    assert cos_dihedral(F(8,3)) == -F(1,2)
    assert cos_dihedral(F(11,4)) == -F(3,5)
    assert cos_dihedral(F(1)) > cos_dihedral(F(8,3)) > cos_dihedral(F(11,4))

    # A rational cross-multiplied identity (no floating point):
    for s in [F(1), F(8,3), F(11,4), F(2,3), F(5,2)]:
        for t in [F(1), F(8,3), F(11,4), F(3,4)]:
            assert cos_dihedral(s) - cos_dihedral(t) == 2*(t-s) / ((4-s)*(4-t))
    assert 3*F(8,3) - 8 == 0
    assert abs(deficit(sqrt(8/3))) < 3e-15
    assert deficit(1.) > 0 > deficit(sqrt(11/4))
    assert abs(deficit_derivative(sqrt(8/3)) + 9*sqrt(2)) < 3e-14

    for h in (1e-3, 1e-4, 1e-5):
        slope = (deficit(sqrt(8/3)+h)-deficit(sqrt(8/3)-h))/(2*h)
        assert abs(slope + 9*sqrt(2)) < 300*h*h, (h,slope)

    return {'before_tetra':2, 'after_tetra':3, 'before_edges':9, 'after_edges':10,
            'boundary_triangles':6, 'new_interior_edge':'DE',
            'interior_faces_before':1, 'interior_faces_after':3,
            'exact_cos_samples':{'s=1':'1/3','s=8/3':'-1/2','s=11/4':'-3/5'},
            'flat_s':'8/3','d_deficit_dx_at_flat':'-9 sqrt(2)',
            'rational_difference_checks':20, 'status':'PASS'}


def curvature_scan():
    rows=[]
    for j in range(81):
        s=0.7 + j*(2.92-0.7)/80
        x=sqrt(s)
        rows.append({'s':s,'internal_edge_x':x,'cos_dihedral':float(cos_dihedral(s)),
                     'angle_deficit_rad':deficit(x),
                     'd_deficit_dx':deficit_derivative(x)})
    with (OUTDIR/'curvature_scan_v31.csv').open('w',newline='') as f:
        w=csv.DictWriter(f, fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
    return rows


def rk4_step(f, y, h):
    def plus(a,b,m):
        return tuple(x+m*z for x,z in zip(a,b))
    a=f(y)
    b=f(plus(y,a,h/2))
    c=f(plus(y,b,h/2))
    d=f(plus(y,c,h))
    return tuple(z+h*(aa+2*bb+2*cc+dd)/6 for z,aa,bb,cc,dd in zip(y,a,b,c,d))


def dynamics(gamma=2.0, dt=0.005, T=12., write=False):
    """Lagrangian curvature mode x, overdamped memory z, cumulative dissipation.

    E = (1/2)M xdot² + (k/2)(delta(x)-z)² + (mu/2)z².
    Equations: M xddot = -k (delta-z)*delta'(x),
               zdot = -gamma ((k+mu)*z - k*delta),
               Ddot = gamma ((k+mu)*z - k*delta)².
    Then d(E+D)/dt=0 by direct differentiation, provided x stays in domain.
    """
    mass,k,mu=1.,0.15,0.5
    x_flat=sqrt(8/3)
    def E0(y):
        x,v,z,_=y
        delta=deficit(x)
        return mass*v*v/2+k*(delta-z)**2/2+mu*z*z/2
    def rhs(y):
        x,v,z,_=y
        delta,dp=deficit(x),deficit_derivative(x)
        gradz=(k+mu)*z-k*delta
        return (v, -k*(delta-z)*dp/mass, -gamma*gradz, gamma*gradz*gradz)
    y=(x_flat+0.035,0.,0.,0.)
    n=round(T/dt);assert abs(n*dt-T)<1e-9
    start_E=E0(y)
    rows=[];max_balance_error=0.;min_E=start_E;max_E=start_E
    for j in range(n+1):
        if j%(max(1,round(0.05/dt)))==0 or j==n:
            energy=E0(y);balance=energy+y[3]-start_E
            max_balance_error=max(max_balance_error,abs(balance))
            min_E=min(min_E,energy);max_E=max(max_E,energy)
            rows.append({'t':j*dt,'x':y[0],'delta':deficit(y[0]),'v':y[1],
                         'memory':y[2],'energy':energy,'dissipated':y[3],
                         'energy_balance_error':balance})
        if j<n: y=rk4_step(rhs,y,dt)
    assert abs(y[0]-x_flat)<0.5 and 0<y[0]<sqrt(3)
    assert max_balance_error < (2e-6 if gamma>0 else 2e-9),max_balance_error
    assert y[3]>=0 and (gamma == 0 or min_E<start_E)
    if write:
        with (OUTDIR/'memory_dynamics_v31.csv').open('w',newline='') as f:
            w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
    return {'gamma':gamma,'dt':dt,'T':T,'initial_E':start_E,'final_E':E0(y),
            'dissipated':y[3],'final_x':y[0],'final_delta':deficit(y[0]),
            'max_abs_energy_balance_error':max_balance_error,'rows':rows}


def main():
    a=exact_checks()
    scan=curvature_scan()
    slow=dynamics(gamma=2.,dt=0.005,T=12.,write=True)
    fine=dynamics(gamma=2.,dt=0.0025,T=12.)
    conservative=dynamics(gamma=0.,dt=0.005,T=12.)
    # Cross-run convergence in the final coordinates, not just conservation:
    assert abs(slow['final_x']-fine['final_x']) < 3e-7
    assert abs(slow['dissipated']-fine['dissipated']) < 3e-8
    assert abs(conservative['final_E']-conservative['initial_E']) < 2e-9
    results={**a,'static_scan':{'rows':len(scan),'delta_s=1':deficit(1),
              'delta_s=8/3':deficit(sqrt(8/3)),'delta_s=11/4':deficit(sqrt(11/4))},
              'memory_dynamics':{k:v for k,v in slow.items() if k!='rows'},
              'refinement':{k:v for k,v in fine.items() if k!='rows'},
              'conservative_control':{k:v for k,v in conservative.items() if k!='rows'},
              'physical_scope':'3D spatial Regge hinge toy; 4D gravity emergence NOT claimed'}
    (OUTDIR/'audit_v31.json').write_text(json.dumps(results,indent=2,ensure_ascii=False)+'\n')
    print(json.dumps({k:v for k,v in results.items() if k not in ('memory_dynamics','refinement','conservative_control')},ensure_ascii=False))
    print('energy balance',slow['max_abs_energy_balance_error'],'conservative drift',conservative['final_E']-conservative['initial_E'])
    return results


if __name__=='__main__':
    main()
