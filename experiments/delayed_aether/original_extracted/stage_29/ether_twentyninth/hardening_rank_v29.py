#!/usr/bin/env python3
"""Finite Hamiltonian regularity: matched stiffening changes coefficients but not number of modes."""
import csv, json
from pathlib import Path
import numpy as np
import sympy as s
P=Path(__file__).resolve().parent
k=2*np.pi*2/64
Avalues=[1,1.25,2,3.2,8]
rows=[]
for A in Avalues:
    # Kinetic L = A * |dot h|^2 / 2; spatial energy A * |grad h|^2 / 2.
    # Uniform A keeps the speed squared equal to 1, with 6 independent h_ij components.
    kinetic=A*np.eye(6)
    stiffness=A*(4*np.sin(k/2)**2)*np.eye(6)
    speeds=np.sqrt(np.linalg.eigvalsh(np.linalg.solve(kinetic,stiffness)))
    rows.append(dict(A=A,kinetic_rank=int(np.linalg.matrix_rank(kinetic)),
                     nonzero_frequency_modes=int(len(speeds)),minimum_omega=float(speeds.min()),
                     maximum_omega=float(speeds.max())))
assert all(row['kinetic_rank']==6 and row['nonzero_frequency_modes']==6 for row in rows)
assert max(abs(row['maximum_omega']-rows[0]['maximum_omega']) for row in rows)<1e-14
with (P/'hardening_rank_scan.csv').open('w',newline='') as f:
    w=csv.DictWriter(f,fieldnames=list(rows[0])); w.writeheader();w.writerows(rows)
x=s.Symbol('x',positive=True)
Q=s.diag(*([x]*6))
assert Q.det()==x**6 and Q.rank()==6
res={'model':'homogeneous matched stiffness / inertia multiplier A>0',
     'rank_kinetic_all_A_positive':6,
     'frequency_multiplicity_all_A_positive':6,
     'kinetic_determinant':'A**6',
     'a_matched_hardening_law_cannot_produce_four_primary_constraints':True,
     'scan':rows,
     'limitation':'A=const homogeneous background, independent metric perturbations, no pre-imposed gravity constraints'}
(P/'hardening_rank_audit_v29.json').write_text(json.dumps(res,indent=2,ensure_ascii=False)+'\n')
print(json.dumps(res,ensure_ascii=False,indent=2))
