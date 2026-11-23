#!/usr/bin/env python3
"""Rerunnable verification of archived output; no new simulation required."""
from pathlib import Path
import csv, math
import numpy as np
P=Path(__file__).resolve().parent
summary=list(csv.DictReader(open(P/'dynamics_summary.csv')))
assert len(summary)==6
names={r['tag']:r for r in summary}
for r in summary:
    name=r['tag']
    ts=list(csv.DictReader(open(P/(name+'_timeseries.csv'))))
    en=np.array([float(x['E']) for x in ts])
    di=np.array([float(x['cumulative_dissipation']) for x in ts])
    monotonic_violation=max(0,float(np.max(np.diff(en))))
    balance_error=float(np.max(np.abs(en+di-en[0])))
    assert len(ts)==161
    assert monotonic_violation<1e-7,(name,monotonic_violation)
    assert balance_error<1e-6,(name,balance_error)
    assert abs(en[-1]-float(r['energy_final']))<1e-8
    assert float(r['initial_amplitude'])>float(r['final_amplitude'])
    print(name,'E+D maximum residual:',balance_error,'final fraction of displacement',float(r['final_amplitude'])/float(r['initial_amplitude']))
ref=names['delayed_memory'];fine=names['fine_delayed']
for k,tol in [('final_amplitude',.025),('final_radius',.005),('effective_charge_final',.002)]:
    rel=abs(float(ref[k])-float(fine[k]))/abs(float(fine[k]))
    print('mesh comparison',k,rel)
    assert rel<tol
assert float(ref['max_tangent_modulus'])>8*float(ref['k'])
assert math.isclose(1/math.sqrt(2),.7071067811865475,rel_tol=1e-12)
print('ARCHIVE AUDIT PASSED')
