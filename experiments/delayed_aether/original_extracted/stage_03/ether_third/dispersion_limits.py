#!/usr/bin/env python3
"""Vacuum linearized characteristic-speed audit for the model in delayed_hardening_dynamics.py.
When q changes slowly the internal z follows strain; when very rapidly, z is frozen.
For a radial high-frequency, short-wavelength disturbance around the vacuum, the
principal q speed changes with frequency, whereas the scalar speed does not.
"""
import csv,math
from pathlib import Path
P=Path(__file__).resolve().parent
cases=[('no_memory',1.,2.,0.),('memory',1.,2.,.9)]
rows=[]
for name,mq,mh,k in cases:
    clow=math.sqrt(1/mq)
    chigh=math.sqrt((1+k)/mq)
    scalar=math.sqrt(1/mh)
    rows.append({'case':name,'q_low_frequency_speed':clow,'q_high_frequency_speed':chigh,'h_scalar_speed':scalar,
                 'single_speed_all_modes':math.isclose(clow,chigh,rel_tol=1e-10) and math.isclose(clow,scalar,rel_tol=1e-10)})
with (P/'vacuum_speed_audit.csv').open('w',newline='') as f:
    w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
for row in rows:print(row)
assert not rows[1]['single_speed_all_modes']
print('SELECTED PARAMETERS FAIL UNIVERSAL LOW/HIGH-FREQUENCY PROPAGATION SPEED')
