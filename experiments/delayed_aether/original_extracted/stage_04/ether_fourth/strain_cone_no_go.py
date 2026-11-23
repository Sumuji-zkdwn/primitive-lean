#!/usr/bin/env python3
"""Local principal symbol test of toy static Skyrme stiffness + fixed inertia.

At a point choose d_2 q=A*v2 and a transverse wave perturbation along x1,
with d_1 delta q=epsilon*v1, v1 orthogonal v2 and both tangent to S^3.
Then rho4 has term 0.5*A^2*epsilon^2, raising the local tangent modulus
from c + k to c + k + A^2. With fixed Mq = 1.9,
this exceeds vacuum cone speed 1 for any A!=0.
This applies to the nonrelativistic kinetic-energy completion used in v3,
not automatically to the fully Lorentz-covariant Skyrme Lagrangian.
"""
from pathlib import Path
import numpy as np,csv
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
P=Path(__file__).resolve().parent
G0=1.;k=.9;M=1.9
A=np.linspace(0,5,250)
v=np.sqrt((G0+k+A*A)/M)
with (P/'strong_field_cone.csv').open('w',newline='') as f:
    w=csv.writer(f);w.writerow(['background_gradient','wavefront_speed'])
    w.writerows(zip(A,v))
fig,ax=plt.subplots(figsize=(8.8,5.1))
ax.plot(A,v,label='Local wavefront speed in fixed-inertia toy dynamics')
ax.axhline(1,color='black',ls='--',lw=1,label='Vacuum front speed 1')
ax.set(xlabel='Background transverse gradient magnitude A',ylabel='Local characteristic speed',
       title='Quartic Skyrme stiffness defeats vacuum-only speed tuning')
ax.legend();ax.grid(alpha=.22);fig.tight_layout();fig.savefig(P/'strong_field_cone.png',dpi=165);plt.close(fig)
print('A=0,2,5 speeds:',np.sqrt((G0+k+np.array([0,2,5])**2)/M))
