#!/usr/bin/env python3
"""A distinct, explicitly extended massless-mode experiment.

This DOES NOT derive gravity from the original delayed-hardening system.
It adds a massless scalar h with quadratic gradient energy and a specified source:
   E[h, rho] = integral (K/2)*|grad h|^2 - g*rho*h
   -K Laplacian(h)=g*rho.
For K=g=1, source delta at grid center, Dirichlet zero boundary,
solve exactly the finite discrete Poisson equation with a type-I DST.
Pair interaction potential is -h(r), attractive force magnitude approximates
1/(4*pi*r^2) on scales distant from the source and boundary.
"""
import csv, json, math
from pathlib import Path
import numpy as np
from scipy.fft import dstn, idstn

HERE=Path(__file__).resolve().parent
N=101  # includes zero-valued Dirichlet boundaries
ni=N-2
center=(N-1)//2
source=np.zeros((ni,ni,ni),dtype=np.float64)
source[ni//2,ni//2,ni//2]=1.
ks=np.arange(1,ni+1)
eigs=2*(1-np.cos(np.pi*ks/(ni+1)))
denominator=eigs[:,None,None]+eigs[None,:,None]+eigs[None,None,:]
hat=dstn(source,type=1,norm='ortho')
solution=idstn(hat/denominator,type=1,norm='ortho')

# Verify discrete -Delta u = source on all interior grid points.
up=np.pad(solution,((1,1),(1,1),(1,1)))
negative_lap=6*up[1:-1,1:-1,1:-1] - (up[2:,1:-1,1:-1]+up[:-2,1:-1,1:-1]
 +up[1:-1,2:,1:-1]+up[1:-1,:-2,1:-1]
 +up[1:-1,1:-1,2:]+up[1:-1,1:-1,:-2])
max_residual=float(np.max(np.abs(negative_lap-source)))

radii=[4,5,6,7,8,10,12,14,16,18]
rows=[]
for r in radii:
    h_plus=float(up[center+r+1,center,center]);h_minus=float(up[center+r-1,center,center])
    h0=float(up[center+r,center,center])
    # F= -d/dr [ -h(r) ] = h'(r), negative (inwards)
    force_mag=(h_minus-h_plus)/2
    expected=1/(4*math.pi*r*r)
    rows.append({'radius_r':r,'potential_h':h0,
                 'inward_force_magnitude':force_mag,
                 'continuum_inverse_square':expected,
                 'ratio_discrete_to_inverse_square':force_mag/expected})
with (HERE/'delayed_aether_3d_poisson.csv').open('w',newline='',encoding='utf-8') as f:
    writer=csv.DictWriter(f,fieldnames=list(rows[0].keys()));writer.writeheader();writer.writerows(rows)
output={'grid_size_with_boundaries':N, 'source_position':center,
        'max_absolute_poisson_residual':max_residual,
        'data':rows,'disclaimer':'Inverse-square force follows from newly assumed 3D massless field; not a derivation from delayed hardening.'}
(HERE/'delayed_aether_3d_poisson.json').write_text(json.dumps(output,indent=2),encoding='utf-8')
print(json.dumps(output,indent=2))

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
fig,ax=plt.subplots(figsize=(7.8,4.5))
ax.loglog(radii,[x['inward_force_magnitude'] for x in rows],'.-',label='3D discrete Laplace solution')
ax.loglog(radii,[x['continuum_inverse_square'] for x in rows],'--',label='1/(4πr²)')
ax.set(xlabel='Separation r (lattice units)',ylabel='Attractive force magnitude',
       title='Inverse-square law from an added massless 3D field')
ax.legend();fig.tight_layout();fig.savefig(HERE/'delayed_aether_3d_poisson.png',dpi=180)
