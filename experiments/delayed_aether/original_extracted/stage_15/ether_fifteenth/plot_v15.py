"""Plots computed outputs; uses matplotlib's default colors."""
from pathlib import Path
import csv
import numpy as np
import matplotlib.pyplot as plt
P=Path(__file__).parent
with (P/'graph_constraints.csv').open() as fh:
    rows=list(csv.DictReader(fh))
r=[x for x in rows if abs(float(x['t'])-0.37)<1e-10]
n=np.array([float(x['n']) for x in r]);h=2*np.pi/n
plt.figure(figsize=(7.3,4.4))
for k,lab in [('H','Hamiltonian constraint'),('M','Momentum constraint'),('gamma_evo','Metric evolution'),('K_evo','K evolution')]:
    plt.loglog(h,[float(x[k]) for x in r],'o-',label=lab)
plt.loglog(h,0.5*(h/h[0])**2,'--',label='reference: O(h^2)')
plt.xlabel('Grid spacing h');plt.ylabel('maximum absolute residual');plt.title('Nonlinear ADM: rippled Minkowski slicing');plt.legend(fontsize=8);plt.grid(True,which='both',alpha=.25);plt.tight_layout();plt.savefig(P/'constraint_convergence.png',dpi=180);plt.close()
plt.figure(figsize=(7.3,4.4))
plt.loglog(h,[float(x['H']) for x in r],'o-',label='Hamiltonian: exact vacuum data')
plt.loglog(h,[float(x['naive_memory_H']) for x in r],'o-',label='Hamiltonian: naive history correction')
plt.loglog(h,[float(x['M']) for x in r],'s--',label='Momentum: exact vacuum data')
plt.loglog(h,[float(x['naive_memory_M']) for x in r],'s--',label='Momentum: naive history correction')
plt.xlabel('Grid spacing h');plt.ylabel('maximum absolute constraint residual');plt.title('Naive memory breaks vacuum ADM constraints');plt.legend(fontsize=8);plt.grid(True,which='both',alpha=.25);plt.tight_layout();plt.savefig(P/'memory_constraint_obstruction.png',dpi=180);plt.close()
with (P/'kasner_IVP_convergence.csv').open() as fh:
    rows=list(csv.DictReader(fh))
dt=np.array([float(x['dt']) for x in rows]);Hs=np.array([float(x['maxH']) for x in rows]); ge=np.array([float(x['metric_max_error']) for x in rows])
plt.figure(figsize=(7.3,4.4))
plt.loglog(dt,Hs,'o-',label='Max |Hamiltonian constraint|')
plt.loglog(dt,ge,'s-',label='Final metric error')
plt.loglog(dt,Hs[0]*(dt/dt[0])**4,'--',label='reference: O(dt^4)')
plt.xlabel('Time step dt');plt.ylabel('error');plt.title('Nonlinear Kasner initial-value evolution (RK4)');plt.legend();plt.grid(True,which='both',alpha=.25);plt.tight_layout();plt.savefig(P/'kasner_IVP_convergence.png',dpi=180);plt.close()
# The exact 3-curvature of a wavy slicing of flat 4D spacetime
import sys
sys.path.insert(0,str(P))
from verify_v15 import fields,finite_geometry
n=128;t=.37
f=fields(n,t);g=finite_geometry(f)
plt.figure(figsize=(6.2,5.3))
img=plt.imshow(g['R_gauss'],origin='lower',extent=[0,2*np.pi,0,2*np.pi],cmap='coolwarm')
plt.colorbar(img,label='Intrinsic scalar curvature of 3D slice')
plt.xlabel('x');plt.ylabel('y');plt.title('Curved spatial slice inside flat Minkowski spacetime');plt.tight_layout();plt.savefig(P/'intrinsic_curvature_slice.png',dpi=180);plt.close()
