#!/usr/bin/env python3
"""Matplotlib plots from reproducible CSVs, no external data or images."""
from pathlib import Path
import csv
import math
import matplotlib.pyplot as plt
P=Path(__file__).resolve().parent

def load(filename):
    with (P/filename).open() as f:
        return [{k:float(v) for k,v in row.items()} for row in csv.DictReader(f)]

c=load('curvature_scan_v31.csv')
flat=math.sqrt(8/3)
fig,ax=plt.subplots(figsize=(8,4.3))
ax.plot([r['internal_edge_x'] for r in c],[r['angle_deficit_rad'] for r in c],lw=2,label='Angle deficit around DE')
ax.axhline(0,lw=1,ls='--')
ax.axvline(flat,lw=1,ls=':',label=f'flat x = {flat:.6f}')
ax.set(xlabel='Interior edge length x',ylabel='Angle deficit δ(x) [radians]',title='3D Pachner 2–3 move: curvature from one internal length')
ax.legend();ax.grid(True,alpha=.25);fig.tight_layout()
fig.savefig(P/'curvature_scan_v31.png',dpi=160);plt.close(fig)

m=load('memory_dynamics_v31.csv')
fig,ax=plt.subplots(figsize=(8,4.3))
ax.plot([r['t'] for r in m],[r['energy'] for r in m],lw=2,label='Energy E')
ax.plot([r['t'] for r in m],[r['dissipated'] for r in m],lw=2,label='Cumulative dissipation D')
ax.plot([r['t'] for r in m],[r['energy']+r['dissipated'] for r in m],lw=1,ls='--',label='E+D (constant)')
ax.set(xlabel='Model time',ylabel='Dimensionless model energy',title='Curvature-memory response (chosen damping law)')
ax.legend();ax.grid(True,alpha=.25);fig.tight_layout()
fig.savefig(P/'memory_energy_v31.png',dpi=160);plt.close(fig)
