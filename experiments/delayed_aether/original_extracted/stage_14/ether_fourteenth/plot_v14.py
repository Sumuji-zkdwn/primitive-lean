#!/usr/bin/env python3
"""Make distinct, source-backed diagnostic figures without subplot composites."""
from pathlib import Path
import csv
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
OUT=Path(__file__).resolve().parent

def rows(path):
    d=list(csv.DictReader((OUT/path).open()))
    return {key:np.array([float(r[key]) for r in d]) for key in d[0]}
a=rows('exp_n10_dt0p002.csv')
b=rows('exp_n12_dt0p002.csv')
c=rows('exp_n10_dt0p001.csv')

fig,ax=plt.subplots(figsize=(7.8,4.8))
ax.plot(a['t'],a['max_shear'],marker='o',markersize=2,label='10^3 cells')
ax.plot(b['t'],b['max_shear'],marker='o',markersize=2,label='12^3 cells')
ax.set(xlabel='Model time',ylabel='Maximum trace-free log-metric norm',title='Self-generated metric shear: g = exp(B)')
ax.legend();ax.grid(alpha=.25)
fig.tight_layout();fig.savefig(OUT/'v14_self_generated_shear.png',dpi=170);plt.close(fig)

fig,ax=plt.subplots(figsize=(7.8,4.8))
ax.plot(a['t'],a['min_pair_dot'],marker='o',markersize=2,label='10^3: minimum pair dot')
ax.plot(b['t'],b['min_pair_dot'],marker='o',markersize=2,label='12^3: minimum pair dot')
ax.plot(a['t'],a['min_admissible_certificate'],ls='--',label='10^3: stepwise lower certificate')
ax.plot(b['t'],b['min_admissible_certificate'],ls='--',label='12^3: stepwise lower certificate')
ax.axhline(0,ls=':',color='gray')
ax.set(xlabel='Model time',ylabel='Positive admissibility margin',title='Topology protection by timestep certification')
ax.legend(fontsize=8);ax.grid(alpha=.25)
fig.tight_layout();fig.savefig(OUT/'v14_topology_certificate.png',dpi=170);plt.close(fig)

fig,ax=plt.subplots(figsize=(7.8,4.8))
ax.plot(a['t'],a['relative_energy_budget'],label='dt = 0.002')
ax.plot(c['t'],c['relative_energy_budget'],label='dt = 0.001')
ax.set(xlabel='Model time',ylabel='(E(t) + dissipated - E(0)) / E(0)',title='Time-step refinement: energy/dissipation balance')
ax.legend();ax.grid(alpha=.25)
fig.tight_layout();fig.savefig(OUT/'v14_energy_refinement.png',dpi=170);plt.close(fig)

fig,ax=plt.subplots(figsize=(7.8,4.8))
ax.plot(a['t'],a['max_memory_radial_modulus'],label='10^3 cells')
ax.plot(b['t'],b['max_memory_radial_modulus'],label='12^3 cells')
ax.axhline(3.55,ls=':',color='gray',label='Bounded modulus ceiling')
ax.set(xlabel='Model time',ylabel='Maximum memory tangent modulus',title='Delayed hardening retained in exp-metric model')
ax.legend();ax.grid(alpha=.25)
fig.tight_layout();fig.savefig(OUT/'v14_memory_hardening.png',dpi=170);plt.close(fig)
