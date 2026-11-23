#!/usr/bin/env python3
"""Plots only derived data from verified 4D 2-4 Euclidean Regge formulas."""
from pathlib import Path
from math import sqrt
import csv
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from verify_v32 import angle_deficit, reduced_action, regge_gradient

ROOT=Path(__file__).resolve().parent
xf=sqrt(5/2)
xc=sqrt(2)
xs=[0.7+(sqrt(8/3)-0.7-0.012)*j/359 for j in range(360)]
f0=reduced_action(xf)
rows=[]
for x in xs:
    rows.append({'x':x, 'x_sq':x*x,
                 'angle_deficit':angle_deficit(x),
                 'S_minus_S_flat':reduced_action(x)-f0,
                 'Regge_gradient':regge_gradient(x)})
with (ROOT/'regge_curve_v32.csv').open('w',newline='',encoding='utf8') as f:
    w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)

fig,ax=plt.subplots(figsize=(8.4,4.8))
ax.plot(xs,[r['S_minus_S_flat'] for r in rows],linewidth=2,label='Euclidean Regge action − flat value')
ax.axvline(xc,linestyle='--',alpha=.7,label='curved stationary point')
ax.axvline(xf,linestyle=':',alpha=.7,label='flat stationary point')
ax.scatter([xc,xf],[reduced_action(xc)-f0,0],zorder=5)
ax.set_xlabel('interior edge x (boundary edges = 1)')
ax.set_ylabel('S_R(x) − S_R(sqrt(5/2))')
ax.set_title('4D Regge 2–4 patch: two stationary points')
ax.legend(fontsize=9)
fig.tight_layout()
fig.savefig(ROOT/'regge_stationary_structure_v32.png',dpi=175)
plt.close(fig)

fig,ax=plt.subplots(figsize=(8.4,4.8))
ax.plot(xs,[r['angle_deficit'] for r in rows],linewidth=2,label='interior triangle deficit δ(x)')
ax.axhline(0,linestyle='--',alpha=.6)
ax.axvline(xc,linestyle=':',alpha=.7,label='nonflat stationary point')
ax.axvline(xf,linestyle='--',alpha=.7,label='unique flat point')
ax.set_xlabel('interior edge x')
ax.set_ylabel('angle deficit (radians)')
ax.set_title('Curvature vs one interior edge in a 4D simplex patch')
ax.legend(fontsize=9)
fig.tight_layout()
fig.savefig(ROOT/'angle_deficit_v32.png',dpi=175)
plt.close(fig)
print('Plots and 360-row curve CSV saved')
