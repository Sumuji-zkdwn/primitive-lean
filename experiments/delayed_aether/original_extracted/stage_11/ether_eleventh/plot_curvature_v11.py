#!/usr/bin/env python3
import csv
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
P=Path(__file__).resolve().parent
rows=list(csv.DictReader(open(P/'metric_cases.csv')))
fig, ax=plt.subplots(figsize=(7.2,4.6))
for n in (8,12,16):
    r=sorted([r for r in rows if int(r['n'])==n],key=lambda row:float(row['alpha']))
    ax.plot([float(x['alpha']) for x in r],
            [float(x['regge_abs_curvature']) for x in r],'.-',label=f'{n} cells / direction')
ax.set(xlabel='texture-to-metric coupling strength',ylabel='sum(edge length × |Regge deficit|)',
       title='Localized field texture induces intrinsic edge curvature')
ax.legend();ax.grid(alpha=.25);fig.tight_layout()
fig.savefig(P/'induced_curvature.png',dpi=160);plt.close(fig)
