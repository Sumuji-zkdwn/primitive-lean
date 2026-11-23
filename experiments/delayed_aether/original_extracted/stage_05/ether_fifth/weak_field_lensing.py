#!/usr/bin/env python3
"""Necessary weak-field spatial-curvature component for observed solar light bending.
This is PPN kinematics; it does not derive Einstein equations or produce a metric dynamically.
"""
from pathlib import Path
import json, csv
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
P=Path(__file__).resolve().parent
GM=1.3271244e20;R=6.957e8;c=299792458.
scale=180/np.pi*3600
# In isotropic weak-field metric: g00=-(1+2 Phi/c²), gij=(1-2 gamma Phi/c²)delta_ij,
# Phi=-GM/r, ray deflection alpha=2(1+gamma)GM/(c² b).
# Angular integration of Born ray-gradient: z=b*tan(theta)
from numpy.polynomial.legendre import leggauss
x,w=leggauss(64)
theta=x*np.pi/2
weights=w*np.pi/2
integral=np.dot(weights,np.cos(theta))
assert abs(integral-2)<1e-14
rows=[]
for g in (-1.,0.,.5,1.,2.):
    exact=2*(1+g)*GM/(c*c*R)*scale
    numeric=(1+g)*GM/(c*c*R)*integral*scale
    assert abs(exact-numeric)<1e-12
    rows.append([g,exact,numeric])
with (P/'weak_field_lensing.csv').open('w',newline='') as f:
    writer=csv.writer(f);writer.writerow(['PPN_gamma','analytic_deflection_arcsec','quadrature_deflection_arcsec']);writer.writerows(rows)
g=np.linspace(-1.5,2,200)
a=2*(1+g)*GM/(c*c*R)*scale
fig,ax=plt.subplots(figsize=(8.3,4.1));ax.plot(g,a)
ax.scatter([-1,0,1],[0,rows[1][1],rows[3][1]])
ax.axhline(rows[3][1],linestyle='--',alpha=.55,color='gray')
ax.set(xlabel='spatial-potential ratio gamma',ylabel='solar-limb ray deflection (arcsec)',title='Light bending requires a non-conformal metric component')
ax.annotate('conformal scalar: 0',xy=(-1,0),xytext=(-1.25,.55),arrowprops=dict(arrowstyle='->'))
ax.annotate('GR: 1.751 arcsec',xy=(1,rows[3][1]),xytext=(.05,2.6),arrowprops=dict(arrowstyle='->'))
fig.tight_layout();fig.savefig(P/'weak_field_lensing.png',dpi=165);plt.close(fig)
result={'quadrature_cos_integral':float(integral),'conformal_arcsec':0.,'g00_only_arcsec':float(rows[1][1]),'gamma_one_arcsec':float(rows[3][1])}
(P/'weak_field_lensing.json').write_text(json.dumps(result,indent=2))
print(json.dumps(result,indent=2))
