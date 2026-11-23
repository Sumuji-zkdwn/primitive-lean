#!/usr/bin/env python3
"""Classical BPS (Prasad-Sommerfield) monopole benchmark, not a new model.
Dimensionless units e=v=1. Analytic radial solution and energy boundary identity.
"""
import json
import numpy as np
from pathlib import Path
from scipy.integrate import trapezoid
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
OUT=Path(__file__).resolve().parent
r=np.geomspace(.04,25,2000)
s=np.sinh(r);c=np.cosh(r)
H=c/s-1/r
K=r/s
Hp=1/r**2-1/s**2
Kp=(s-r*c)/s**2
resH=Hp-(1-K*K)/r**2
resK=Kp+H*K
assert np.max(np.abs(resH))<4e-11,np.max(np.abs(resH))
assert np.max(np.abs(resK))<4e-13,np.max(np.abs(resK))
# BPS radial energy: 4pi int dr [r² H'² +2 H²K²]; exact integral equals boundary term
energy_integrand=r*r*Hp*Hp+2*H*H*K*K
energy_boundary=4*np.pi*H*(1-K*K)
energy_check=4*np.pi*trapezoid(energy_integrand,r)
exact_to_r=energy_boundary[-1]-energy_boundary[0]
assert abs(energy_check-exact_to_r)<2e-5,(energy_check,exact_to_r)
# at large r >20, K tiny, H≈1-1/r, so energy approaches 4pi with power-law tail.
energy_R=4*np.pi*H[-1]*(1-K[-1]**2)
assert abs(energy_R/(4*np.pi)-.96)<1e-9
summary={'BPS_radial_equation_max_residual_H':float(np.max(np.abs(resH))),
         'BPS_radial_equation_max_residual_K':float(np.max(np.abs(resK))),
         'integral_energy_from_r0_to_R':float(energy_check),
         'boundary_energy_difference':float(exact_to_r),
         'energy_at_R_25':float(energy_R),
         'analytical_energy_at_infinite_radius':float(4*np.pi),
         'finite_R_energy_fraction_at_25':float(energy_R/(4*np.pi))}
(OUT/'monopole_benchmark.json').write_text(json.dumps(summary,indent=2),encoding='utf8')
np.savetxt(OUT/'monopole_profile.csv',np.column_stack([r,H,K,Hp,Kp,energy_integrand,energy_boundary]),
           delimiter=',',header='r,H,K,dH_dr,dK_dr,radial_integrand,energy_inside_radius',comments='')
fig,ax=plt.subplots(1,2,figsize=(10,3.8))
ax[0].plot(r,H,label='H(r): Higgs magnitude');ax[0].plot(r,K,label='K(r): gauge profile')
ax[0].set(xlabel='dimensionless radius',ylabel='radial profile',xlim=(0,12),ylim=(-.03,1.08));ax[0].legend()
ax[1].plot(r,energy_boundary/(4*np.pi),label='enclosed energy / 4π')
ax[1].axhline(1,color='gray',linestyle='--',label='total mass = 4π')
ax[1].set(xlabel='dimensionless radius',ylabel='fraction of total energy',xlim=(0,25),ylim=(0,1.05));ax[1].legend()
fig.suptitle('Established BPS monopole: a finite 3D defect with two-derivative field equations')
fig.tight_layout();fig.savefig(OUT/'bps_monopole_benchmark.png',dpi=170);plt.close(fig)
print(json.dumps(summary,indent=2))
