#!/usr/bin/env python3
"""A numerical and analytic audit of a 3D strain-sourced Skyrme toy model.

No claim of experimentally established gravity. Natural units, no calibration.
Use: python ether_skyrme_gravity.py
"""
from __future__ import annotations
import csv, json, math
from pathlib import Path
import numpy as np
from scipy.integrate import quad
from scipy.special import betainc
from scipy.optimize import minimize_scalar
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

OUT = Path(__file__).resolve().parent
PI = math.pi
# q(x) = (cos F, sin F x/r), F(r) = 2 atan((R/r)^2)
# quadratic strain energy density, quartic Skyrme energy density at R=1:
def rho2(x):
    return 12*x*x/(1+x**4)**2

def rho4(x):
    return 72*x**4/(1+x**4)**4

A = 3*PI*PI*math.sqrt(2)     # E_2(R) = A R
B = 45/16*PI*PI*math.sqrt(2) # E_4(R) = B/R
D22 = 9/4*A                # Coulomb integral for rho_2: D_22(R) = D22 R


def xz(x):
    xx = np.asarray(x)
    return xx**4/(1+xx**4)


def mass2(x):
    return A*betainc(5/4, 3/4, xz(x))


def mass4(x):
    return B*betainc(7/4, 9/4, xz(x))


def potential2_unit(x):
    """Coulomb potential phi= convolution rho2 with 1/(4 pi distance)."""
    x = np.asarray(x, dtype=float)
    return np.where(x > 1e-12, mass2(x)/(4*PI*np.maximum(x,1e-12)), 0.) + 3/(1+x**4)


def baryon_density_integrand(x):
    # B = -(2/pi) integral F' sin^2 F dr
    # F'= -4x/(1+x^4), sinF=2x^2/(1+x^4)
    return 32/PI*x**5/(1+x**4)**3


# verify exact energy and degree using independent quadratures
An = quad(lambda x: 4*PI*x*x*rho2(x), 0, np.inf, epsabs=1e-11)[0]
Bn = quad(lambda x: 4*PI*x*x*rho4(x), 0, np.inf, epsabs=1e-11)[0]
Btop = quad(baryon_density_integrand, 0, np.inf, epsabs=1e-11)[0]
D22n = quad(lambda x: 2*x*rho2(x)*mass2(x), 0, np.inf, epsabs=1e-11)[0]
assert np.isclose(An, A, rtol=1e-11)
assert np.isclose(Bn, B, rtol=1e-11)
assert np.isclose(Btop, 1, rtol=1e-11)
assert np.isclose(D22n, D22, rtol=1e-11)

# Additional strain sourcing comparison (rho2+rho4): quartic-sourced gravity collapses as R->0.
D24 = quad(lambda x: x*(rho2(x)*mass4(x)+rho4(x)*mass2(x)), 0, np.inf, epsabs=1e-10)[0]
D44 = quad(lambda x: 2*x*rho4(x)*mass4(x), 0, np.inf, epsabs=1e-10)[0]
assert D24 > 0 and D44 > 0

def E_core(R): return A*R + B/R

def E_2source(R, coupling): return (A - .5*coupling*D22)*R + B/R

def E_total_source(R, coupling):
    return A*R + B/R - coupling/2*(D22*R+2*D24/R+D44/R**3)

# alpha = g^2/K, g=0.5 and K=1; only the quadratic strain sources h
coupling = 0.25
g = math.sqrt(coupling)
K = 1.
R0 = math.sqrt(B/A)
R1 = math.sqrt(B/(A-0.5*coupling*D22))
E0 = E_core(R0)
E1 = E_2source(R1, coupling)
res0 = minimize_scalar(E_core, bounds=(0.25, 6), method='bounded', options={'xatol':1e-13})
res1 = minimize_scalar(lambda R: E_2source(R, coupling), bounds=(0.25, 6), method='bounded', options={'xatol':1e-13})
assert abs(res0.x-R0) < 1e-7 and abs(res1.x-R1) < 1e-7
# For this analytic profile: h(0) = 3g/K at all R. Linear stiffness at center is 1-gh(0)=1-3alpha.
min_stiffness_coeff = 1 - 3*coupling
assert min_stiffness_coeff > 0

# Far field: distributed radial strain energy (not a placed point source).
field_rows=[]
for d_over_R in (1, 2, 3, 5, 8, 10, 16, 24, 40):
    y=float(d_over_R)
    V=float(potential2_unit(y))
    M=float(mass2(y))
    h_actual = (g/K)*V
    h_far = (g/K)*A/(4*PI*y)
    F_actual = M/(4*PI*y*y)
    F_far = A/(4*PI*y*y)
    field_rows.append(dict(r_over_R=y, h=h_actual, h_approx_point=h_far,
                           h_ratio=h_actual/h_far, enclosed_strain_fraction=M/A,
                           force_test_ratio=F_actual/F_far))

# Two extended radially symmetric solitons (well-separated density superposition approximation):
# F(d) = alpha \int rho2(x) mass2(|d+x|) (d + x dot e) / (4*pi*|d+x|^3) d^3x
# Radial integration over x = t/(1-t) and angle u using Gauss Legendre quadrature.
def pair_force_dimensionless(delta, radial_nodes=800, angular_nodes=96):
    t,w = np.polynomial.legendre.leggauss(radial_nodes)
    t=(t+1)/2; w=w/2
    x=t/(1-t)
    radial_weight=w/(1-t)**2 * 4*PI*x*x*rho2(x)
    mu,wm=np.polynomial.legendre.leggauss(angular_nodes)
    z=delta + x[:,None]*mu[None,:]
    r=np.sqrt(delta**2+x[:,None]**2+2*delta*x[:,None]*mu[None,:])
    centr=mass2(r)/(4*PI*r**3) * z
    return float(np.dot(radial_weight, np.dot(centr, wm)/2))

pair_rows=[]
for delta in (3., 4., 5., 6., 8., 10., 12., 16., 24.):
    raw=pair_force_dimensionless(delta)
    point=A*A/(4*PI*delta**2)
    pair_rows.append(dict(separation_in_radii=delta,
                          force_normalized=raw,
                          point_force_normalized=point,
                          ratio=raw/point,
                          physical_separation=delta*R1,
                          physical_force=coupling*raw,
                          point_physical_force=coupling*point))
# Convergence audit against twice as many radial/angular nodes
checks=[]
for delta in (3., 8., 24.):
    base=next(v['force_normalized'] for v in pair_rows if v['separation_in_radii']==delta)
    refined=pair_force_dimensionless(delta, 1400, 192)
    checks.append(dict(delta=delta, base=base, refined=refined,
                       relative_quadrature_difference=abs(base-refined)/abs(refined)))
assert max(row['relative_quadrature_difference'] for row in checks)<2e-5

# Energetic audit: scaling instability if all strain energies source the massless h.
for R in [0.3, 0.15, 0.08, 0.04]:
    pass
critical_coupling=2*A/D22  # 8/9; an ansatz-only radial criterion

with open(OUT/'summary.json','w',encoding='utf-8') as f:
    json.dump(dict(model='3D S3 order-parameter Skyrme-type medium and massless scalar deformation h',
                   A=A,B=B,Btop=Btop,D22=D22,D24=D24,D44=D44,
                   relative_error_energy_2=abs(An-A)/A,
                   relative_error_energy_4=abs(Bn-B)/B,
                   relative_error_coulomb=abs(D22n-D22)/D22,
                   gravitational_coupling_alpha=coupling,
                   radius_without_coupling=R0,radius_with_coupling=R1,
                   energy_without_coupling=E0,energy_with_coupling=E1,
                   min_quadratic_coefficient=min_stiffness_coeff,
                   radial_critical_coupling=critical_coupling,
                   pair_convergence_audit=checks,
                   caveat='Stability only with respect to uniform scaling within the chosen hedgehog profile; full PDE stability and relativity not established.'),f,indent=2,ensure_ascii=False)
for name, rows in [('single_field.csv',field_rows),('pair_force.csv',pair_rows)]:
    with open(OUT/name,'w',newline='',encoding='utf-8') as f:
        writer=csv.DictWriter(f,fieldnames=list(rows[0].keys()))
        writer.writeheader(); writer.writerows(rows)

# Plot one: energy minimum, and runaway when all elastic energy sources h
R=np.linspace(0.32,2.6,600)
fig,ax=plt.subplots(figsize=(8.6,5.2))
ax.plot(R, [E_core(r) for r in R],label='No long-range coupling',lw=2.2)
ax.plot(R, [E_2source(r,coupling) for r in R],label=r'Quadratic strain sources $h$ ($\alpha=0.25$)',lw=2.2)
ax.scatter([R0,R1],[E0,E1],s=55,zorder=5)
ax.annotate(f'R*={R0:.4f}',(R0,E0),xytext=(R0+0.1,E0+7),arrowprops={'arrowstyle':'-'},fontsize=10)
ax.annotate(f'R*={R1:.4f}',(R1,E1),xytext=(R1+0.2,E1-14),arrowprops={'arrowstyle':'-'},fontsize=10)
ax.set(xlabel='Soliton radius R (model units)',ylabel='Effective static energy',title='3D topological defect: stability against radial rescaling')
ax.grid(alpha=.25);ax.legend()
fig.tight_layout();fig.savefig(OUT/'energy_radius.png',dpi=160);plt.close(fig)

fig,ax=plt.subplots(figsize=(8.6,5.2))
R=np.geomspace(.02,3,650)
ax.plot(R,[E_core(r) for r in R],label='No scalar coupling')
ax.plot(R,[E_2source(r,.25) for r in R],label='Coupling only to quadratic strain')
ax.plot(R,[E_total_source(r,.25) for r in R],label='Coupling to ALL strain energy (collapses)')
ax.set_xscale('log');ax.set_ylim(-450,350)
ax.set(xlabel='Radius R (log scale)',ylabel='Effective energy',title='Source-choice counterexample: quartic-energy sourcing causes collapse')
ax.grid(alpha=.25);ax.legend(loc='upper right');fig.tight_layout();fig.savefig(OUT/'source_choice_collapse.png',dpi=160);plt.close(fig)

fig,ax=plt.subplots(figsize=(8.6,5.2))
deltas=np.array([p['separation_in_radii'] for p in pair_rows]);ratios=np.array([p['ratio'] for p in pair_rows]);forces=np.array([p['force_normalized'] for p in pair_rows])
ax.plot(deltas,ratios,'o-',label='Force from two distributed strain sources / point inverse-square')
ax.axhline(1,ls='--',c='k',label='Far-field inverse-square')
ax.set(xlabel='Separation / soliton radius',ylabel='Force ratio',title='Force approaches inverse-square without inserting a point source')
ax.set_ylim(min(.85, float(min(ratios))-.015),1.025)
ax.grid(alpha=.25);ax.legend(loc='lower right');fig.tight_layout();fig.savefig(OUT/'pair_force_ratio.png',dpi=160);plt.close(fig)

print('A',A,'B',B,'D22',D22,'D24',D24,'D44',D44)
print('winding B',Btop,'R0',R0,'R1',R1,'E0',E0,'E1',E1)
print('radial instability coupling critical',critical_coupling,'local quadratic coefficient',min_stiffness_coeff)
print('field',*field_rows,sep='\n')
print('pair',*pair_rows,sep='\n')
print('checks',checks)
print('collapse E at R=0.1',E_total_source(.1,coupling),'R=0.02',E_total_source(.02,coupling))
