#!/usr/bin/env python3
"""V29: local seven-edge distance stencil, metric decomposition and simple-wave counterexample.
All displayed results can be regenerated with `python verify_v29.py`.
No Einstein action or graviton dynamics derived from this distance stencil.
"""
from __future__ import annotations
import csv, json, math
from pathlib import Path
import numpy as np
import sympy as sp
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ROOT=Path(__file__).resolve().parent
OUT=lambda s: ROOT/s
V=[(1,0,0),(0,1,0),(0,0,1),(1,1,0),(1,0,1),(0,1,1),(1,1,1)]
M=sp.Matrix([[v[0]**2,v[1]**2,v[2]**2,2*v[0]*v[1],2*v[0]*v[2],2*v[1]*v[2]] for v in V])
r=sp.Matrix([1,1,1,-1,-1,-1,1])

def hmat(c):
    return sp.Matrix([[c[0],c[3],c[4]],[c[3],c[1],c[5]],[c[4],c[5],c[2]]])
def hvec(H):
    return sp.Matrix([H[0,0],H[1,1],H[2,2],H[0,1],H[0,2],H[1,2]])

d=sp.Matrix([1,2,3]); d2=(d.T*d)[0]
S=sp.Matrix([[2*d[0],0,0],[0,2*d[1],0],[0,0,2*d[2]],[d[1],d[0],0],[d[2],0,d[0]],[0,d[2],d[1]]])
C=sp.Matrix([[d2-d[0]**2,d2-d[1]**2,d2-d[2]**2,-2*d[0]*d[1],-2*d[0]*d[2],-2*d[1]*d[2]]])
P=sp.eye(3)-(d*d.T)/d2
T=sp.Matrix.hstack(*[hvec(P*hmat(sp.eye(6)[:,j])*P-sp.Rational(1,2)*P*sp.trace(P*hmat(sp.eye(6)[:,j])*P)) for j in range(6)])
I6=hvec(sp.eye(3))
ttb=T.columnspace()
# Canonical momentum uses off-diagonal canonical P_xy=2 pi_xy.
Momentum=sp.Matrix([[d[0],0,0,d[1]/2,d[2]/2,0],
                    [0,d[1],0,d[0]/2,0,d[2]/2],
                    [0,0,d[2],0,d[0]/2,d[1]/2]])
# sp.Matrix with integers /2 in Python can produce exact floats unless sympified; above d are sympy Integers.
assert M.rank()==6 and r.T*M == sp.zeros(1,6)
assert S.rank()==3 and C.rank()==1 and C*S == sp.zeros(1,3)
assert T.rank()==2 and T*T==T and T*S==sp.zeros(6,3) and C*T==sp.zeros(1,6)
assert sp.Matrix.hstack(S,I6,*ttb).rank()==6
assert Momentum.rank()==3 and C*Momentum.T==sp.zeros(1,3)
assert sp.Matrix.vstack(C,Momentum).rank()==4
assert r.dot(r)==7
# Matrix projection identity (orthogonal decomposition into metric and one mismatch)
Q=M*(M.T*M).inv()*M.T
assert Q == sp.eye(7)-r*r.T/7

npM=np.array(M,float)
npR=np.array(r,float).reshape(-1)
rng=np.random.default_rng(29023)
metric_err=[]; mindet=[]; nonmetric_residual=[]
for _ in range(300):
    x=rng.normal(0,0.045,6)
    H=np.array(hmat(sp.Matrix([float(z) for z in x])),float)
    g=np.eye(3)+H
    mineig=np.linalg.eigvalsh(g).min()
    assert mineig>0
    b=npM@x
    fit=np.linalg.lstsq(npM,b,rcond=None)[0]
    metric_err.append(np.max(np.abs(fit-x)))
    mindet.append(mineig)
    assert abs(npR@b)<1e-13
    # a truly independent body-diagonal measurement creates a 1-d residual
    b[-1]+=rng.normal(0,0.035)
    resid=b-npM@np.linalg.lstsq(npM,b,rcond=None)[0]
    assert np.linalg.norm(resid-(npR@b)*npR/7)<1e-12
    nonmetric_residual.append(abs(npR@b))

# A smooth vertex displacement embedded in flat R^3 can have NONZERO seven-bar residual.
# u_x=A sin(2pi(y+z)), y=z=1/8; all actual points remain in a single Euclidean R^3.
rows=[]
Amp=0.01
for N in [16,24,32,48,64,96,128,192]:
    a=1/N
    theta=2*np.pi/N
    mismatch=2*a*Amp*(np.cos(2*theta)-2*np.cos(theta)+1)
    expected=-2*Amp*(2*np.pi)**2*a**3
    rows.append(dict(N=N,a=a,mismatch=mismatch,abs_mismatch=abs(mismatch),
                     mismatch_over_a3=mismatch/a**3,asymptotic=expected))
with open(OUT('embedding_mismatch.csv'),'w',newline='') as f:
    w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
fit_slope=float(np.polyfit(np.log([x['a'] for x in rows[-5:]]),np.log([x['abs_mismatch'] for x in rows[-5:]]),1)[0])
fig,ax=plt.subplots(figsize=(7.2,4.5))
ax.loglog([x['a'] for x in rows],[x['abs_mismatch'] for x in rows], 'o-',label='Flat embedded displacement: |7-link residual|')
ax.loglog([x['a'] for x in rows],[abs(x['asymptotic']) for x in rows],'--',label='Asymptotic O(a³)')
ax.set_xlabel('Lattice spacing a'); ax.set_ylabel('Absolute 7-link mismatch'); ax.set_title('Naive link mismatch is NOT intrinsic curvature')
ax.grid(True,which='both',alpha=.25); ax.legend();fig.tight_layout();fig.savefig(OUT('flat_embedding_false_defect.png'),dpi=175);plt.close(fig)

# 3D periodic grid: test exact identities for central differences on N=17.
N3=17; coords=np.arange(N3)*2*np.pi/N3
X,Y,Z=np.meshgrid(coords,coords,coords,indexing='ij')
xi=np.stack([0.06*np.sin(X+2*Y)+0.04*np.cos(Z),
            0.05*np.cos(Y+Z)+0.02*np.sin(X),
            0.03*np.sin(X+Y+Z)],axis=-1)
def D(arr,j):
    return (np.roll(arr,-1,axis=j)-np.roll(arr,1,axis=j))/2
hh=np.empty((N3,N3,N3,3,3))
for i in range(3):
    for j in range(3):hh[...,i,j]=D(xi[...,j],i)+D(xi[...,i],j)
trace=np.trace(hh,axis1=-2,axis2=-1)
curvature=np.zeros((N3,N3,N3))
for i in range(3):
    for j in range(3):curvature+=D(D(hh[...,i,j],i),j)
for i in range(3):curvature-=D(D(trace,i),i)
# all six linearly independent local length probes reconstruct h
H6=np.stack([hh[...,0,0],hh[...,1,1],hh[...,2,2],hh[...,0,1],hh[...,0,2],hh[...,1,2]],axis=-1)
local_l=np.einsum('ra,...a->...r',npM,H6)
local_delta=np.einsum('r,...r->...',npR,local_l)
assert np.max(np.abs(curvature))<1e-12
assert np.max(np.abs(local_delta))<1e-12

# 1D-in-z modes with a 3D symmetric metric; SAME local wave law for all six link-derived fields.
Nz=64;dt=0.2; steps=700;z=np.arange(Nz);k=2*np.pi*2/Nz
omega_theory=2/dt*np.arcsin(dt*np.sin(k/2))
weights=np.array([1.,1.,1.,2.,2.,2.])

def lap(q):return np.roll(q,-1,axis=0)-2*q+np.roll(q,1,axis=0)
def energy(q1,q2):
    dv=(q2-q1)/dt
    grad1=np.roll(q1,-1,axis=0)-q1
    grad2=np.roll(q2,-1,axis=0)-q2
    return float(np.sum(weights*(0.5*dv*dv+0.5*grad1*grad2)))

initials={}
plus=np.zeros((Nz,6));plus[:,0]=0.55*np.cos(k*z);plus[:,1]=-0.55*np.cos(k*z);plus[:,3]=0.55*np.sin(k*z)
scalar=np.zeros((Nz,6));scalar[:,0]=np.cos(k*z);scalar[:,1]=np.cos(k*z)
gauge=np.zeros((Nz,6));gauge[:,4]=np.sin(k*z) # pure spatial gradient of u_x in z
initials['two_TT']=plus
initials['transverse_scalar']=scalar
initials['pure_displacement_gauge']=gauge
records=[]; drift={}; measured_frequencies={}
for name,q0 in initials.items():
    prev=q0.copy();cur=q0+0.5*dt*dt*lap(q0)
    e0=energy(prev,cur)
    energies=[]; amps=[]
    for step in range(steps):
        next_q=2*cur-prev+dt*dt*lap(cur)
        E=energy(cur,next_q)
        energies.append(E)
        curv=-D(D(cur[:,0]+cur[:,1],0),0)
        # Normalized orthogonal decomposition for a z-wave
        tt=np.stack([0.5*(cur[:,0]-cur[:,1]),cur[:,3]],axis=-1)
        scalar_amp=np.sqrt(np.sum((cur[:,0]+cur[:,1])**2)/2)
        gauge_amp=np.sqrt(np.sum(cur[:,4]**2+cur[:,5]**2))
        tt_amp=np.sqrt(np.sum(tt[:,0]**2+tt[:,1]**2))
        row=dict(case=name,t=(step+1)*dt,energy=E,relative_energy=E/e0,
                 scalar_curvature_rms=float(np.sqrt(np.mean(curv**2))),
                 tt_amplitude=float(tt_amp),scalar_amplitude=float(scalar_amp),
                 gauge_amplitude=float(gauge_amp))
        records.append(row)
        # projected Fourier component of the actual 2nd-order time solver
        amp0=np.sum(cur[:,0]*np.cos(k*z))
        amp1=np.sum(cur[:,3]*np.sin(k*z))
        amp2=np.sum(cur[:,4]*np.sin(k*z))
        amps.append([amp0,amp1,amp2])
        prev,cur=cur,next_q
    drift[name]=float(max(abs(e/e0-1) for e in energies))
    # Fourier temporal peak is a finite-window estimate; exact discrete mode frequency formula above.
    amps=np.array(amps)
    nontrivial=next(c for c in range(3) if np.std(amps[:,c])>1e-5)
    waveform=amps[:,nontrivial]
    # Estimate via adjacent time samples cos(omega*dt) = (y[n+1]+y[n-1])/(2*y[n]); LS better.
    x=waveform[1:-1]; yy=(waveform[2:]+waveform[:-2])/2
    omega_measured=float(np.arccos(np.clip((x@yy)/(x@x),-1,1))/dt)
    measured_frequencies[name]=omega_measured
with open(OUT('wave_counterexample.csv'),'w',newline='') as f:
    w=csv.DictWriter(f,fieldnames=list(records[0]));w.writeheader();w.writerows(records)
fig,axes=plt.subplots(2,1,figsize=(8.2,7.0),sharex=True)
for name in initials:
    rr=[x for x in records if x['case']==name]
    axes[0].semilogy([r['t'] for r in rr],[max(1e-17,abs(r['relative_energy']-1)) for r in rr],label=name)
    attr={'two_TT':'tt_amplitude','transverse_scalar':'scalar_amplitude','pure_displacement_gauge':'gauge_amplitude'}[name]
    axes[1].plot([r['t'] for r in rr],[r[attr] for r in rr],label=name)
axes[0].set_ylabel('Relative discrete energy error');axes[0].set_ylim(1e-17,1e-12)
axes[0].set_title('A local wave update propagates ALL edge-metric sectors')
axes[1].set_xlabel('Model time');axes[1].set_ylabel('Sector field amplitude (oscillatory)')
axes[0].legend(fontsize=8);axes[1].legend(fontsize=8)
for ax in axes:ax.grid(True,alpha=.25)
fig.tight_layout();fig.savefig(OUT('six_mode_no_go.png'),dpi=175);plt.close(fig)

# A full-rank positive quadratic kinetic with uniform elastic energy has six independent waves.
# The two physical tensor modes are NOT selected without separate gauge/constraint assumptions.
lap_eigen=4*np.sin(k/2)**2
Fmat=(2-dt**2*lap_eigen)*np.eye(6)
dynamic_transition=np.block([[Fmat,-np.eye(6)], [np.eye(6),np.zeros((6,6))]])
eigvals=np.linalg.eigvals(dynamic_transition)
# six copies of each propagating frequency, including the scalar and displacement-like sectors
phase=np.angle(eigvals)
assert np.sum(phase>0)==6 and np.sum(phase<0)==6
assert np.max(abs(abs(phase)-omega_theory*dt))<1e-10

report={
 'model':'seven_oriented_squared_links_to_local_metric_plus_one_mismatch',
 'date':'2026-11-23',
 'input':'seven squared link lengths at each corner, six local symmetric metric components; no Einstein action',
 'algebra':{
   'metric_map_rank':int(M.rank()),'metric_mismatch_dimension':1,
   'strain_gauge_rank':int(S.rank()),'scalar_curvature_constraint_rank':int(C.rank()),
   'TT_projector_rank':int(T.rank()),'momentum_constraint_rank':int(Momentum.rank()),
   'four_linear_first_class_constraints':int(sp.Matrix.vstack(C,Momentum).rank()),
   'configuration_dof_after_scalar_constraint_and_gauge':int(6-int(C.rank())-int(S.rank())),
   'phase_space_dof_after_four_first_class_constraints':int(12-2*4),
   'canonical_pairs':2,
   'exact_identities':['r^T M=0','T^2=T','T S=0','C S=0','C T=0','C momentum^T=0']
 },
 'numeric':{
   'positive_metric_trials':300, 'minimum_spd_eigenvalue':float(min(mindet)),
   'max_metric_reconstruction_error':float(max(metric_err)),
   'random_nonmetric_residual_mean':float(np.mean(nonmetric_residual)),
   'false_mismatch_scaling_slope':fit_slope,
   'max_gauge_curvature_residual_17cube':float(np.max(abs(curvature))),
   'max_gauge_seven_link_mismatch_17cube':float(np.max(abs(local_delta))),
   'local_wave_omega_theory':float(omega_theory),
   'local_wave_frequency_by_sector':measured_frequencies,
   'local_wave_energy_relative_max_drifts':drift,
   'local_wave_eigenvalue_positive_frequency_multiplicity':int(np.sum(phase>0)),
   'local_wave_eigenvalue_negative_frequency_multiplicity':int(np.sum(phase<0))
 },
 'interpretation':'Seven measured local distances split into one non-quadratic residual + three displacement/pure-gauge metric modes + one scalar-curvature mode + two TT metric modes, modewise for nonzero derivative symbol. Generic positive local wave kinetic propagates all six metric modes: two are not spontaneously selected.',
 'limitations':['geometry is a seven-edge local cubical stencil, not a complete globally glued Regge triangulation',
                'TT decomposition and curvature derived using central differences on a flat reference background',
                'finite link mismatch is not a gauge-invariant curvature quantity: a smooth Euclidean embedding creates a nonzero mismatch O(a^3)',
                'GR Hamiltonian and momentum constraints are assumed in the two-pair count, not derived from edge dynamics',
                'wave evolution is a simple local six-component wave equation, not GR or emergent graviton dynamics',
                'no damping, irreversible stiffness, topology or universal gravitational coupling is derived']
}
OUT('audit_v29.json').write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'exact_decomposition':'7 = 1 + 3 + 1 + 2',
 'TT_rank':int(T.rank()),'curvature_false_mismatch_slope':fit_slope,
 'gauge_curvature_error':float(np.max(abs(curvature))),
 'energy_drifts':drift,'omega_theory':omega_theory,'omega_measured':measured_frequencies},indent=2))
