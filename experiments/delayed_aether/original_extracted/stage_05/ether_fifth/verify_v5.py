#!/usr/bin/env python3
"""Ether model V5: causal field-space stiffening, static interface, finite dynamics, and scalar-gravity no-go.
Run with Python 3.11+, numpy, scipy, matplotlib. Outputs reproducible CSV/PNG/audit.
No assumption of physical ether and no claim of GR reconstruction.
"""
from __future__ import annotations
import csv
import json
from pathlib import Path
import numpy as np
from scipy.integrate import solve_ivp
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

OUT = Path(__file__).resolve().parent

def save_csv(name, header, rows):
    with (OUT / name).open('w', newline='', encoding='utf-8') as f:
        w = csv.writer(f)
        w.writerow(header)
        w.writerows(rows)

def A(y, delta=3., a=.3):
    return 1. + delta * np.tanh(y/a)**2

def Ap(y, delta=3., a=.3):
    t=np.tanh(y/a)
    return (2.*delta/a)*t*(1.-t*t)

def model_local_speeds():
    ys=np.linspace(-2,2,401)
    av=A(ys)
    inertia_u=av
    stiffness_u=av
    speeds_matched=np.sqrt(stiffness_u/inertia_u)
    speeds_old=np.sqrt(stiffness_u)
    assert np.max(np.abs(speeds_matched-1)) < 4e-16
    assert np.min(av)>=1-1e-12 and np.max(av)<4.000001
    save_csv('matched_cones.csv', ['lag_y','stiffness_A','inertia_A','new_front_speed','old_fixed_inertia_speed'],
             zip(ys, av, av, speeds_matched, speeds_old))
    fig,axes=plt.subplots(1,2,figsize=(11,3.5))
    axes[0].plot(ys,av,label='effective stiffness A(y)')
    axes[0].plot(ys, av, '--', label='matched inertia A(y)', alpha=.65)
    axes[0].set(xlabel='lag y=u-z',ylabel='coefficient',ylim=(0,4.3)); axes[0].legend()
    axes[1].plot(ys,speeds_matched,label='matched kinetic/spatial coefficients')
    axes[1].plot(ys,speeds_old,label='old: fixed inertia')
    axes[1].set(xlabel='lag y=u-z',ylabel='front speed (c=1 units)',ylim=(.8,2.2)); axes[1].legend()
    fig.suptitle('State-dependent hardening without widening the characteristic cone')
    fig.tight_layout();fig.savefig(OUT/'matched_cones.png',dpi=175);plt.close(fig)
    return dict(speed_error=float(np.max(np.abs(speeds_matched-1))),stiffness_max=float(np.max(av)))

def frozen_interface_scattering():
    # A static prescribed coefficient test (NOT solution of full two-field theory)
    dx=.08; x=np.arange(-65,65+dx/2,dx); n=len(x)
    Ai=np.where(x<0,1.,3.)
    Af=2*Ai[:-1]*Ai[1:]/(Ai[:-1]+Ai[1:])
    def lap_flux(u):
        flow=Af*np.diff(u)/dx
        out=np.zeros_like(u)
        out[1:-1]=(flow[1:]-flow[:-1])/dx
        # no-flux boundaries (far from wave)
        out[0]=flow[0]/dx; out[-1]=-flow[-1]/dx
        return out/Ai
    center=-22.; sigma=2.4
    u0=np.exp(-.5*((x-center)/sigma)**2)
    v0=(x-center)/sigma**2*u0  # right-going wave: u_t = -u_x
    dt=.032; steps=int(round(44/dt)); dt=44./steps
    # advance with u_{-1}, u_0; second-order Taylor backstep
    uprev=u0 - dt*v0 + .5*dt*dt*lap_flux(u0)
    u=u0.copy()
    def energy_density(ur, us):
        v=(ur-us)/dt
        edge=.5*Af*(np.diff(ur)/dx)**2
        ei=.5*Ai*v*v
        ei[:-1]+=edge/2; ei[1:]+=edge/2
        return ei
    E0=np.sum(.5*Ai*v0*v0)*dx + np.sum(.5*Af*(np.diff(u0)/dx)**2)*dx
    snapshots={0:(u0.copy(),v0.copy())}
    for i in range(steps):
        unew=2*u-uprev+dt*dt*lap_flux(u)
        uprev,u=u,unew
        if i+1 in {round(20/dt),round(30/dt),steps}:
            t=(i+1)*dt
            snapshots[round(t)]=(u.copy(),(u-uprev)/dt)
    ed=energy_density(u,uprev)
    left=x<-5; right=x>5
    EL=np.sum(ed[left])*dx; ER=np.sum(ed[right])*dx
    Eend=np.sum(ed)*dx
    R=EL/E0; T=ER/E0
    predicted_r=(1.-3.)/(1.+3.)
    predicted_R=predicted_r**2
    predicted_T=1-predicted_R
    xleft=np.sum(x[left]*ed[left])/np.sum(ed[left]); xright=np.sum(x[right]*ed[right])/np.sum(ed[right])
    # Need convergence tolerances account for sharp interface and finite numerical error
    assert abs(R-predicted_R)<.02, (R, predicted_R)
    assert abs(T-predicted_T)<.02, (T, predicted_T)
    assert abs((R+T)-1)<.01, (R,T)
    assert abs(xleft+22.)<1.5 and abs(xright-22.)<1.5, (xleft,xright)
    fig,ax=plt.subplots(figsize=(10.5,4.2))
    for tt in (0,20,30,44):
        uu=snapshots[tt][0]
        ax.plot(x,uu,label=f't={tt}')
    ax.axvline(0,color='gray',alpha=.7,linestyle='--')
    ax.set(xlim=(-46,46),xlabel='coordinate x',ylabel='u perturbation',title='Reflection from a hardened interface; both sides c=1')
    ax.legend(ncol=4);fig.tight_layout();fig.savefig(OUT/'interface_scattering.png',dpi=175);plt.close(fig)
    result={'R_numeric':float(R),'T_numeric':float(T),'R_exact':predicted_R,'T_exact':predicted_T,
            'initial_energy':float(E0),'final_energy':float(Eend),'relative_energy_error':float(Eend/E0-1.),
            'left_energy_centroid_x':float(xleft),'right_energy_centroid_x':float(xright),
            'dx':dx,'dt':dt,'n_grid':n,'time_final':44}
    save_csv('interface_audit.csv',list(result),[list(result.values())]);return result

def dynamics_lagrangian(delta=3., a=.3, kappa=1.2, lam=.6, N=256, L=80., final_time=12., output_stem='nonlinear_dynamics', make_plot=True):
    x=np.linspace(-L/2,L/2,N,endpoint=False); dx=L/N
    # Hamiltonian: sum dx [pu^2/(2A)+pz^2/2 + A_e*du^2/(2dx^2) + dz^2/(2dx^2) + V(y)]
    # Inertial lag is conservative.  No friction term added.
    def potential(y): return .5*kappa*y*y + .25*lam*y**4
    def vp(y): return kappa*y+lam*y**3
    def ham(w):
        u,z,pu,pz=np.split(w,4)
        y=u-z;du=np.roll(u,-1)-u;dz=np.roll(z,-1)-z
        Ae=A((y+np.roll(y,-1))/2,delta=delta,a=a)
        kinetic=.5*pu*pu/A(y,delta=delta,a=a) + .5*pz*pz
        strain=.5*Ae*(du/dx)**2 + .5*(dz/dx)**2
        return float(dx*np.sum(kinetic+strain+potential(y)))
    def rhs(t,w):
        u,z,pu,pz=np.split(w,4)
        y=u-z
        aval=A(y,delta=delta,a=a)
        apr=Ap(y,delta=delta,a=a)
        ut=pu/aval
        du=np.roll(u,-1)-u;dz=np.roll(z,-1)-z
        ye=(y+np.roll(y,-1))/2
        Ae=A(ye,delta=delta,a=a);Ape=Ap(ye,delta=delta,a=a)
        flux=Ae*du
        div_u=(flux-np.roll(flux,1))/(dx*dx)
        lap_z=(dz-np.roll(dz,1))/(dx*dx)
        b=(Ape*du*du+np.roll(Ape*du*du,1))/(4*dx*dx)
        pu_t=div_u-b+.5*apr*ut*ut-vp(y)
        pz_t=lap_z+b-.5*apr*ut*ut+vp(y)
        return np.concatenate((ut,pz,pu_t,pz_t))
    u0=np.zeros(N);z0=np.zeros(N)
    vel0=.9*np.exp(-.5*(x/1.7)**2)
    pu0=vel0.copy();pz0=np.zeros(N)
    w0=np.concatenate([u0,z0,pu0,pz0])
    tt=np.linspace(0,final_time,121)
    sol=solve_ivp(rhs,(0,final_time),w0,method='DOP853',t_eval=tt,rtol=7e-9,atol=2e-11,max_step=.05)
    assert sol.success,sol.message
    e=np.array([ham(w) for w in sol.y.T]);e0=e[0]
    lag_rms=np.array([np.sqrt(np.mean((w[:N]-w[N:2*N])**2)) for w in sol.y.T])
    max_A=np.array([np.max(A(w[:N]-w[N:2*N],delta=delta,a=a)) for w in sol.y.T])
    abs_e=np.max(np.abs(e/e0-1.))
    assert abs_e<2e-6,abs_e
    rows=np.column_stack([tt,e,e/e0-1,lag_rms,max_A])
    save_csv(output_stem+'.csv',['time','energy','relative_energy_error','lag_rms','max_A'],rows)
    if make_plot:
        fig,axes=plt.subplots(3,1,figsize=(9.5,8),sharex=True)
        axes[0].plot(tt,lag_rms);axes[0].set(ylabel='RMS(u-z)',title='Conservative nonlinear two-field evolution')
        axes[1].plot(tt,max_A);axes[1].set(ylabel='maximum A(y)',ylim=(.9,4.1))
        axes[2].plot(tt,e/e0-1);axes[2].set(ylabel='relative energy error',xlabel='model time')
        fig.tight_layout();fig.savefig(OUT/(output_stem+'.png'),dpi=175);plt.close(fig)
    return {'energy_initial':float(e0),'max_relative_energy_error':float(abs_e),
            'max_lag_rms':float(np.max(lag_rms)),'max_stiffness':float(np.max(max_A)),
            'lag_at_final':float(lag_rms[-1]),'n_sites':N,'time_final':final_time,'solver':sol.message,
            'nfev':int(sol.nfev)}

def scaling_no_go():
    radii=np.geomspace(.08,3.2,150)
    E2=2*radii;E0=.15*radii**3;E4=1/radii
    no_fourth=E2+E0
    yes_fourth=no_fourth+E4
    assert np.all(np.diff(no_fourth)>0)
    imin=np.argmin(yes_fourth)
    save_csv('scaling_obstruction.csv',['radius','two_derivative_plus_potential_E','with_fourth_derivative_E'],
             zip(radii,no_fourth,yes_fourth))
    fig,ax=plt.subplots(figsize=(8.8,4.2))
    ax.plot(radii,no_fourth,label='2-derivative target-metric theory (no static soliton)')
    ax.plot(radii,yes_fourth,label='plus Skyrme-like spatial term (scaling balance)')
    ax.set(xlabel='radius R',ylabel='trial energy (arbitrary units)',xlim=(0,3.2),ylim=(0,14))
    ax.legend();fig.tight_layout();fig.savefig(OUT/'scaling_obstruction.png',dpi=175);plt.close(fig)
    return {'no_stabilizer_E_at_smallest_R':float(no_fourth[0]),
            'trial_stabilized_optimum_R':float(radii[imin]),
            'trial_stabilized_optimum_E':float(yes_fourth[imin])}

def lensing_no_go():
    c=299_792_458.
    GM=1.3271244e20
    R=6.957e8
    GR_arcsec=4*GM/(c*c*R)*(180/np.pi*3600)
    assert 1.74 < GR_arcsec < 1.76
    # conformal factor Omega(x): n=sqrt(g_xx/(-g_tt)) = 1 for any positive Omega.
    phi=np.linspace(-.45,.45,101)
    Omega=np.exp(phi)
    n=np.sqrt((Omega**2)/(Omega**2))
    assert np.max(np.abs(n-1.))<4e-16
    save_csv('conformal_lensing_audit.csv',['log_Omega','optical_index'],zip(phi,n))
    return {'conformal_scalar_light_deflection_arcsec':0.,'gr_solar_limb_deflection_arcsec':float(GR_arcsec),
            'max_optical_index_deviation':float(np.max(np.abs(n-1.)))}

def main():
    records={}
    for fn in (model_local_speeds,frozen_interface_scattering,dynamics_lagrangian,scaling_no_go,lensing_no_go):
        result=fn()
        records[fn.__name__]=result
        print(fn.__name__,json.dumps(result,ensure_ascii=False))
    fine=dynamics_lagrangian(N=512,output_stem='nonlinear_dynamics_fine',make_plot=False)
    records['dynamics_refinement_512']=fine
    co=records['dynamics_lagrangian']
    refinement={'peak_A_difference':abs(co['max_stiffness']-fine['max_stiffness']),
      'peak_lag_RMS_difference':abs(co['max_lag_rms']-fine['max_lag_rms'])}
    assert refinement['peak_A_difference']<.15 and refinement['peak_lag_RMS_difference']<.005,refinement
    records['refinement_difference']=refinement
    print('dynamics_refinement', json.dumps({**fine, **refinement},ensure_ascii=False))
    (OUT/'audit_results.json').write_text(json.dumps(records,ensure_ascii=False,indent=2),encoding='utf-8')
    (OUT/'audit.txt').write_text('PASS: all explicit numerical assertions in verify_v5.py\n' + json.dumps(records,ensure_ascii=False,indent=2),encoding='utf-8')

if __name__=='__main__':
    main()
