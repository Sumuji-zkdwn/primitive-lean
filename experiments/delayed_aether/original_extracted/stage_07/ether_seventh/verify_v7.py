#!/usr/bin/env python3
"""Reproducible v7: intrinsic metric shear vs displacement strain, linear spin-2 tests.

Dependencies: numpy, sympy, matplotlib. Run: python verify_v7.py
The equations of linearised GR used here are a benchmark, NOT derived from an ether.
"""
from __future__ import annotations
from pathlib import Path
import json
import csv
import hashlib
import numpy as np
import sympy as s
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

OUT = Path(__file__).resolve().parent
ETA = s.diag(-1,1,1,1)
HALF = s.Rational(1,2)

def einstein_fourier(k, h):
    """Linearised Einstein tensor for exp(i k_mu x^mu), covariant k and h."""
    kup = ETA*k
    k2 = (k.T * kup)[0]
    tr = s.trace(ETA*h)
    hk = h*kup
    ric = -HALF*(k*hk.T + hk*k.T - k2*h - (k*k.T)*tr)
    rsc = - (kup.T*h*kup)[0] + k2*tr
    return ric-HALF*ETA*rsc

def riemann_fourier(k,h):
    # Convention R_{mu nu rho sig} = 1/2(h_{mu sig,nu rho}
    # +h_{nu rho,mu sig}-h_{mu rho,nu sig}-h_{nu sig,mu rho})
    return [[[[s.expand(-HALF*(k[rr]*k[nu]*h[mu,ss]
                         + k[ss]*k[mu]*h[nu,rr]
                         - k[ss]*k[nu]*h[mu,rr]
                         - k[rr]*k[mu]*h[nu,ss]))
               for ss in range(4)] for rr in range(4)]
             for nu in range(4)] for mu in range(4)]

def symzero(x):
    return s.expand(x) == 0

def symbol_tests():
    kv=s.symbols('k0 k1 k2 k3', real=True)
    k=s.Matrix(kv)
    H={}
    for i in range(4):
        for j in range(i,4): H[(i,j)] = s.Symbol(f'h{i}{j}',real=True)
    h=s.Matrix(4,4,lambda i,j:H[(min(i,j),max(i,j))])
    xi=s.Matrix(s.symbols('xi0:4', real=True))
    G=einstein_fourier(k,h)
    bianchi=k.T*ETA*G
    assert all(symzero(bianchi[0,i]) for i in range(4)), 'Bianchi identity failed'
    gauge=k*xi.T + xi*k.T
    gauge_einstein=einstein_fourier(k,gauge)
    assert all(symzero(gauge_einstein[i,j]) for i in range(4) for j in range(4)), 'Gauge invariance failed'
    # Full linearised Riemann of a 4D coordinate displacement vanishes.
    rg=riemann_fourier(k,gauge)
    assert all(symzero(rg[i][j][r][t]) for i in range(4) for j in range(4) for r in range(4) for t in range(4)), 'Flat pure gauge Riemann failed'
    omega,kz=s.symbols('omega kz',real=True)
    wavek=s.Matrix([-omega,0,0,kz])
    hp=s.zeros(4); hp[1,1]=1;hp[2,2]=-1
    hx=s.zeros(4); hx[1,2]=1;hx[2,1]=1
    # For a TT wave, G = (k^2/2)h, k^2=kz^2-omega^2.
    for p in (hp,hx):
        ans=einstein_fourier(wavek,p)
        target=HALF*(kz**2-omega**2)*p
        assert all(symzero(ans[i,j]-target[i,j]) for i in range(4) for j in range(4))
    tidal=riemann_fourier(wavek,hp)[0][1][0][1]
    assert symzero(tidal-omega**2/2)
    # Static Newton solution h00=-2phi, hij=-2phi deltaij: G00=2 Laplacian phi.
    phi=s.Symbol('phi',real=True)
    spatial_k=s.Matrix([0,*s.symbols('kx ky kz',real=True)])
    hn=s.diag(-2*phi,-2*phi,-2*phi,-2*phi)
    Gn=einstein_fourier(spatial_k,hn)
    kk=sum(spatial_k[i]**2 for i in range(1,4))
    assert symzero(Gn[0,0]+2*kk*phi)
    assert all(symzero(Gn[i,j]) for i in range(4) for j in range(4) if (i,j)!=(0,0))
    return dict(bianchi_symbolic=True, gauge_symbolic=True,
                pure_displacement_flat_symbolic=True,
                two_polarizations_obey_null_wave=True,
                plus_tidal_curvature=str(tidal),
                newton_static_linearized=True,
                note='Linearized GR equations were assumed for benchmarking, not derived from ether.')

def tt_projector(k,h):
    n = k/np.linalg.norm(k)
    P = np.eye(3)-np.outer(n,n)
    return P@h@P-0.5*P*np.trace(P@h)

def tt_tests():
    rng=np.random.default_rng(20261122)
    max_symgrad=max_trace=max_one=0.
    equalities=[]
    for _ in range(2048):
        k=rng.normal(size=3)
        u=rng.normal(size=3)
        phi=rng.normal()
        strain=np.outer(k,u)+np.outer(u,k)
        sym_norm=np.linalg.norm(tt_projector(k,strain))
        tr_norm=np.linalg.norm(tt_projector(k,phi*np.eye(3)))
        max_symgrad=max(max_symgrad,sym_norm)
        max_trace=max(max_trace,tr_norm)
        n=k/np.linalg.norm(k)
        a=np.array([1.,0.,0.]) if abs(n[0])<0.9 else np.array([0.,1.,0.])
        e1=a-n*np.dot(n,a);e1/=np.linalg.norm(e1)
        e2=np.cross(n,e1)
        plus=np.outer(e1,e1)-np.outer(e2,e2)
        cross=np.outer(e1,e2)+np.outer(e2,e1)
        max_one=max(max_one,np.linalg.norm(tt_projector(k,plus)-plus),np.linalg.norm(tt_projector(k,cross)-cross))
        equalities.append([float(sym_norm),float(tr_norm),float(np.linalg.norm(tt_projector(k,plus))),float(np.linalg.norm(tt_projector(k,cross)))])
    with (OUT/'tt_projection_samples.csv').open('w',newline='') as f:
        w=csv.writer(f);w.writerow(['symgrad_tt_norm','scalar_tt_norm','plus_tt_norm','cross_tt_norm']);w.writerows(equalities)
    assert max_symgrad < 1e-12 and max_trace < 1e-12 and max_one < 1e-12
    return dict(random_directions=2048, max_tt_symgrad=max_symgrad,
                max_tt_isotropic=max_trace,max_projector_error=max_one,
                expected_polarization_norm=np.sqrt(2))

def laplacian(u,dx):
    return (np.roll(u,-1,axis=-1)-2*u+np.roll(u,1,axis=-1))/dx**2

def periodic_gradient(u,dx):
    return (np.roll(u,-1,axis=-1)-u)/dx

def wave_tests():
    # 1D spatial dependence of the transverse traceless metric perturbation.
    L=80.0; N=640; dx=L/N; dt=0.05; c=1.; end=22.0
    z=np.arange(N)*dx; x0=14.0; x1=29.0
    plus=np.exp(-0.5*((z-x0)/2.0)**2)
    cross=0.68*np.exp(-0.5*((z-x1)/2.6)**2)
    h0=np.stack([plus,cross])
    v0=-c*(np.roll(h0,-1,axis=-1)-np.roll(h0,1,axis=-1))/(2*dx)
    hprev=h0-dt*v0+0.5*dt**2*c**2*laplacian(h0,dx)
    hcur=h0.copy()
    nsteps=int(round(end/dt))
    times=[]; energy=[]; centers_plus=[];centers_cross=[]
    at={0:hcur.copy()}
    def energy_half(u,prev):
        # Exact quadratic conserved energy for periodic leapfrog wave scheme.
        return dx*(0.5*np.sum(((u-prev)/dt)**2)
                  +0.5*c*c*np.sum(periodic_gradient(u,dx)*periodic_gradient(prev,dx)))
    E0=energy_half(hcur,hprev)
    for n in range(nsteps+1):
        t=n*dt
        if n in (0, nsteps//2, nsteps): at[n]=hcur.copy()
        times.append(t)
        energy.append(energy_half(hcur,hprev))
        centers_plus.append(np.sum(z*hcur[0]**2)/np.sum(hcur[0]**2))
        centers_cross.append(np.sum(z*hcur[1]**2)/np.sum(hcur[1]**2))
        hn=2*hcur-hprev+dt**2*c**2*laplacian(hcur,dx)
        hprev,hcur=hcur,hn
    energy=np.array(energy)
    err=np.max(np.abs(energy-E0))/E0
    assert err < 1e-10, f'energy drift={err}'
    times=np.array(times)
    cp=np.array(centers_plus);cx=np.array(centers_cross)
    fitp=np.polyfit(times,cp,1);fitx=np.polyfit(times,cx,1)
    assert abs(fitp[0]-1)<0.01 and abs(fitx[0]-1)<0.01, (fitp[0],fitx[0])
    with (OUT/'tensor_wave_timeseries.csv').open('w',newline='') as f:
        w=csv.writer(f);w.writerow(['t','E_half','relative_energy_error','plus_center','cross_center'])
        w.writerows(zip(times,energy,(energy-E0)/E0,cp,cx))
    fig,axs=plt.subplots(2,1,figsize=(9.4,6.7),sharex=True,layout='constrained')
    colors=plt.rcParams['axes.prop_cycle'].by_key()['color']
    for ind, name,ax in [(0,'plus',axs[0]),(1,'cross',axs[1])]:
        for i,n in enumerate(sorted(at)):
            ax.plot(z,at[n][ind],label=f't={n*dt:.1f}',color=colors[i])
        ax.set_ylabel(name+' mode amplitude');ax.grid(alpha=.18);ax.legend()
    axs[1].set_xlabel('z (model units)')
    fig.suptitle('Two independent transverse-traceless waves (linear benchmark)')
    fig.savefig(OUT/'tensor_wave_propagation.png',dpi=180)
    plt.close(fig)
    fig, ax=plt.subplots(figsize=(8.7,3.7),layout='constrained')
    ax.plot(times,(energy-E0)/E0,lw=1.2)
    ax.set(xlabel='t (model units)',ylabel='(E - E0)/E0',title='Conserved discrete wave energy (leapfrog)')
    ax.grid(alpha=.2);fig.savefig(OUT/'tensor_wave_energy.png',dpi=180);plt.close(fig)
    return dict(grid_N=N, dx=dx, dt=dt, end_time=end,
                plus_center_speed=float(fitp[0]), cross_center_speed=float(fitx[0]),
                max_relative_discrete_energy_drift=float(err),
                model='gauge-fixed TT wave equation, not dynamical emergence from a gel')


def main():
    results={'symbolic':symbol_tests(),'tt_projection':tt_tests(),'waves':wave_tests()}
    (OUT/'audit_v7.json').write_text(json.dumps(results,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps(results,ensure_ascii=False,indent=2))
if __name__=='__main__':main()
