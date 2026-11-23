#!/usr/bin/env python3
"""Time-symmetric, non-spherical Einstein-Hamiltonian initial-data constraint.

Matter = SU(2) Skyrme hedgehog + chi memory field (v16/v17 action), affinely
ellipsoidally distorted, q(x)=q0(Mx), chi(x)=chi0(Mx), det M=1.
Conformally flat spatial metric gamma_ij=psi^4 delta_ij, K_ij=0, P_q=P_chi=0.

Hamiltonian constraint: Delta psi = -2*pi*G*(psi*e2+psi^-3*e4+psi^5*V)
Momentum constraint holds identically from time symmetry and zero flux.

Boundary: multipole approximation at finite cubic domain (monopole+quadrupole),
NOT an exact asymptotically flat outer condition. Discrete solve is exact to
round-off for interior 7-point Laplacian; continuum truncation remains.
"""
from __future__ import annotations
import numpy as np
from scipy.fft import dstn,idstn
from pathlib import Path
import time, json, csv
from verify_v18 import density,make_grid,G
OUT=Path(__file__).resolve().parent

def make_dirichlet_grid(n=64,L=15.):
    h=2*L/(n-1)
    x=np.linspace(-L,L,n)
    return n,L,h,x,x[:,None,None],x[None,:,None],x[None,None,:]

def source_moments(src,grid):
    n,L,h,xx,X,Y,Z=grid
    vol=h**3
    mass=float(np.sum(src)*vol)
    x2=float(np.sum(src*X*X)*vol)
    y2=float(np.sum(src*Y*Y)*vol)
    z2=float(np.sum(src*Z*Z)*vol)
    return mass, 2*x2-y2-z2, 2*y2-x2-z2, 2*z2-x2-y2

def boundary(grid,mom):
    n,L,h,xx,X,Y,Z=grid
    mass,qx,qy,qz=mom
    # full boundary arrays via broadcasting
    rr=np.sqrt(X*X+Y*Y+Z*Z)
    r3=rr**3
    safe_rr=np.where(rr>0,rr,1.)
    ub=G*.5*(mass/safe_rr +.5*(qx*X*X+qy*Y*Y+qz*Z*Z)/(safe_rr**5))
    mask=np.zeros((n,n,n),dtype=bool)
    mask[0,:,:]=True;mask[-1,:,:]=True
    mask[:,0,:]=True;mask[:,-1,:]=True
    mask[:,:,0]=True;mask[:,:,-1]=True
    ub[~mask]=0.
    return ub

def solve_dirichlet(rhs,bdy,h):
    n=bdy.shape[0]
    v=rhs[1:-1,1:-1,1:-1].copy()
    fac=1./h**2
    v[0,:,:]+=fac*bdy[0,1:-1,1:-1];v[-1,:,:]+=fac*bdy[-1,1:-1,1:-1]
    v[:,0,:]+=fac*bdy[1:-1,0,1:-1];v[:,-1,:]+=fac*bdy[1:-1,-1,1:-1]
    v[:,:,0]+=fac*bdy[1:-1,1:-1,0];v[:,:,-1]+=fac*bdy[1:-1,1:-1,-1]
    nh=n-2;k=np.arange(1,nh+1)
    l=2*fac*(1-np.cos(np.pi*k/(n-1)))
    den=l[:,None,None]+l[None,:,None]+l[None,None,:]
    hat=dstn(v,type=1,norm='ortho',workers=-1)
    sol=idstn(hat/den,type=1,norm='ortho',workers=-1)
    u=bdy.copy()
    u[1:-1,1:-1,1:-1]=sol
    return u

def residual(psi,S,h):
    p=psi;fac=1./h**2
    lap=(p[:-2,1:-1,1:-1]+p[2:,1:-1,1:-1]
        +p[1:-1,:-2,1:-1]+p[1:-1,2:,1:-1]
        +p[1:-1,1:-1,:-2]+p[1:-1,1:-1,2:]
        -6*p[1:-1,1:-1,1:-1])*fac
    rr=lap+2*np.pi*G*S[1:-1,1:-1,1:-1]
    return float(np.linalg.norm(rr.ravel())/max(np.linalg.norm((2*np.pi*G*S[1:-1,1:-1,1:-1]).ravel()),1e-30)),float(np.max(np.abs(rr)))

def iterate(n=64,s=.16,lag_amplitude=0.,L=15.,tol=1e-11,maxit=120):
    grid=make_dirichlet_grid(n,L)
    e2,e4,V=density(s,grid,memory_amp=lag_amplitude)
    h=grid[2]
    psi=np.ones_like(e2)
    history=[]
    for it in range(maxit):
        S=psi*e2+psi**-3*e4+psi**5*V
        bd=boundary(grid,source_moments(S,grid))
        rhs=2*np.pi*G*S
        pn=1+solve_dirichlet(rhs,bd,h)
        # underrelax for safety, but positivity holds in all tests
        diff=float(np.max(np.abs(pn-psi)))
        psi=.75*pn+.25*psi
        history.append(diff)
        if diff<tol:
            psi=pn
            break
    else:
        raise RuntimeError('fixed point failed')
    S=psi*e2+psi**-3*e4+psi**5*V
    mom=source_moments(S,grid)
    err,maxres=residual(psi,S,h)
    properE=float(np.sum(psi**2*e2+psi**-2*e4+psi**6*V)*h**3)
    emat=float(np.sum((e2+e4+V))*h**3)
    mass0=source_moments(e2+e4+V,grid)[0]
    psi0=float(psi[n//2,n//2,n//2])
    data=dict(n=n,L=L,h=h,s=s,lag_amplitude=lag_amplitude,iterations=it+1,
              last_fixed_point_update=diff,psi_center=psi0,
              psi_min=float(np.min(psi)),psi_max=float(np.max(psi)),
              ADM_mass=mom[0],ADM_quadrupole_x=mom[1],ADM_quadrupole_y=mom[2],ADM_quadrupole_z=mom[3],
              rest_angular_mass=mass0,proper_mass=properE,
              flat_matter_energy=emat,
              Hamiltonian_constraint_rel_l2=err,
              Hamiltonian_constraint_max_abs=maxres,
              time_symmetric_momentum_constraint_residual=0.)
    return data,grid,psi,S,(e2,e4,V),history

def main():
    ts=time.monotonic()
    cases=[]
    for n in [41,61,81]:
        for s in [0.,.16,-.16]:
            if n==81 and s<0: continue
            dat,grid,psi,S,terms,hist=iterate(n,s)
            print('n',n,'s',s,'ADM',dat['ADM_mass'],'center',dat['psi_center'],'resid',dat['Hamiltonian_constraint_rel_l2'], 'iterations',dat['iterations'],flush=True)
            cases.append(dat)
            if n==81 and s in (0.,.16):
                # central plane, three directions
                np.savetxt(OUT/f'psi_slice_n{n}_s{str(s).replace(".","p")}.csv',
                           np.c_[grid[3],psi[:,n//2,n//2],psi[n//2,:,n//2],psi[n//2,n//2,:],
                                 S[:,n//2,n//2],S[n//2,:,n//2]],
                           delimiter=',',header='coordinate,psi_x,psi_y,psi_z,source_x,source_y',comments='')
    dat,grid,psi,S,terms,hist=iterate(61,.16,lag_amplitude=.06)
    cases.append(dat)
    with (OUT/'non_spherical_adm_initial_data.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(cases[0]));w.writeheader();w.writerows(cases)
    summary={
      'duration_seconds':time.monotonic()-ts,
      'exact_momentum_constraint_note':'time symmetric Kij=0 and static scalar field momenta=0, S_i=0: momentum constraint is 0=0 identically',
      'Einstein_hamiltonian':'Delta psi=-2piG(psi e2 + psi^-3 e4 + psi^5 V)',
      'boundary_approximation':'finite cubic box; Dirichlet boundary includes monopole and quadrupole of current nonlinear conformal source',
      'warning':'constraint-satisfying initial data only. Time evolution and TT gravitational waves not simulated.',
      'cases':cases,
    }
    with (OUT/'adm_audit_v18.json').open('w') as f:json.dump(summary,f,indent=2,ensure_ascii=False)
    print('Done',summary['duration_seconds'])

if __name__=='__main__':main()
