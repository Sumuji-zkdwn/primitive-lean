#!/usr/bin/env python3
"""Finite-energy non-affine l=2 test deformations for spherical Skyrme+memory seed.

F_eps(x) = x + eps exp(-|x|^2/Lmode^2) diag(1,-1,0)x.
Field q_eps(x)=q0(F_eps(x)), chi_eps(x)=chi0(F_eps(x)).
The Jacobian is explicitly evaluated to compute energy, not a frozen
spatial q-gradient. For small eps with det DF>0 and fixed vacuum boundary,
topological degree remains 1.
"""
import numpy as np,csv,json
from pathlib import Path
from verify_v18 import make_grid,profile,LAM
OUT=Path(__file__).resolve().parent

def calc(eps,sigma,grid):
    n,L,h,xx,X,Y,Z=grid
    r0sq=X*X+Y*Y+Z*Z
    mode=np.exp(-r0sq/(sigma*sigma))
    yx=(1+eps*mode)*X;yy=(1-eps*mode)*Y;yz=Z
    r=np.sqrt(yx*yx+yy*yy+yz*yz)
    a,b,cp2,A,V,lag=profile(r)
    nx=np.divide(yx,r,out=np.zeros_like(r),where=r>0)
    ny=np.divide(yy,r,out=np.zeros_like(r),where=r>0)
    nz=np.divide(np.broadcast_to(yz,r.shape),r,out=np.zeros_like(r),where=r>0)
    u=eps*(-2/(sigma*sigma))*mode*X
    v=eps*(2/(sigma*sigma))*mode*Y
    J00=1+eps*mode+u*X
    J01=u*Y
    J02=u*Z
    J10=v*X
    J11=1-eps*mode+v*Y
    J12=v*Z
    Jacobian=J00*J11-J01*J10
    vi=(nx*J00+ny*J10,nx*J01+ny*J11,nx*J02+ny*J12+nz)
    cols=((J00,J10,np.zeros_like(r)),(J01,J11,np.zeros_like(r)),(J02,J12,np.ones_like(r)))
    trace=np.zeros_like(r)
    trace2=np.zeros_like(r)
    for i in range(3):
        v_i=vi[i]
        trace += b*sum(j*j for j in cols[i])+(a-b)*v_i*v_i
        for j in range(3):
            cij=b*sum(ci*cj for ci,cj in zip(cols[i],cols[j]))+(a-b)*v_i*vi[j]
            trace2+=cij*cij
    e2=.5*(A*trace+cp2*sum(vv*vv for vv in vi))
    e4=.25*LAM*(trace*trace-trace2)
    E2=float(np.sum(e2)*h**3);E4=float(np.sum(e4)*h**3);E0=float(np.sum(V)*h**3)
    assert np.min(e4)>-1e-10
    return dict(E2=E2,E4=E4,E0=E0,Etotal=E2+E4+E0,
                min_map_jacobian=float(np.min(Jacobian)),
                max_map_jacobian=float(np.max(Jacobian)),
                max_deformation=float(np.max(np.abs(eps*mode))))

def main():
    rows=[]
    for n in [48,72,96]:
        grid=make_grid(n=n,L=13.5)
        for sigma in [2.5,4.5,7.0]:
            for eps in [-.20,-.10,0.,.10,.20]:
                stats=calc(eps,sigma,grid)
                rows.append(dict(n=n,sigma=sigma,eps=eps,**stats))
                print(n,sigma,eps,stats['Etotal'],stats['min_map_jacobian'],flush=True)
    with (OUT/'nonaffine_quadrupole.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
    results=[]
    for n in [48,72,96]:
        for sigma in [2.5,4.5,7.0]:
            vals={r['eps']:r['Etotal'] for r in rows if r['n']==n and r['sigma']==sigma}
            for eps in [.1,.2]:
                signed=vals[eps]+vals[-eps]-2*vals[0]
                asym=(vals[eps]-vals[-eps])/2
                results.append(dict(n=n,sigma=sigma,amplitude=eps,
                    symmetric_energy_increase=signed/2,
                    signed_odd_energy_component=asym,
                    centered_second_derivative=signed/eps**2))
    with (OUT/'nonaffine_hessian.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(results[0]));w.writeheader();w.writerows(results)
    print(json.dumps({'tests':len(rows),'min_jac':min(r['min_map_jacobian'] for r in rows),'max_odd_component':max(abs(r['signed_odd_energy_component']) for r in results), 'min_hessian':min(r['centered_second_derivative'] for r in results)},indent=2))

if __name__=='__main__':main()
