#!/usr/bin/env python3
"""Independent checks of v19 by torch autodiff, discrete Hessian and angular quadrature."""
from pathlib import Path
import sys,json,csv
import numpy as np
from scipy.linalg import eigh
from scipy.integrate import simpson
from scipy.special import roots_legendre
import torch
from verify_v19 import Radial,coeff,projected_matrices,background,bases,second_variation,LAM,KAPPA,MU,DELTA,S_MEM,FOURPI
OUT=Path(__file__).resolve().parent
torch.set_num_threads(1)

def torch_energy(x,n,R=12.):
    d=torch.float64;h=R/n
    F=torch.cat((torch.tensor([np.pi],dtype=d),x[:n-1],torch.zeros(1,dtype=d)))
    C=torch.cat((x[n-1:n],x[n-1:2*n-2],torch.ones(1,dtype=d)))
    rm=torch.arange(n,dtype=d)*h+h/2
    f=(F[:-1]+F[1:])/2;chi=(C[:-1]+C[1:])/2
    fprime=(F[1:]-F[:-1])/h;cp=(C[1:]-C[:-1])/h
    lag=chi-torch.cos(f)
    aa=1+DELTA*torch.tanh(lag/S_MEM)**2
    s=torch.sin(f)
    ep=.5*aa*(rm**2*fprime**2+2*s**2)+.5*rm**2*cp**2
    ep+=LAM*(s**2*fprime**2+.5*s**4/rm**2)
    ep+=KAPPA/2*rm**2*lag**2+MU**2/2*rm**2*(chi-1)**2
    return FOURPI*h*torch.sum(ep)

def radial_hessian(model,point):
    n=len(point);H=np.empty((n,n));eps=3e-5
    for j in range(n):
        p=np.zeros(n);p[j]=eps
        H[:,j]=(model.energy_grad(point+p)[1]-model.energy_grad(point-p)[1])/(2*eps)
    sym=float(np.max(abs(H-H.T)))
    H=(H+H.T)/2
    return H,sym

def angular_energy(eps,r,sf,sc,a,ap,b,bp,l=2):
    assert l==2
    mu,w=roots_legendre(48)
    mu=mu[None,:]
    Y=np.sqrt(5)*.5*(3*mu*mu-1)
    DY=3*np.sqrt(5)*mu
    r=r[:,None]
    f=sf(r)+eps*a[:,None]*Y
    c=sc(r)+eps*b[:,None]*Y
    fd=sf.derivative()(r)+eps*ap[:,None]*Y
    cd=sc.derivative()(r)+eps*bp[:,None]*Y
    ang=(1-mu*mu)*DY*DY
    fgrad=fd*fd+eps*eps*a[:,None]**2*ang/(r*r)
    cgrad=cd*cd+eps*eps*b[:,None]**2*ang/(r*r)
    si=np.sin(f); D=si*si/(r*r)
    lag=c-np.cos(f)
    A=1+DELTA*np.tanh(lag/S_MEM)**2
    rho=.5*A*(fgrad+2*D)+.5*cgrad
    rho+=LAM*(D*fd*fd+.5*D*eps**2*a[:,None]**2*ang/(r*r)+.5*D**2)
    rho+=.5*KAPPA*lag*lag+.5*MU*MU*(c-1)**2
    return float(FOURPI*simpson((r[:,0]**2)*(.5*np.sum(rho*w[None,:],axis=1)),x=r[:,0]))

def main():
    checks={}
    for n in [80,120,180]:
        rad=Radial(n)
        data=np.genfromtxt(OUT/f'radial_profile_n{n}.csv',delimiter=',',names=True)
        x=rad.pack(data['f'],data['chi'])
        rng=np.random.default_rng(2342+n)
        # field variation ensures derivative check away from optimum too
        xpert=x+.002*rng.normal(size=x.shape)
        xe=torch.tensor(xpert,dtype=torch.float64,requires_grad=True)
        v=torch_energy(xe,n)
        gt=torch.autograd.grad(v,xe)[0].detach().numpy()
        en,gn=rad.energy_grad(xpert)
        chk=dict(n=n,energy_abs_difference=float(abs(v.item()-en)),gradient_max_abs_difference=float(np.max(abs(gt-gn))),gradient_rms_difference=float(np.sqrt(np.mean((gt-gn)**2))))
        print('torch gradient',chk,flush=True)
        checks[f'gradient_{n}']=chk
        H,sym=radial_hessian(rad,x)
        # normalized nodal kinetic for relative eigenvalues; chi0 constrained to chi1
        f=data['f'];chi=data['chi'];r=rad.r[1:-1]
        AA=coeff(chi[1:-1]-np.cos(f[1:-1]))[0]
        D=(np.sin(f[1:-1])/r)**2
        sigma=AA+2*LAM*D
        masses=FOURPI*rad.h*np.r_[r*r*sigma,r*r]
        # exact cosh kinetic strong positive. at chi1 add chi0 r0^2=0.
        ew=eigh(H,np.diag(masses),eigvals_only=True,subset_by_index=[0,5])
        rec=dict(n=n,lowest_radial_omega_squared=float(ew[0]),six_smallest_omega_squared=list(map(float,ew)),hessian_symmetry_residual=sym)
        print('radial Hessian',rec,flush=True)
        checks[f'radial_{n}']=rec
    m=Radial(180)
    dat=np.genfromtxt(OUT/'radial_profile_n180.csv',delimiter=',',names=True)
    sf,sc=background(m,type('R',(),{'x':m.pack(dat['f'],dat['chi'])})())
    r=np.linspace(1e-4,12.,2401)
    aa=bases(r,2)
    af,ap=aa[3];bc,bp=aa[5]
    hess=float(second_variation(r,sf,sc,af,ap,bc,bp,l=2))
    rec={'analytic_projected_second_variation':hess}
    e0=angular_energy(0,r,sf,sc,af,ap,bc,bp)
    for eps in [0.008,0.004,0.002]:
        ep=angular_energy(eps,r,sf,sc,af,ap,bc,bp)
        em=angular_energy(-eps,r,sf,sc,af,ap,bc,bp)
        fd=(ep+em-2*e0)/eps**2
        rec[f'fd_second_variation_eps_{eps}']=float(fd)
        rec[f'abs_error_eps_{eps}']=float(abs(fd-hess))
    print('angular quadrature',rec,flush=True)
    checks['angular_independent_quadrature']=rec
    (OUT/'independent_audit_v19.json').write_text(json.dumps(checks,indent=2,ensure_ascii=False))

if __name__=='__main__':main()
