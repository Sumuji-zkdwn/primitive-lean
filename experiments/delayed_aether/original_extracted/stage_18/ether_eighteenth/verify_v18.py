#!/usr/bin/env python3
"""v18: non-spherical affine stress test of the v17 hedgehog+chi model.

Computes static field energy exactly for q_s(x)=q_0(M_s x), chi_s(x)=chi_0(M_s x),
M_s=diag(exp(s),exp(-s),1) with det M_s=1; weak-field self-gravity
(leading Newtonian field sourced by the computed flat-space energy density).

This is NOT time-dependent 3+1 Einstein evolution, nor full linear mode stability.
"""
from __future__ import annotations
import numpy as np
from scipy.integrate import simpson, cumulative_trapezoid
from scipy.fft import rfftn,irfftn,next_fast_len
from scipy.special import roots_legendre
from pathlib import Path
import csv, json, time

OUT=Path(__file__).resolve().parent
R0=1.15; W=3.; R=12.; taper_start=9.
LAM=0.2; MU=0.15; KAPPA=0.9; DELTA=2.; S_MEM=0.28
G=0.002

def profile(r, memory_amp=0.):
    """Analytic compact initial f(r) used in v17, chi=cos f + memory perturbation."""
    r=np.asarray(r)
    amp=R0*np.exp(-(r*r)/(2*W*W))
    fbase=2*np.arctan2(amp,r)
    fpbase=-2*amp*(1+r*r/W**2)/(r*r+amp*amp)
    u=np.clip((r-taper_start)/(R-taper_start),0,1)
    taper=1-10*u**3+15*u**4-6*u**5
    taperp=(-30*u*u+60*u**3-30*u**4)/(R-taper_start)
    taperp=np.where((r>taper_start)&(r<R),taperp,0.)
    f=fbase*taper
    fp=fpbase*taper+fbase*taperp
    f=np.where(r>=R,0.,f)
    fp=np.where(r>=R,0.,fp)
    # radial memory displacement m(r) localized and smooth at r=0
    lag=memory_amp*np.exp(-(r/2.0)**2)
    lagp=-2*r/(2.0**2)*lag
    chi=np.cos(f)+lag
    chip=-np.sin(f)*fp+lagp
    a=fp*fp
    b=np.zeros_like(r)
    mask=r>1e-9
    b[mask]=(np.sin(f[mask])/r[mask])**2
    b[~mask]=(2/R0)**2
    A=1+DELTA*np.tanh(lag/S_MEM)**2
    V=.5*KAPPA*lag**2+.5*MU**2*(chi-1)**2
    return a,b,chip**2,A,V,lag

def radial_pieces(memory_amp=0.):
    r=np.linspace(0,15,30001)
    a,b,cp2,A,V,_=profile(r,memory_amp)
    e2=.5*(A*(a+2*b)+cp2)
    e4=LAM*(a*b+.5*b*b)
    integral=lambda rho: 4*np.pi*simpson(r*r*rho,x=r)
    e2int=integral(e2);e4int=integral(e4);vint=integral(V)
    rho=e2+e4+V
    m=cumulative_trapezoid(4*np.pi*r*r*rho,r,initial=0.)
    U=-4*np.pi*G*simpson(r*m*rho,x=r)
    return dict(E2=e2int,E4=e4int,E0=vint,mass=e2int+e4int+vint,U_radial=U)

def exact_matter(s,radial):
    # for volume preserving diagonal stretch, angular averages exactly fixed
    w=(1+2*np.cosh(2*s))/3
    return radial['E0']+(radial['E2']+radial['E4'])*w

def make_grid(n=64,L=13.5):
    h=2*L/n
    x=np.linspace(-L+h/2,L-h/2,n)
    # broadcasting is more memory efficient than meshgrid arrays
    return n,L,h,x,x[:,None,None],x[None,:,None],x[None,None,:]

def density(s,grid,memory_amp=0.):
    n,L,h,x,X,Y,Z=grid
    dx=np.exp(s);dy=np.exp(-s)
    xx=dx*X;yy=dy*Y;zz=Z
    # broadcast coordinate combinations via r
    r=np.sqrt(xx*xx+yy*yy+zz*zz)
    a,b,cp2,A,V,lag=profile(r,memory_amp)
    with np.errstate(divide='ignore',invalid='ignore'):
        nx2=np.where(r>1e-12,xx*xx/(r*r),0.)
        ny2=np.where(r>1e-12,yy*yy/(r*r),0.)
        nz2=np.where(r>1e-12,zz*zz/(r*r),0.)
    d2=np.array([dx**2,dy**2,1.])
    t1=d2[0]*nx2+d2[1]*ny2+nz2
    t2=d2[0]**2*nx2+d2[1]**2*ny2+nz2
    S1=np.sum(d2);S2=np.sum(d2*d2)
    trace=b*S1+(a-b)*t1
    trace2=b*b*S2+2*b*(a-b)*t2+(a-b)**2*t1*t1
    e2=.5*(A*trace+cp2*t1)
    e4=.25*LAM*(trace*trace-trace2)
    # quartic positive semi-definite. min tiny numerical round-off near tails.
    assert np.min(e4)>=-1e-11
    return e2,e4,V

def make_kernel_fft(n,h):
    # Linear convolution: periodic alias-free over n^3 supported density cube
    L=2*n
    offsets=np.arange(L)
    shifts=np.where(offsets<=n-1,offsets,offsets-L)
    aa=shifts[:,None,None]**2+shifts[None,:,None]**2+shifts[None,None,:]**2
    K=np.zeros((L,L,L),dtype=np.float64)
    ok= (np.abs(shifts[:,None,None])<n)&(np.abs(shifts[None,:,None])<n)&(np.abs(shifts[None,None,:])<n)
    np.divide(1.,h*np.sqrt(aa),out=K,where=ok&(aa>0))
    # cube-cell average of 1/r at the central cell, approximate constant 2.38/h
    K[0,0,0]=2.380077363979553/h
    return rfftn(K,workers=-1)

def newton_energy(rho,h,Khat):
    n=rho.shape[0];L=2*n
    buf=np.zeros((L,L,L),dtype=np.float64)
    buf[:n,:n,:n]=rho
    F=rfftn(buf,workers=-1)
    del buf
    convolution=irfftn(F*Khat,s=(L,L,L),workers=-1)[:n,:n,:n]
    return -.5*G*h**6*float(np.sum(rho*convolution))

def moment_data(rho,grid):
    n,L,h,xx,X,Y,Z=grid
    mass=np.sum(rho)*h**3
    x2=np.sum(rho*X**2)*h**3
    y2=np.sum(rho*Y**2)*h**3
    z2=np.sum(rho*Z**2)*h**3
    Qx=2*x2-y2-z2;Qy=2*y2-x2-z2;Qz=2*z2-x2-y2
    return dict(mass=mass,Qx=Qx,Qy=Qy,Qz=Qz)

def far_potential(rho,grid,point):
    n,L,h,_,X,Y,Z=grid
    dx=X-point[0];dy=Y-point[1];dz=Z-point[2]
    return -G*h**3*np.sum(rho/np.sqrt(dx*dx+dy*dy+dz*dz))

def test_analytic_affine():
    # exact pointwise gradient determinant identities are checked numerically
    rng=np.random.default_rng(311)
    worst=0.
    for _ in range(500):
        s=rng.uniform(-.4,.4)
        M=np.diag([np.exp(s),np.exp(-s),1.])
        n=rng.normal(size=3);n/=np.linalg.norm(n)
        a,b=rng.uniform(.01,3,size=2)
        U=np.eye(3)*b+(a-b)*np.outer(n,n)
        gram=M.T@U@M
        tr=np.trace(gram);tr2=np.sum(gram*gram)
        ds=np.exp(2*s);dt=np.exp(-2*s)
        t1=ds*n[0]**2+dt*n[1]**2+n[2]**2
        t2=ds**2*n[0]**2+dt**2*n[1]**2+n[2]**2
        tr_formula=b*(ds+dt+1)+(a-b)*t1
        tr2_formula=b*b*(ds*ds+dt*dt+1)+2*b*(a-b)*t2+(a-b)**2*t1*t1
        worst=max(worst,abs(tr-tr_formula),abs(tr2-tr2_formula))
    assert worst<1e-12
    return worst

def angular_gravity_factor(s,num=96):
    # transported, radial, fixed mass density: Egrav ratio is universal angular integral
    # integrate over mu=cos(theta), phi with periodic trapezoid.
    mu,w=roots_legendre(num)
    phi=2*np.pi*np.arange(4*num)/(4*num)
    nx2=(1-mu[:,None]**2)*np.cos(phi[None,:])**2
    ny2=(1-mu[:,None]**2)*np.sin(phi[None,:])**2
    nz2=np.broadcast_to(mu[:,None]**2,nx2.shape)
    inv=np.sqrt(np.exp(-2*s)*nx2+np.exp(2*s)*ny2+nz2)
    return float(np.sum(w[:,None]*(1/inv),axis=None)/(2*len(phi)))

def main():
    t0=time.monotonic()
    identities=test_analytic_affine()
    rs0=radial_pieces(0.);rsLag=radial_pieces(.06)
    table=[]
    for n in [48,72,96]:
        grid=make_grid(n=n)
        Khat=make_kernel_fft(n,grid[2])
        for memory_amp in ([0.,.06] if n==72 else [0.]):
            radial=rsLag if memory_amp else rs0
            for s in [0.,.08,.16,.24]:
                e2,e4,v=density(s,grid,memory_amp)
                rho=e2+e4+v
                E2=float(np.sum(e2)*grid[2]**3)
                E4=float(np.sum(e4)*grid[2]**3)
                E0=float(np.sum(v)*grid[2]**3)
                U=newton_energy(rho,grid[2],Khat)
                mom=moment_data(rho,grid)
                row=dict(n=n, s=s,lag_amplitude=memory_amp,
                    E2=E2,E4=E4,E0=E0,Emat=E2+E4+E0,
                    Emat_exact=exact_matter(s,radial),Ugravity=U,
                    Etotal=E2+E4+E0+U,
                    grav_source_mass=mom['mass'],Qx=mom['Qx'],Qy=mom['Qy'],Qz=mom['Qz'],
                    transported_radial_factor=angular_gravity_factor(s),
                    radial_reference_U=radial['U_radial'])
                table.append(row)
                print('N',n,'lag',memory_amp,'s',s,'E',round(row['Emat'],8),'E_exact',round(row['Emat_exact'],8), 'U',round(U,8),'Qx',round(mom['Qx'],6),flush=True)
            if memory_amp==0.:
                s=.16
                _,_,_=None,None,None
                e2,e4,v=density(s,grid)
                rho=e2+e4+v
                mom=moment_data(rho,grid)
                for rad in [24.,40.]:
                    for axis,quad in [('x',mom['Qx']),('y',mom['Qy']),('z',mom['Qz'])]:
                        point=np.zeros(3);point['xyz'.index(axis)]=rad
                        direct=far_potential(rho,grid,point)
                        monopole=-G*mom['mass']/rad
                        multipole=-G*(mom['mass']/rad+quad/(2*rad**3))
                        table.append(dict(n=n,s=s,lag_amplitude=0.,test='farfield',rad=rad,axis=axis,
                            direct_potential=direct,monopole=monopole,multipole=multipole))
        del Khat
    rows=[row for row in table if 'test' not in row]
    with (OUT/'affine_gravity_energy.csv').open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=list(rows[0]));writer.writeheader();writer.writerows(rows)
    rowsfar=[row for row in table if 'test' in row]
    with (OUT/'farfield_quadrupole.csv').open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=list(rowsfar[0]));writer.writeheader();writer.writerows(rowsfar)
    summary={
        'radial_reference_no_memory':rs0,
        'radial_reference_frozen_memory':rsLag,
        'max_gradient_identity_error':identities,
        'unitless_gravity_G':G,
        'formula_quadrupole_E_matter': 'E(s)=E0+(E2+E4)*(1+2*cosh(2*s))/3 for det M=1, M=diag(e^s,e^-s,1)',
        'model_status':'affine non-spherical slice, Newtonian weak-field approximate binding, not nonlinear GR and no time evolution',
        'runtime_seconds':time.monotonic()-t0,
    }
    with (OUT/'audit_v18.json').open('w') as f:json.dump(summary,f,indent=2,ensure_ascii=False)
    print('done',summary['runtime_seconds'])

if __name__=='__main__':main()
