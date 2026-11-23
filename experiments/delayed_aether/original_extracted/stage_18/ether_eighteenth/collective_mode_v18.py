#!/usr/bin/env python3
"""Restricted non-spherical collective oscillation with approximate Newtonian self gravity.

A controlled 1-DOF shape ansatz q_s(x)=q0(M(s)x), chi_s similarly.
The inertia includes quadratic and Skyrme time-space terms, derived from v16 action.
No claim of stability against general perturbations or full 3+1 Einstein evolution.
"""
import numpy as np
import csv,json,time
from pathlib import Path
from scipy.integrate import solve_ivp
from scipy.interpolate import PchipInterpolator
from scipy.optimize import brentq
from verify_v18 import make_grid,profile,density,make_kernel_fft,newton_energy,radial_pieces,exact_matter,G,LAM
OUT=Path(__file__).resolve().parent

def collective_inertia(s,grid):
    n,L,h,xx,X,Y,Z=grid
    dx,dy=np.exp(s),np.exp(-s)
    yx=dx*X;yy=dy*Y;yz=Z
    r=np.sqrt(yx*yx+yy*yy+zz(yz,n))
    a,b,cp2,A,V,lag=profile(r)
    nx=np.divide(yx,r,out=np.zeros_like(r),where=r>0)
    ny=np.divide(yy,r,out=np.zeros_like(r),where=r>0)
    nz=np.divide(np.broadcast_to(yz,r.shape),r,out=np.zeros_like(r),where=r>0)
    # w= d/ds M(s)x = (yx,-yy,0)
    w2=yx*yx+yy*yy
    nw=np.divide(yx*yx-yy*yy,r,out=np.zeros_like(r),where=r>0)
    qn=b*w2+(a-b)*nw*nw
    chin=cp2*nw*nw
    # partial spatial norm sum tr C
    d2x=dx*dx;d2y=dy*dy
    t1=d2x*nx*nx+d2y*ny*ny+nz*nz
    trC=b*(d2x+d2y+1)+(a-b)*t1
    # G_y w = b w+(a-b) n(n.w)
    gwx=b*yx+(a-b)*nx*nw
    gwy=-b*yy+(a-b)*ny*nw
    gwz=(a-b)*nz*nw
    v2=d2x*gwx*gwx+d2y*gwy*gwy+gwz*gwz
    I2=np.sum(A*qn+chin)*h**3
    I4=LAM*np.sum(qn*trC-v2)*h**3
    assert I2>0 and I4>=-1e-8
    return I2,I4,I2+I4

def zz(z,n):
    return np.broadcast_to(z,(n,n,n))**2

def main():
    grid=make_grid(n=96)
    Khat=make_kernel_fft(96,grid[2])
    radial=radial_pieces()
    rows=[]
    for s in np.linspace(0.,.25,14):
        e2,e4,v=density(s,grid)
        U=newton_energy(e2+e4+v,grid[2],Khat)
        i2,i4,I=collective_inertia(s,grid)
        rows.append(dict(s=s,Emat=exact_matter(s,radial),Ugravity=U,Etotal=exact_matter(s,radial)+U,I2=i2,I4=i4,inertia=I))
        print('s',round(s,4),'I',round(I,7),'U',round(U,7),flush=True)
    with (OUT/'collective_shape_samples.csv').open('w',newline='') as f:
        dw=csv.DictWriter(f,fieldnames=list(rows[0]));dw.writeheader();dw.writerows(rows)
    s2=np.array([r['s']**2 for r in rows]); ug=np.array([r['Ugravity'] for r in rows]);Ival=np.array([r['inertia'] for r in rows]);
    Ufun=PchipInterpolator(s2,ug);Ifun=PchipInterpolator(s2,Ival)
    def V(s):return exact_matter(s,radial)+float(Ufun(s*s))
    def Vd(s):return (radial['E2']+radial['E4'])*(4./3.)*np.sinh(2*s)+2*s*float(Ufun.derivative()(s*s))
    # exact derivative d/ds of (1+2cosh2s)/3 is (4/3)sinh2s
    def I(s):return float(Ifun(s*s))
    def Id(s):return 2*s*float(Ifun.derivative()(s*s))
    def fun(t,y):
        s,v=y
        return [v,-(Vd(s)+.5*Id(s)*v*v)/I(s)]
    init=[.12,0.]
    T=20.
    t=np.linspace(0,T,2001)
    sol=solve_ivp(fun,(0,T),init,t_eval=t,dense_output=True,method='DOP853',rtol=2e-11,atol=1e-12)
    if not sol.success: raise RuntimeError(sol.message)
    E=np.array([.5*I(s)*v*v+V(s) for s,v in zip(*sol.y)])
    imax=np.where((sol.y[1,1:]<=0)&(sol.y[1,:-1]>0))[0]
    # positive-to-negative v crossing = local maxima of s after first max
    crest_times=[]
    for j in imax:
        if sol.y[0,j]>0:
            crest_times.append(float(brentq(lambda q: sol.sol(q)[1],t[j],t[j+1],xtol=1e-13)))
    period=float(np.mean(np.diff(crest_times))) if len(crest_times)>1 else None
    # second derivative stiffness numerically near zero
    du2=float(Ufun.derivative()(0.))
    Kmat=(8./3.)*(radial['E2']+radial['E4'])
    Kgrav=2*du2
    kh=Kmat+Kgrav
    w0=np.sqrt(kh/I(0.))
    summary=dict(radial=radial,I0=I(0.),I4fraction=float(rows[0]['I4']/I(0.)),
                 Kmat=Kmat,Kgravity=Kgrav,Ktotal=kh,frequency_small_amplitude=w0,
                 period_harmonic=2*np.pi/w0,period_observed=period,
                 energy_initial=E[0],relative_energy_drift=float(np.max(np.abs(E-E[0]))/E[0]),
                 time_span=T,max_s=float(np.max(sol.y[0])),min_s=float(np.min(sol.y[0])),
                 approximation='single affine shape degree of freedom, Skyrme kinetic contribution; Newtonian instantaneous gravity at G=0.002; assumes frozen radial profiles and omits radiation',
                 gravity_source_changes_with_shape=True)
    np.savetxt(OUT/'collective_shape_oscillation.csv',np.c_[t,sol.y[0],sol.y[1],E],delimiter=',',header='t,s,ds_dt,reduced_energy',comments='')
    with (OUT/'collective_mode_audit.json').open('w') as f:json.dump(summary,f,indent=2)
    print(json.dumps({k:v for k,v in summary.items() if k!='radial'},indent=2))

if __name__=='__main__':main()
