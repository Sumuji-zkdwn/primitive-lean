#!/usr/bin/env python3
"""v19: static self-consistent hedgehog+memory equilibrium and restricted l=2 Hessian.

Uses same flat-space Einstein-Skyrme-chi matter action as v16-v18, G=0.
Nonlinear radial equilibrium with correct f,chi variation; angular l=2 quadratic
fluctuations with independent f,chi radial basis. NOT full perturbation spectrum,
not general-relativistic self-gravitating equilibrium, not dissipative memory.
"""
from __future__ import annotations
import json,csv
from pathlib import Path
import numpy as np
from scipy.optimize import minimize
from scipy.linalg import eigh
from scipy.integrate import simpson
BASE=Path(__file__).resolve().parent
# Model parameters retained verbatim from v18; self-contained for archival.
R0=1.15; W=3.; R=12.; taper_start=9.
LAM=.2; MU=.15; KAPPA=.9; DELTA=2.; S_MEM=.28

FOURPI=4*np.pi

def coeff(y):
    t=np.tanh(y/S_MEM)
    A=1+DELTA*t*t
    Ap=2*DELTA/S_MEM*t*(1-t*t)
    App=2*DELTA/S_MEM**2*(1-t*t)*(1-3*t*t)
    return A,Ap,App

class Radial:
    def __init__(self,n,Rbox=12):
        self.n=n;self.R=Rbox;self.h=Rbox/n
        self.r=np.linspace(0,Rbox,n+1)
        self.rm=(self.r[:-1]+self.r[1:])/2
        self.r2=self.rm**2
    def unpack(self,x):
        n=self.n
        f=np.r_[np.pi,x[:n-1],0.]
        # zero derivative at origin chi_0=chi_1
        chi=np.r_[x[n-1],x[n-1:2*n-2],1.]
        return f,chi
    def pack(self,f,chi):return np.r_[f[1:-1],chi[1:-1]]
    def initial(self):
        r=self.r
        amp=R0*np.exp(-r*r/(2*W*W))
        f0=2*np.arctan2(amp,r)
        u=np.clip((r-taper_start)/(R-taper_start),0,1)
        taper=1-10*u**3+15*u**4-6*u**5
        f0=f0*taper
        f0[0]=np.pi;f0[-1]=0
        chi=np.cos(f0);chi[0]=chi[1];chi[-1]=1
        return self.pack(f0,chi)
    def energy_grad(self,x,return_pieces=False):
        n=self.n;h=self.h;rr=self.r2
        f,chi=self.unpack(x)
        fm=(f[:-1]+f[1:])/2
        cm=(chi[:-1]+chi[1:])/2
        fd=np.diff(f)/h;cd=np.diff(chi)/h
        s=np.sin(fm);c=np.cos(fm)
        y=cm-c; A,Ap,_=coeff(y)
        s2=s*s
        E2=.5*A*(rr*fd*fd+2*s2)+.5*rr*cd*cd
        E4=LAM*(s2*fd*fd+.5*s2*s2/rr)
        E0=.5*KAPPA*rr*y*y+.5*MU*MU*rr*(cm-1)**2
        vals=np.array([FOURPI*h*np.sum(a) for a in [E2,E4,E0]])
        e=float(np.sum(vals))
        if return_pieces:return vals
        gf_mid=.5*Ap*s*(rr*fd*fd+2*s2)+2*A*s*c+LAM*(2*s*c*fd*fd+2*s**3*c/rr)+KAPPA*rr*y*s
        gc_mid=.5*Ap*(rr*fd*fd+2*s2)+KAPPA*rr*y+MU**2*rr*(cm-1)
        gf_grad=A*rr*fd+2*LAM*s2*fd
        gc_grad=rr*cd
        gf=np.zeros(n+1); gc=np.zeros(n+1)
        gf[:-1]+= .5*gf_mid-gf_grad/h
        gf[1:]+= .5*gf_mid+gf_grad/h
        gc[:-1]+= .5*gc_mid-gc_grad/h
        gc[1:]+= .5*gc_mid+gc_grad/h
        gf*=FOURPI*h;gc*=FOURPI*h
        gc[1]+=gc[0] # chi0=chi1
        g=np.r_[gf[1:-1],gc[1:-1]]
        return e,g
    def minimize(self):
        x0=self.initial()
        bounds=[(0.,np.pi)]*(self.n-1)+[(-1.5,1.5)]*(self.n-1)
        res=minimize(self.energy_grad,x0,method='L-BFGS-B',jac=True,bounds=bounds,
                     options={'maxiter':20000,'maxfun':35000,'ftol':2e-15,'gtol':3e-9,'maxls':45,'maxcor':25})
        if not res.success and np.max(np.abs(res.jac))>1e-4:
            print('WARNING radial optimize', self.n, res.message, np.max(np.abs(res.jac)))
        return res

# continuum smooth radial interpolants of optimized profiles via PCHIP
from scipy.interpolate import PchipInterpolator

def background(model,res):
    f,chi=model.unpack(res.x)
    sf=PchipInterpolator(model.r,f);sc=PchipInterpolator(model.r,chi)
    return sf,sc

def radial_density_at(r,sf,sc):
    f=sf(r);chi=sc(r);fp=sf.derivative()(r);chip=sc.derivative()(r)
    s=np.sin(f);c=np.cos(f);y=chi-c;A,Ap,App=coeff(y)
    rr=np.maximum(r*r,1e-18);D=s*s/rr
    E2=.5*A*(r*r*fp*fp+2*s*s)+.5*r*r*chip*chip
    E4=LAM*(s*s*fp*fp+.5*s**4/rr)
    E0=.5*KAPPA*r*r*y*y+.5*MU*MU*r*r*(chi-1)**2
    return E2,E4,E0

# l=2 variations: F=f(r)+eps a(r)Y, Chi=chi(r)+eps b(r)Y,
# angular average Y^2=1, |grad_S Y|^2=l(l+1).
# Returns E'' at eps=0, integrated over 4pi r^2 dr. No weak gravity.
def second_variation(r,sf,sc,a,ap,b,bp,l=2):
    f=sf(r);fp=sf.derivative()(r);chi=sc(r);chip=sc.derivative()(r)
    si=np.sin(f);co=np.cos(f);y=chi-co
    A,Ay,Ayy=coeff(y)
    rr=r*r;inv=np.divide(1.,rr,out=np.zeros_like(rr),where=rr>0)
    S=si*si;Sf=np.sin(2*f);Sff=2*np.cos(2*f)
    # expansion of A(y) and tr(C)
    y1=b+si*a
    A1=Ay*y1
    A2=Ayy*y1*y1+Ay*co*a*a
    C0=fp*fp+2*S*inv
    C1=2*fp*ap+2*Sf*a*inv
    C2=2*ap*ap+2*l*(l+1)*a*a*inv+2*Sff*a*a*inv
    e2q=.5*(A2*C0+2*A1*C1+A*C2)
    e2chi=bp*bp+l*(l+1)*b*b*inv
    D=S*inv;D1=Sf*a*inv;D2=Sff*a*a*inv
    e4=LAM*(D2*fp*fp+4*D1*fp*ap+2*D*ap*ap +D*a*a*l*(l+1)*inv +D1*D1+D*D2)
    e0=KAPPA*(y1*y1+y*co*a*a)+MU**2*b*b
    result=4*np.pi*simpson(rr*(e2q+e2chi+e4+e0),x=r)
    return float(result)

def bases(r,l,widths=(.60, .95, 1.4, 2.0, 2.9, 4.1, 5.8, 8.2),Rbox=12):
    # positive, smooth at origin, vanish smoothly at finite outer boundary.
    modes=[]
    for w in widths:
        # radial functions f(r)= r^l exp(-(r/w)^2) (1-r/R)^2; normalize max amplitude to 1
        taper=(1-r/Rbox)**2
        tapd=-2*(1-r/Rbox)/Rbox
        gaussian=np.exp(-(r/w)**2)
        g=(r/w)**l*gaussian
        gd=gaussian*((l*(r/w)**l)/np.maximum(r,1.e-50)-2*r/w**2*(r/w)**l)
        # exact zero r derivative set for l>=2
        if l>=2: gd=np.where(r<1e-14,0.,gd)
        a=g*taper
        ap=gd*taper+g*tapd
        scale=max(float(np.max(abs(a))),1e-15)
        modes.append((a/scale,ap/scale))
    return modes

def projected_matrices(r,sf,sc,l=2,widths=(.6,.95,1.4,2.0,2.9,4.1,5.8,8.2)):
    bset=bases(r,l,widths,Rbox=max(r))
    m=len(bset);z=np.zeros_like(r);K=np.zeros((2*m,2*m));M=np.zeros_like(K)
    comps=[]
    for a,ap in bset:comps.append((a,ap,z,z))
    for b,bp in bset:comps.append((z,z,b,bp))
    # second variation quadratic form q(v)=v^T K v
    # q(e_i) diag, q(e_i+e_j) cross =2K_ij
    for i in range(2*m):
        K[i,i]=second_variation(r,sf,sc,*comps[i],l=l)
        for j in range(i):
            Kij=0.5*(second_variation(r,sf,sc,*[u+v for u,v in zip(comps[i],comps[j])],l=l)-K[i,i]-K[j,j])
            K[i,j]=K[j,i]=Kij
    f=sf(r);chi=sc(r); A,_,_=coeff(chi-np.cos(f))
    kinf=A+2*LAM*(np.sin(f)/np.maximum(r,1e-20))**2
    kinchi=np.ones_like(r)
    for i in range(2*m):
        for j in range(i+1):
            if i<m and j<m: dens=kinf*comps[i][0]*comps[j][0]
            elif i>=m and j>=m:dens=kinchi*comps[i][2]*comps[j][2]
            else:dens=0.
            Mij=4*np.pi*simpson(r*r*dens,x=r)
            M[i,j]=M[j,i]=Mij
    ew,evec=eigh(K,M)
    return K,M,ew,evec

def main():
    stats=[]; sols={}
    for n in [80,120,180]:
        model=Radial(n); x0=model.initial();eold=float(model.energy_grad(x0)[0]);res=model.minimize()
        f,chi=model.unpack(res.x)
        max_grad=np.max(abs(res.jac))
        vals=model.energy_grad(res.x,True)
        B=(-2/np.pi)*simpson(np.gradient(f,model.h)*np.sin(f)**2,x=model.r)
        s={"n":n,"h":model.h,"energy_old":eold,"energy_equilibrium":float(res.fun),"delta_energy":float(eold-res.fun),"components_E2_E4_E0":list(map(float,vals)),"iterations":int(res.nit),"success":bool(res.success),"optimizer_message":str(res.message),"max_abs_gradient":float(max_grad),"memory_delta_max":float(np.max(abs(chi-np.cos(f)))),"f_at_r1":float(np.interp(1,model.r,f)),"chi_at_r1":float(np.interp(1,model.r,chi)),"baryon_degree_radial_integral":float(B),"f_bounds":[float(np.min(f)),float(np.max(f))]}
        print('radial',s,flush=True)
        stats.append(s);sols[n]=(model,res)
        with (BASE/f'radial_profile_n{n}.csv').open('w',newline='') as file:
            w=csv.writer(file);w.writerow(['r','f','chi','cos_f','lag']);w.writerows(np.c_[model.r,f,chi,np.cos(f),chi-np.cos(f)])
    data=[]
    for n in [120,180]:
        model,res=sols[n];sf,sc=background(model,res)
        r=np.linspace(1e-4,model.R,2401)
        for l in [2,3]:
            K,M,ew,_=projected_matrices(r,sf,sc,l=l)
            data.append(dict(n=n,l=l,num_independent_radial_basis=int(K.shape[0]),lowest_omega_squared=float(ew[0]),second_omega_squared=float(ew[1]),max_off_diagonal_K=float(np.max(abs(K-np.diag(np.diag(K))))),min_mass_eig=float(np.min(np.linalg.eigvalsh(M)))))
            print('projected',data[-1],flush=True)
            np.savetxt(BASE/f'hessian_l{l}_n{n}.csv',K,delimiter=',')
            np.savetxt(BASE/f'mass_l{l}_n{n}.csv',M,delimiter=',')
    with (BASE/'equilibrium_convergence.csv').open('w',newline='') as file:
        w=csv.DictWriter(file,fieldnames=list(stats[0]));w.writeheader();w.writerows(stats)
    with (BASE/'restricted_modes.csv').open('w',newline='') as file:
        w=csv.DictWriter(file,fieldnames=list(data[0]));w.writeheader();w.writerows(data)
    audit={'equilibrium':stats,'projected_modes':data,'scope':'flat-space stationary Skyrme+chi hedgehog with l=2 and l=3 trial subspaces, NOT full perturbation spectrum, no dynamical gravity/no dissipation'}
    (BASE/'audit_v19.json').write_text(json.dumps(audit,indent=2,ensure_ascii=False))

if __name__=='__main__':main()
