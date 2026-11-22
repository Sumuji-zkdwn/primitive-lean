#!/usr/bin/env python3
"""Einstein–hedgehog Skyrme–chi: spherical constrained evolution, dimensionless.
Not an emergent derivation of gravity. Polar-areal slicing, zero shift.

Metric ds^2=-alpha^2 dt^2+a^2 dr^2+r^2 dOmega^2. Einstein constraints
m'=4*pi*r^2*rho, alpha'/alpha=a^2*(G*m/r^2+4*pi*G*r*pr),
a^2=(1-2G*m/r)^-1; independently checked Einstein momentum evolution
a_t=4*pi*G*r*alpha*(w_f f_r+w_chi chi_r).

Matter density and pressures derived from v16 generally covariant action.
Evolved matter variables are interior-node f,chi, canonical p_f,p_chi with
p_f=4*pi*h*r^2*(a/alpha)*Sigma*f_t and p_chi=4*pi*h*r^2*(a/alpha)*chi_t.
Fields are fixed f(0)=pi, f(R)=0, chi_r(0)=0, chi(R)=1.
"""
from __future__ import annotations
import numpy as np
from scipy.integrate import cumulative_trapezoid, solve_ivp
from dataclasses import dataclass
from pathlib import Path
import time, csv, json

FOURPI=4*np.pi
OUT=Path(__file__).resolve().parent


def A_and_derivative(y,delta=2.0,scale=0.28):
    z=np.tanh(y/scale)
    return 1+delta*z*z,2*delta/scale*z*(1-z*z)


def compact_initial(r, radius=1.15,width=3.0,R=12.,taper_start=9.):
    amp=radius*np.exp(-r*r/(2*width*width))
    f=2*np.arctan2(amp, r)
    u=np.clip((r-taper_start)/(R-taper_start),0,1)
    w=1-10*u**3+15*u**4-6*u**5
    return f*w


@dataclass
class Snapshot:
    m:np.ndarray
    a:np.ndarray
    alpha:np.ndarray
    rho:np.ndarray
    pr:np.ndarray
    gradf:np.ndarray
    gradchi:np.ndarray
    B:np.ndarray
    U:np.ndarray
    w_f:np.ndarray
    w_chi:np.ndarray
    Sigma:np.ndarray
    K:np.ndarray
    W:np.ndarray
    radial_ham_rms:float
    radial_slice_rms:float
    p_f:np.ndarray
    p_chi:np.ndarray
    f:np.ndarray
    chi:np.ndarray


class Model:
    def __init__(self,n=80,R=12.,G=0.00065,lam=0.2,kappa=0.9,mu=0.15,delta=2.,scale=0.28,kick=0.08):
        self.n=n; self.R=R; self.r=np.linspace(0,R,n+1); self.ri=self.r[1:-1]
        self.rm=.5*(self.r[:-1]+self.r[1:]); self.h=R/n; self.k=n-1
        self.G=G; self.lam=lam; self.kappa=kappa; self.mu=mu; self.delta=delta; self.scale=scale; self.kick=kick
        self.fac=FOURPI*self.h

    def full(self,f,chi):
        return np.r_[np.pi,f,0.],np.r_[chi[0],chi,1.]

    def unpack(self,y):
        k=self.k; return y[:k],y[k:2*k],y[2*k:3*k],y[3*k:4*k]

    def initial(self):
        F=compact_initial(self.r,R=self.R)
        f=F[1:-1]; chi=np.cos(f).copy()
        s=np.sin(f);Sigma=1+2*self.lam*s*s/self.ri**2
        # use same canonical initial data at G=0 and at G>0 as a controlled comparison
        ft=self.kick*np.exp(-((self.ri-1.35)/.7)**2)
        p_f=self.fac*self.ri**2*Sigma*ft
        p_chi=np.zeros_like(p_f)
        return np.r_[f,chi,p_f,p_chi]

    def snapshot(self,y,audit=False):
        f,chi,pf,pc=self.unpack(y)
        F,C=self.full(f,chi);r=self.r;h=self.h
        ff=np.gradient(F,h,edge_order=2)
        cc=np.gradient(C,h,edge_order=2)
        cc[0]=0
        sn=np.sin(F);co=np.cos(F);lag=C-co
        A,_=A_and_derivative(lag,self.delta,self.scale)
        sover=np.zeros_like(r)
        sover[1:]=sn[1:]/r[1:]
        sover[0]=-ff[0] # sin(pi+f'(0)r) ~ -f'(0)r
        Sigma=A+2*self.lam*sover**2
        W=A*sover**2+0.5*self.lam*sover**4+0.5*self.kappa*lag**2+0.5*self.mu**2*(C-1)**2
        wf=np.zeros_like(r);wc=np.zeros_like(r)
        wf[1:-1]=pf/(self.fac*self.ri**2)
        wc[1:-1]=pc/(self.fac*self.ri**2)
        wf[0]=0;wc[0]=0;wf[-1]=0;wc[-1]=0
        K=.5*(wf**2/Sigma+wc**2+Sigma*ff**2+cc**2)
        # Hamiltonian constraint m' + 8*pi*G*r*K*m = 4*pi*r^2*(K+W).
        b=8*np.pi*self.G*r*K
        c=FOURPI*r*r*(K+W)
        if self.G:
            B=cumulative_trapezoid(b,r,initial=0)
            m=np.exp(-B)*cumulative_trapezoid(np.exp(B)*c,r,initial=0)
            cone=np.ones_like(r);cone[1:]=1-2*self.G*m[1:]/r[1:]
            if np.min(cone)<.15: raise RuntimeError('polar areal gauge approaching horizon')
            aa=1/np.sqrt(cone)
            rho=cone*K+W
            pr=cone*K-W
            beta=np.zeros_like(r);beta[1:]=aa[1:]**2*(self.G*m[1:]/r[1:]**2+FOURPI*self.G*r[1:]*pr[1:])
            beta[0]=0
            total=cumulative_trapezoid(beta,r,initial=0)
            logalpha=np.log(np.sqrt(cone[-1]))+total-total[-1]
            alpha=np.exp(logalpha)
        else:
            m=cumulative_trapezoid(c,r,initial=0)
            aa=np.ones_like(r);alpha=np.ones_like(r)
            rho=K+W;pr=K-W;beta=np.zeros_like(r)
        if audit:
            md=np.gradient(m,h,edge_order=2)
            drpred=FOURPI*r*r*rho
            rr=(r>.3)&(r<self.R-1.5)
            radial_ham=float(np.linalg.norm((md-drpred)[rr])/max(np.linalg.norm(drpred[rr]),1.e-30))
            ad=np.gradient(np.log(alpha),h,edge_order=2)
            radial_slice=float(np.linalg.norm((ad-beta)[rr])/max(np.linalg.norm(beta[rr]),1.e-30)) if self.G else 0
        else: radial_ham=radial_slice=float('nan')
        return Snapshot(m,aa,alpha,rho,pr,ff,cc,B if self.G else np.zeros_like(r),W,wf,wc,Sigma,K,W,radial_ham,radial_slice,pf,pc,f,chi)

    def derivative(self,t,y):
        f,chi,pf,pc=self.unpack(y)
        metric=self.snapshot(y)
        F,C=self.full(f,chi)
        rm=self.rm;h=self.h
        fm=.5*(F[:-1]+F[1:]);cm=.5*(C[:-1]+C[1:]);df=np.diff(F)/h;dc=np.diff(C)/h
        sn=np.sin(fm);co=np.cos(fm)
        A,Aprime=A_and_derivative(cm-np.cos(fm),self.delta,self.scale)
        coef=.5*rm**2*A+self.lam*sn**2
        cf=.5*rm**2*Aprime*sn+2*self.lam*sn*co
        cc=.5*rm**2*Aprime
        # metric at edge: average neighboring alpha/a, second-order approximation
        wa=.5*((metric.alpha/metric.a)[:-1]+(metric.alpha/metric.a)[1:])
        factor=self.fac*wa
        gf=np.zeros(self.n+1);gc=np.zeros(self.n+1)
        gf[:-1]+=factor*(.5*cf*df**2-2*coef*df/h)
        gf[1:]+=factor*(.5*cf*df**2+2*coef*df/h)
        gc[:-1]+=factor*(.5*cc*df**2-rm**2*dc/h)
        gc[1:]+=factor*(.5*cc*df**2+rm**2*dc/h)
        s=np.sin(f);c=np.cos(f);ri=self.ri
        lag=chi-c;Ai,Apy=A_and_derivative(lag,self.delta,self.scale)
        weight=self.fac*metric.alpha[1:-1]*metric.a[1:-1]
        gf_loc=weight*(Apy*s**3+2*Ai*s*c+2*self.lam*s**3*c/ri**2+self.kappa*ri**2*lag*s)
        gc_loc=weight*(Apy*s**2+ri**2*(self.kappa*lag+self.mu**2*(chi-1)))
        gf=gf[1:-1]+gf_loc
        gc=gc[1:-1]+gc_loc+np.r_[gc[0],np.zeros(self.k-1)]
        massbase=self.fac*ri**2*metric.a[1:-1]/metric.alpha[1:-1]
        S=Ai+2*self.lam*s**2/ri**2
        Mf=massbase*S;Mc=massbase
        ft=pf/Mf;ct=pc/Mc
        Mff=massbase*(Apy*s+4*self.lam*s*c/ri**2)
        Mfc=massbase*Apy
        pft=-gf+.5*ft**2*Mff
        pct=-gc+.5*ft**2*Mfc
        return np.r_[ft,ct,pft,pct]

    def diagnostic(self,t,y):
        s=self.snapshot(y,audit=True)
        obs={
            'time':float(t),'total_mass':float(s.m[-1]), 'center_lapse':float(s.alpha[0]),
            'surface_lapse':float(s.alpha[-1]),'center_a':float(s.a[0]),
            'max_compactness':float(np.max(2*self.G*s.m[1:]/self.r[1:])),
            'max_hardening':float(np.max(s.Sigma[1:-1]-2*self.lam*np.sin(s.f)**2/self.ri**2)),
            'max_memory_lag':float(np.max(abs(s.chi-np.cos(s.f)))),
            'hamiltonian_radial_relative_residual':s.radial_ham_rms,
            'slicing_radial_relative_residual':s.radial_slice_rms,
            'radial_mass_center':float(np.interp(2,self.r,s.m)),
            'f_at_r1':float(np.interp(1,self.r,self.full(s.f,s.chi)[0])),
            'chi_at_r1':float(np.interp(1,self.r,self.full(s.f,s.chi)[1])),
            'm_profile':s.m,'a_profile':s.a,'alpha_profile':s.alpha,
            'matter_flux':s.w_f*s.gradf+s.w_chi*s.gradchi,
        }
        return obs


def run(n=64,G=.00065,T=.28,kick=.08,dt=.01,rtol=5e-9,atol=1e-11,delta=2.0):
    model=Model(n=n,G=G,kick=kick,delta=delta)
    initial=model.initial()
    te=np.linspace(0,T,int(round(T/dt))+1)
    tic=time.monotonic()
    sol=solve_ivp(model.derivative,(0,T),initial,t_eval=te,method='DOP853',rtol=rtol,atol=atol)
    if not sol.success:raise RuntimeError(sol.message)
    diag=[model.diagnostic(float(t),sol.y[:,idx]) for idx,t in enumerate(te)]
    r=model.r
    # independent differential Einstein momentum equation (not used in evolution):
    # m_t=4*pi*r^2 alpha/a^3*(w_f*f_r+w_chi*chi_r)
    mm=np.array([d['m_profile'] for d in diag]); al=np.array([d['alpha_profile'] for d in diag]); a=np.array([d['a_profile'] for d in diag]); mf=np.array([d['matter_flux'] for d in diag])
    mdot=np.gradient(mm,te,axis=0,edge_order=2)
    expected=FOURPI*(r[None,:]**2)*(al/a**3)*mf
    maskr=(r>.3)&(r<8.)
    maskt=np.arange(len(te))[1:-1]
    # relative L2 residual over time-radius, avoids arbitrarily small denominator at node level
    diff=mdot[1:-1,maskr]-expected[1:-1,maskr]
    scales=np.linalg.norm(expected[1:-1,maskr])
    err=float(np.linalg.norm(diff)/max(scales,1e-30)) if G>0 else None
    # absolute scaled to signal: Einstein momentum evolution nonzero
    res_abs=float(np.sqrt(np.mean(diff*diff)))
    maxrelative_mass=float(np.max(abs(mm[:,-1]-mm[0,-1]))/mm[0,-1])
    # independent constraint propagation: a_t vs flux (equivalent, different finite form)
    adot=np.gradient(a,te,axis=0,edge_order=2)
    resid_a=adot-FOURPI*G*r[None,:]*al*mf
    scale_a=np.linalg.norm((FOURPI*G*r[None,:]*al*mf)[1:-1,maskr])
    momentum_a=float(np.linalg.norm(resid_a[1:-1,maskr])/max(scale_a,1e-30)) if G else None
    summaries={
        'n':n,'G':G,'T':T,'dt_observation':dt,'solver_nfev':sol.nfev,
        'runtime_seconds':time.monotonic()-tic,
        'metric_mass_initial':diag[0]['total_mass'],
        'metric_mass_final':diag[-1]['total_mass'],
        'max_relative_total_mass_drift':maxrelative_mass,
        'initial_center_lapse':diag[0]['center_lapse'],
        'final_center_lapse':diag[-1]['center_lapse'],
        'center_lapse_change':diag[-1]['center_lapse']-diag[0]['center_lapse'],
        'max_compactness':max(d['max_compactness'] for d in diag),
        'maximum_hardening':max(d['max_hardening'] for d in diag),
        'maximum_abs_memory_lag':max(d['max_memory_lag'] for d in diag),
        'max_radial_hamiltonian_residual':max(d['hamiltonian_radial_relative_residual'] for d in diag),
        'max_radial_slicing_residual':max(d['slicing_radial_relative_residual'] for d in diag),
        'independent_momentum_residual_rel_l2':err,
        'independent_momentum_residual_rms':res_abs,
        'independent_metric_a_t_residual_rel_l2':momentum_a,
        'mid_shell_mass_change':diag[-1]['radial_mass_center']-diag[0]['radial_mass_center'],
        'nontrivial_q_profile_change_at_r1':diag[-1]['f_at_r1']-diag[0]['f_at_r1'],
    }
    return model,sol,diag,summaries


def main():
    configs=[(64,.00065,.28,.01),(96,.00065,.28,.01),(144,.00065,.28,.01),(96,.0,.28,.01),(96,.002,.28,.01),
             (96,.00065,.28,.005),(96,.00065,.28,.0025)]
    allresults={}; results=[]; raw={}
    for n,G,T,dt in configs:
        key=f'N{n}_G{G:.5f}_dt{dt}'
        model,sol,diag,s=run(n,G,T,dt=dt)
        print(key,'mom',s['independent_momentum_residual_rel_l2'],'mass',s['max_relative_total_mass_drift'],'wall',s['runtime_seconds'],flush=True)
        allresults[key]=s
        results.append(s)
        raw[key]=(model,sol,diag)
        if n==96 and G==.00065 and dt==.01:
            with (OUT/'time_series.csv').open('w',newline='') as f:
                writer=csv.writer(f)
                fields=['time','total_mass','center_lapse','max_compactness','max_hardening','max_memory_lag','hamiltonian_radial_relative_residual','slicing_radial_relative_residual','radial_mass_center','f_at_r1','chi_at_r1']
                writer.writerow(fields)
                writer.writerows([[d[k] for k in fields] for d in diag])
            for idx in [0,len(diag)//2,len(diag)-1]:
                ds=diag[idx]
                np.savetxt(OUT/f'metric_profiles_t{idx:02}.csv',np.c_[model.r,ds['m_profile'],ds['a_profile'],ds['alpha_profile']],delimiter=',',header='r,m,a,alpha',comments='')
    with (OUT/'summary.json').open('w') as f:json.dump(allresults,f,indent=2)
    with (OUT/'summary.csv').open('w',newline='') as f:
        keys=list(results[0]);w=csv.DictWriter(f,fieldnames=keys);w.writeheader();w.writerows(results)
    return results,raw


if __name__=='__main__': main()
