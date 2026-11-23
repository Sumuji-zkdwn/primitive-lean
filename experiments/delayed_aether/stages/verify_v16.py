#!/usr/bin/env python3
"""第16回: 共変Skyrme+memory toy theory: a radial variational dynamics test,
plus time-symmetric conformally flat Einstein constraint initial data.

All quantities are dimensionless. This is not a derivation of Einstein gravity.
"""
import argparse, json
from pathlib import Path
import numpy as np
from scipy.integrate import solve_ivp, cumulative_trapezoid, trapezoid
import sympy as sp
import matplotlib.pyplot as plt

OUT = Path(__file__).resolve().parent
FOURPI = 4*np.pi


def A_with_derivative(y, delta=2., scale=.28):
    t = np.tanh(y/scale)
    return 1+delta*t*t, 2*delta/scale*t*(1-t*t)


def analytic_profile(r, radius=1.15, width=3.0):
    """Regular q hedgehog at r=0 with exponentially decaying tail."""
    r = np.asarray(r, dtype=float)
    amp = radius*np.exp(-r*r/(2*width*width))
    f = 2*np.arctan2(amp, r)
    deriv = np.zeros_like(r)
    mask = r>0
    x=r[mask]; a=amp[mask]
    deriv[mask] = -2*a*(1 + x*x/width**2)/(x*x+a*a)
    deriv[~mask] = -2/radius
    return f, deriv


def compact_profile(r, radius=1.15, width=3.0, R=12.0, taper_start=9.0):
    """Smoothly set f=f'=0 at finite outer boundary to fix topology."""
    f, fp=analytic_profile(r,radius,width)
    u=np.clip((r-taper_start)/(R-taper_start),0,1)
    w=1-10*u**3+15*u**4-6*u**5
    wp=(-30*u*u+60*u**3-30*u**4)/(R-taper_start)
    return f*w, fp*w+f*wp


class RadialModel:
    def __init__(self, n=96, R=12.0, delta=2., coupling=.9, lam=.20, mu=.15, scale=.28):
        self.n=n; self.R=R; self.h=R/n; self.r=np.arange(n+1)*self.h
        self.ri=self.r[1:-1]; self.rm=(np.arange(n)+.5)*self.h
        self.delta=delta; self.coupling=coupling; self.lam=lam; self.mu=mu; self.scale=scale
        self.w=FOURPI*self.h; self.k=n-1

    def full(self, f,chi):
        F=np.concatenate(([np.pi],f,[0.]))
        C=np.concatenate(([chi[0]],chi,[1.]))
        return F,C

    def potential_grad(self, f,chi):
        F,C=self.full(f,chi)
        fm=.5*(F[:-1]+F[1:]); cm=.5*(C[:-1]+C[1:])
        df=np.diff(F)/self.h; dc=np.diff(C)/self.h
        rm=self.rm
        sm=np.sin(fm); csm=np.cos(fm)
        am, apm=A_with_derivative(cm-np.cos(fm),self.delta,self.scale)
        tcoef=0.5*rm**2*am + self.lam*sm**2
        Vs=self.w*np.sum(tcoef*df*df +0.5*rm**2*dc*dc)
        dcoef_f=0.5*rm**2*apm*sm+2*self.lam*sm*csm
        dcoef_c=0.5*rm**2*apm
        gf=np.zeros(self.n+1); gc=np.zeros(self.n+1)
        gf[:-1]+=self.w*(.5*dcoef_f*df**2 -2*tcoef*df/self.h)
        gf[1:]+=self.w*(.5*dcoef_f*df**2 +2*tcoef*df/self.h)
        gc[:-1]+=self.w*(.5*dcoef_c*df**2 -rm**2*dc/self.h)
        gc[1:]+=self.w*(.5*dcoef_c*df**2 +rm**2*dc/self.h)
        # local angular & potential terms
        s=np.sin(f); c=np.cos(f); r=self.ri
        y=chi-c
        aa,da=A_with_derivative(y,self.delta,self.scale)
        Vl=self.w*np.sum(aa*s*s+0.5*self.lam*s**4/r**2 +r*r*(0.5*self.coupling*y*y+0.5*self.mu**2*(chi-1)**2))
        df_loc=self.w*(da*s**3 +2*aa*s*c+2*self.lam*s**3*c/r**2+self.coupling*r*r*y*s)
        dc_loc=self.w*(da*s*s+self.coupling*r*r*y+self.mu**2*r*r*(chi-1))
        # C[0] is constrained to C[1] (Neumann at origin).
        return Vs+Vl, gf[1:-1]+df_loc, gc[1:-1]+dc_loc+np.r_[gc[0],np.zeros(self.k-1)]

    def mass(self,f,chi):
        s=np.sin(f); c=np.cos(f);r=self.ri
        y=chi-c
        A,da=A_with_derivative(y,self.delta,self.scale)
        Mf=self.w*(r*r*A+2*self.lam*s*s)
        Mc=self.w*r*r
        Mf_f=self.w*(r*r*da*s+4*self.lam*s*c)
        Mf_c=self.w*r*r*da
        return Mf,Mc,Mf_f,Mf_c

    def initial(self, v=.09):
        F,fp=analytic_profile(self.r)
        F[-1]=0.0
        f=F[1:-1].copy()
        chi=np.cos(f).copy()
        ft=v*np.exp(-((self.ri-1.35)/0.7)**2)
        ct=np.zeros_like(f)
        Mf,Mc,*_=self.mass(f,chi)
        return np.r_[f,chi,Mf*ft,Mc*ct]

    def split(self,y):
        k=self.k
        return y[:k],y[k:2*k],y[2*k:3*k],y[3*k:4*k]

    def hamiltonian(self,y):
        f,c,pf,pc=self.split(y)
        Mf,Mc,*_=self.mass(f,c)
        V,*_=self.potential_grad(f,c)
        Tf=.5*np.sum(pf*pf/Mf); Tc=.5*np.sum(pc*pc/Mc)
        return Tf+Tc+V,Tf,Tc,V

    def rhs(self,t,y):
        f,c,pf,pc=self.split(y)
        Mf,Mc,Mff,Mfc=self.mass(f,c)
        V,Vf,Vc=self.potential_grad(f,c)
        ft=pf/Mf; ct=pc/Mc
        pdotf=-Vf+.5*ft*ft*Mff
        pdotc=-Vc+.5*ft*ft*Mfc
        return np.r_[ft,ct,pdotf,pdotc]

    def obs(self,y):
        f,c,pf,pc=self.split(y)
        ylag=c-np.cos(f)
        A,_=A_with_derivative(ylag,self.delta,self.scale)
        H,Tf,Tc,V=self.hamiltonian(y)
        return (H,Tf,Tc,V,np.max(np.abs(ylag)),np.max(A),np.linalg.norm(f-self.initial()[:self.k])/np.sqrt(self.k))

    def gradient_audit(self,y,nsamples=8,eps=2e-6):
        f,c,pf,pc=self.split(y)
        V,gf,gc=self.potential_grad(f,c)
        rng=np.random.default_rng(17)
        relative=[]
        for k in range(nsamples):
            df=rng.normal(size=len(f));dc=rng.normal(size=len(c));
            norm=np.sqrt(np.dot(df,df)+np.dot(dc,dc));df/=norm;dc/=norm
            VP=self.potential_grad(f+eps*df,c+eps*dc)[0]
            VM=self.potential_grad(f-eps*df,c-eps*dc)[0]
            ana=np.dot(gf,df)+np.dot(gc,dc)
            num=(VP-VM)/(2*eps)
            relative.append(abs(ana-num)/max(1,abs(ana),abs(num)))
        return max(relative)


def sympy_noether():
    """Symbolic 1+1 Noether test: generic f,chi and nonconstant A(y)."""
    t,x=sp.symbols('t x',real=True)
    f=sp.Function('f')(t,x);chi=sp.Function('chi')(t,x)
    y=chi-sp.cos(f)
    delta=sp.Rational(3,2); a=sp.Rational(2,5); k=sp.Rational(7,10)
    A=1+delta*y*y/(a*a+y*y)
    V=k*y*y/2+sp.sin(f)**2/sp.Integer(3)
    L=A*(sp.diff(f,t)**2-sp.diff(f,x)**2)/2+(sp.diff(chi,t)**2-sp.diff(chi,x)**2)/2-V
    # Euler-Lagrange equations in the + convention:
    Ef=sp.diff(sp.diff(L,sp.diff(f,t)),t)+sp.diff(sp.diff(L,sp.diff(f,x)),x)-sp.diff(L,f)
    Ec=sp.diff(sp.diff(L,sp.diff(chi,t)),t)+sp.diff(sp.diff(L,sp.diff(chi,x)),x)-sp.diff(L,chi)
    res=[]
    for coord in [t,x]:
        j0=sp.diff(L,sp.diff(f,t))*sp.diff(f,coord)+sp.diff(L,sp.diff(chi,t))*sp.diff(chi,coord)-(L if coord==t else 0)
        j1=sp.diff(L,sp.diff(f,x))*sp.diff(f,coord)+sp.diff(L,sp.diff(chi,x))*sp.diff(chi,coord)-(L if coord==x else 0)
        ident=sp.diff(j0,t)+sp.diff(j1,x)-Ef*sp.diff(f,coord)-Ec*sp.diff(chi,coord)
        ans=sp.simplify(sp.expand(ident))
        res.append(ans==0)
    if not all(res): raise AssertionError(f'Symbolic Noether failure: {res}')
    return {'1+1_energy_identity':bool(res[0]),'1+1_momentum_identity':bool(res[1]),'note':'Symbolic 1+1 subsector; full 3+1 Noether identity follows from diffeomorphism invariance on shell.'}


def evolve(n=96,T=.45,dt_out=.01,delta=2.,coupling=.9,rtol=3e-10,atol=3e-12):
    m=RadialModel(n=n,delta=delta,coupling=coupling)
    y0=m.initial()
    audit=m.gradient_audit(y0)
    t_eval=np.linspace(0,T,int(round(T/dt_out))+1)
    sol=solve_ivp(m.rhs,(0,T),y0,method='DOP853',rtol=rtol,atol=atol,t_eval=t_eval)
    if not sol.success:raise RuntimeError(sol.message)
    obs=np.asarray([m.obs(sol.y[:,k]) for k in range(len(sol.t))])
    H0=obs[0,0]
    obs_err=float(np.max(np.abs(obs[:,0]-H0))/H0)
    return m,sol,obs,{'gradient_directional_relative_max':audit,'energy_relative_drift':obs_err,
                      't_eval_count':len(sol.t),'solver_rhs_evaluations':sol.nfev,
                      'max_lag':float(np.max(obs[:,4])),'max_hardening':float(np.max(obs[:,5])),
                      'final_H':float(obs[-1,0]), 'initial_H':float(H0)}


def constraint(n=900, radius=1.15, width=3., coupling=.9, lam=.20, mu=.15, G=0.00065, R=12., lag_amp=0.):
    """Solve Lichnerowicz Hamiltonian constraint on time symmetric conformally flat slice.
    Exterior Schwarzschild-like isotropic tail psi=1+C/r for r>=R (not a vacuum Einstein evolution).
    Momentum constraint is trivially satisfied by time symmetry.
    """
    r=np.linspace(0,R,n+1)
    f,fp=compact_profile(r,radius,width,R=R)
    chi=np.cos(f)+lag_amp*np.sin(f)**2
    chip=(-np.sin(f)+2*lag_amp*np.sin(f)*np.cos(f))*fp
    sover=np.zeros_like(r);sover[1:]=np.sin(f[1:])/r[1:];sover[0]=2/radius
    y=chi-np.cos(f) # exactly zero, A=1 initially
    aa,_=A_with_derivative(y)
    def density(psi):
        E2=0.5*aa*psi**-4*(fp**2+2*sover**2)
        E4=0.5*lam*psi**-8*(2*sover**2*fp**2+sover**4)
        Ec=0.5*psi**-4*chip**2 +0.5*mu*mu*(chi-1)**2+0.5*coupling*y*y
        return E2+E4+Ec
    psi=np.ones_like(r)
    iters=0;err=np.inf
    for i in range(1000):
        S=2*np.pi*G*psi**5*density(psi)
        integ=cumulative_trapezoid(r*r*S,r,initial=0)
        F=np.zeros_like(r);F[1:]=integ[1:]/r[1:]**2
        # Match a vacuum harmonic exterior psi=1+integ(R)/r, with psi(infty)=1.
        new=1+integ[-1]/R-cumulative_trapezoid(F[::-1],r[::-1],initial=0)[::-1]
        err=float(np.max(abs(new-psi)))
        psi=.65*new+.35*psi
        iters=i+1
        if err<1e-12: break
    S=2*np.pi*G*psi**5*density(psi)
    integ=cumulative_trapezoid(r*r*S,r,initial=0)
    F=np.zeros_like(r);F[1:]=integ[1:]/r[1:]**2
    # The conservative radial finite-volume finite difference at nodes j=1...n-1.
    h=r[1]
    rp=r[1:-1]+h/2; rm=r[1:-1]-h/2
    lap=(rp**2*(psi[2:]-psi[1:-1])/h-rm**2*(psi[1:-1]-psi[:-2])/h)/(r[1:-1]**2*h)
    res=lap+S[1:-1]
    region=(r[1:-1]>.45)&(r[1:-1]<R-1)
    residual=float(np.sqrt(np.mean(res[region]**2)))
    source=float(np.sqrt(np.mean(S[1:-1][region]**2)))
    Msource=float(FOURPI*trapezoid(r*r*psi**5*density(psi),r))
    Mflux=float(2*integ[-1]/G)
    output={'grid_n':n,'G':G,'initial_memory_lag_amplitude':lag_amp,'radius_box':R,'iteration_count':iters,'last_unrelaxed_difference':err,
            'psi_at_center':float(psi[0]),'min_psi':float(np.min(psi)),'max_psi':float(np.max(psi)),
            'psi_outer_boundary':float(psi[-1]),
            'asymptotic_matching_robin_residual':float(abs(psi[-1]-1-R*F[-1])),
            'hamiltonian_constraint_rms':residual,'hamiltonian_constraint_relative_rms':residual/source,
            'mass_from_source':Msource,'mass_from_boundary_flux':Mflux,
            'mass_relative_disagreement':abs(Msource-Mflux)/Msource,
            'max_2GM_over_r':float(np.max(2*G*FOURPI*cumulative_trapezoid(r*r*psi**5*density(psi),r,initial=0)[1:]/r[1:])),
            'field_hedgehog_degree_boundary':1.0,
            'momentum_constraint':'exactly zero (time-symmetric initial data)'}
    return r,psi,density(psi),S,output


def main():
    OUT.mkdir(exist_ok=True)
    import csv
    sym=sympy_noether()
    m,sol,obs,integrator=evolve(n=96,T=.55)
    # Control 1: remove nonlinear hardening but retain the same potential coupling.
    ctrl,sol0,ob0,contro=evolve(n=96,T=.55,delta=0,coupling=.9)
    # Control 2: fully decoupled (both nonlinear A and coupling potential removed).
    isolated,soli,obi,isolate_audit=evolve(n=96,T=.55,delta=0,coupling=0)
    # convergence in time solver tolerances and radial discretization
    _,_,_,fine=evolve(n=96,T=.55,delta=2,coupling=.9,rtol=8e-12,atol=8e-14)
    with open(OUT/'radial_dynamics.csv','w',newline='') as file:
        wr=csv.writer(file)
        wr.writerow(['time','H','T_q','T_chi','V','max_abs_chi_minus_q0','max_A','profile_RMS_shift',
                     'control_H','control_T_q','control_T_chi','control_V','control_lag','control_max_A','control_profile_shift','isolated_H','isolated_T_q','isolated_T_chi','isolated_V','isolated_lag','isolated_max_A','isolated_profile_shift'])
        for t,a,b,z in zip(sol.t,obs,ob0,obi):wr.writerow([float(t),*[float(x) for x in a],*[float(x) for x in b],*[float(x) for x in z]])
    # Gravity constraint benchmark convergence: aligned and lagged memory states.
    gr=[]; grlag=[]
    for n in (300,600,1200):
        r,psi,rho,S,g=constraint(n=n,lag_amp=0)
        gr.append(g)
        if n==1200:
            rbase,psibase,rhobase,Sbase=r,psi,rho,S
        r,psi,rho,S,g=constraint(n=n,lag_amp=.18)
        grlag.append(g)
        if n==1200:
            with open(OUT/'einstein_constraint_profile.csv','w',newline='') as file:
                wr=csv.writer(file);wr.writerow(['r','psi_lagged','psi_aligned','rho_lagged','rho_aligned',
                                                  'poisson_source_2piG_psi5rho_lagged',
                                                  'poisson_source_2piG_psi5rho_aligned'])
                wr.writerows(zip(r,psi,psibase,rho,rhobase,S,Sbase))
    # Independent gradient check at a later dynamical state
    later_grad=m.gradient_audit(sol.y[:,len(sol.t)//2])
    # plots
    fig,axs=plt.subplots(3,1,figsize=(8,8),sharex=True)
    axs[0].plot(sol.t,obs[:,1],label='topological-field kinetic Tq')
    axs[0].plot(sol.t,obs[:,2],label='memory-field kinetic Tchi')
    axs[0].plot(sol.t,obs[:,3]-obs[0,3],label='potential delta V')
    axs[0].legend(fontsize=8);axs[0].set_ylabel('Energy / change')
    axs[1].plot(sol.t,obs[:,4],label='coupled |chi - q0| max')
    axs[1].plot(sol.t,ob0[:,4],linestyle='--',label='no-hardening control lag')
    axs[1].legend(fontsize=8);axs[1].set_ylabel('Lag amplitude')
    axs[2].plot(sol.t,obs[:,5],label='coupled stiffness A')
    axs[2].plot(sol.t,ob0[:,5],linestyle='--',label='control A=1')
    axs[2].legend(fontsize=8);axs[2].set_ylabel('Effective coefficient');axs[2].set_xlabel('Model time')
    fig.suptitle('v16: covariant topological field + reversible internal memory');fig.tight_layout()
    fig.savefig(OUT/'topological_memory_dynamics.png',dpi=145);plt.close(fig)
    fig,ax=plt.subplots(figsize=(8,4.5))
    ax.plot(sol.t,(obs[:,0]-obs[0,0])/obs[0,0],label='coupled')
    ax.plot(sol.t,(ob0[:,0]-ob0[0,0])/ob0[0,0],label='no-hardening control',alpha=.8)
    ax.set_xlabel('Model time');ax.set_ylabel('Relative total energy drift')
    ax.legend();fig.tight_layout();fig.savefig(OUT/'energy_conservation.png',dpi=145);plt.close(fig)
    fig,axes=plt.subplots(2,1,figsize=(8,7),sharex=True)
    axes[0].plot(r,psi,label='lagged memory psi')
    axes[0].plot(r,psibase,linestyle='--',label='aligned memory psi')
    axes[0].legend();axes[0].set_ylabel('psi(r)')
    axes[1].plot(r,rho,label='lagged memory energy density')
    axes[1].plot(r,rhobase,linestyle='--',label='aligned memory energy density')
    axes[1].legend();axes[1].set_xlabel('r');axes[1].set_ylabel('rho(r)')
    fig.suptitle('v16: time-symmetric Einstein constraint initial data');fig.tight_layout();fig.savefig(OUT/'einstein_initial_constraint.png',dpi=145);plt.close(fig)
    f,c,pf,pc=m.split(sol.y[:,-1]);f0,c0,_,_=m.split(sol.y[:,0]);
    fig,ax=plt.subplots(figsize=(8,4.5))
    ax.plot(m.ri,f0,label='f initial')
    ax.plot(m.ri,f,label='f at final time')
    ax.plot(m.ri,c,label='chi final')
    ax.plot(m.ri,np.cos(f),label='q0 = cos(f) final',linestyle='--')
    ax.set_xlim(0,6);ax.set_xlabel('Radius');ax.legend();fig.tight_layout();fig.savefig(OUT/'radial_profiles.png',dpi=145);plt.close(fig)
    report={'symbolic':sym,'dynamics_coupled':integrator,'dynamics_control_no_hardening':contro,'dynamics_isolated':isolate_audit,'dynamics_tight_tol':fine,
            'gradient_audit_late':later_grad,'radial_q_fixed_boundary_degree':1,
            'grav_initial_constraint_aligned_memory':gr,'grav_initial_constraint_lagged_memory':grlag,
            'qualifications':['Dynamic radial evolution computed on flat spacetime, not dynamical Einstein+matter.',
                              'Curved Einstein constraint solved for time-symmetric prescribed q,chi initial data only.',
                              'Topological degree = 1 follows from imposed radial boundaries; no 3D nonspherical topological stability demonstrated.',
                              'chi is a reversible dynamical field; no irreversible viscoelastic relaxation from this closed action.',
                              'GR gravity is assumed via Einstein-Hilbert action and constraints, not derived from ether.']}
    (OUT/'audit_v16.json').write_text(json.dumps(report,ensure_ascii=False,indent=2))
    print(json.dumps(report,ensure_ascii=False,indent=2))

if __name__=='__main__': main()