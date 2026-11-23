#!/usr/bin/env python3
"""Finite-radius corotational Skyrme + causal scalar + dissipative strain-memory toy model.

Radial sector only; the memory channels follow (F', sin(F)/r), not a proven
covariant 3D constitutive theory. See RESEARCH_NOTE for limitations.
"""
from __future__ import annotations
from dataclasses import dataclass
from pathlib import Path
import csv, math, argparse
import numpy as np
from scipy.integrate import solve_ivp
from scipy.optimize import minimize
from radial_profile_positive import Radial
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

OUT=Path(__file__).resolve().parent
PI=np.pi

@dataclass
class Params:
    dr: float=.16
    tau: float=1.0
    k: float=.9
    eta: float=20.0
    gamma_q: float=.25
    gamma_h: float=.4
    mass_q: float=1.0
    mass_h: float=2.0
    alpha: float=.25
    t_final: float=8.0
    amplitude: float=.19
    L: float=16.0

class Evolution:
    def __init__(self,p):
        self.p=p
        self.model=Radial(L=p.L,dr=p.dr,alpha=p.alpha)
        self.n=self.model.n
        self.r=self.model.r;self.rn=np.arange(self.n+1)*self.model.dr
        self.w=self.model.w
        self.Fmass=p.mass_q*4*PI*self.rn[1:-1]**2*self.model.dr
        self.Hmass=p.mass_h*self.w
        self.slices={};k=0
        for name,n in [('F',self.n-1),('vF',self.n-1),('h',self.n),('vh',self.n),('zr',self.n),('zt',self.n),('diss',1)]:
            self.slices[name]=slice(k,k+n);k+=n
        self.ndim=k
    def pack(self,**kw):
        y=np.empty(self.ndim)
        for name,s in self.slices.items():y[s]=kw[name]
        return y
    def unpack(self,y):return {name:y[s] for name,s in self.slices.items()}
    def strain(self,x):
        F=np.r_[PI,x,0.]
        fm=(F[1:]+F[:-1])/2
        return np.diff(F)/self.model.dr,np.sin(fm)/self.r,fm
    def field_A(self,h):
        m=self.model
        Ah=m.diag*h
        Ah=Ah.copy()
        Ah[:-1]+=m.sub*h[1:]
        Ah[1:]+=m.sub*h[:-1]
        return Ah
    def potential(self,x,h,zr,zt,gradient=False):
        p=self.p;m=self.model;dr=m.dr;r=self.r;w=self.w
        df,st,fm=self.strain(x)
        s=np.sin(fm);c=np.cos(fm)
        rho2=.5*df**2+st**2
        rho4=st**2*df**2+.5*st**4
        v=m.g*h
        cf=1-v+.5*v**2
        yr=df-zr;yt=st-zt
        mem=.5*p.k*(yr**2+2*yt**2)+.25*p.eta*(yr**4+2*yt**4)
        Ah=self.field_A(h)
        Ebase=float(np.dot(w,cf*rho2+rho4)+.5*np.dot(h,Ah))
        Emem=float(np.dot(w,mem))
        if not gradient:return Ebase+Emem,Ebase,Emem
        sr=p.k*yr+p.eta*yr**3
        stt=p.k*yt+p.eta*yt**3
        dEddf=w*(cf*df+2*st**2*df+sr)
        dEdfm=w*(cf*2*st*c/r+2*st*c*df**2/r+2*st**3*c/r+2*stt*c/r)
        gradnodes=np.zeros(self.n+1)
        gradnodes[:-1]+=-dEddf/dr+.5*dEdfm
        gradnodes[1:]+=dEddf/dr+.5*dEdfm
        gradF=gradnodes[1:-1]
        gradH=w*m.g*(v-1)*rho2+Ah
        loss_mem=float(np.dot(w,(p.k*yr**2+p.eta*yr**4+2*p.k*yt**2+2*p.eta*yt**4))/p.tau)
        return Ebase+Emem,gradF,gradH,loss_mem,Ebase,Emem
    def energy(self,y):
        s=self.unpack(y)
        pot,base,mem=self.potential(s['F'],s['h'],s['zr'],s['zt'])
        Tq=.5*float(np.dot(self.Fmass,s['vF']**2))
        Th=.5*float(np.dot(self.Hmass,s['vh']**2))
        return pot+Tq+Th,base,mem,Tq,Th
    def rhs(self,t,y):
        s=self.unpack(y);p=self.p
        F=s['F'];vF=s['vF'];h=s['h'];vh=s['vh'];zr=s['zr'];zt=s['zt']
        _,gradF,gradH,_,_,_=self.potential(F,h,zr,zt,gradient=True)
        er,et,_=self.strain(F)
        dzr=(er-zr)/p.tau;dzt=(et-zt)/p.tau
        dvF=-gradF/self.Fmass-p.gamma_q*vF
        dvh=-gradH/self.Hmass-p.gamma_h*vh
        return self.pack(F=vF,vF=dvF,h=vh,vh=dvh,zr=dzr,zt=dzt,diss=np.array([sum(self.dissipation(y))]))
    def dissipation(self,y):
        s=self.unpack(y)
        _,_,_,Dmem,_,_=self.potential(s['F'],s['h'],s['zr'],s['zt'],gradient=True)
        Dq=self.p.gamma_q*float(np.dot(self.Fmass,s['vF']**2))
        Dh=self.p.gamma_h*float(np.dot(self.Hmass,s['vh']**2))
        return Dmem,Dq,Dh
    def init(self,quiet=False):
        sol=self.model.optimize(maxiter=2500)
        if not quiet:print('static opt:',sol.success,sol.nit,sol.fun,'grad_inf',np.max(np.abs(self.model.evaluate(sol.x)[1])),flush=True)
        F0=sol.x
        h0=self.model.evaluate(F0,details=True)['h']
        e0r,e0t,_=self.strain(F0)
        gn=np.exp(-.5*((self.rn[1:-1]-1.1)/.42)**2)
        F=F0+self.p.amplitude*gn
        zeroF=np.zeros_like(F);zeroh=np.zeros_like(h0)
        y=self.pack(F=F,vF=zeroF,h=h0,vh=zeroh,zr=e0r,zt=e0t,diss=np.array([0.0]))
        return y,F0,h0
    def observable(self,t,y,F0):
        s=self.unpack(y);p=self.p
        E,base,mem,Tq,Th=self.energy(y)
        er,et,_=self.strain(s['F']);yr=er-s['zr'];yt=et-s['zt']
        yabs=max(float(np.max(abs(yr))),float(np.max(abs(yt))))
        incmod=p.k+3*p.eta*yabs*yabs
        Dmem,Dq,Dh=self.dissipation(y)
        amp=float(np.sqrt(np.dot(self.Fmass,(s['F']-F0)**2)/sum(self.Fmass)))
        Ffull=np.r_[PI,s['F'],0.]
        crossings=np.where(np.diff(np.sign(Ffull-PI/2))!=0)[0]
        rad=np.nan
        if len(crossings)>0:
            i=crossings[0]
            rad=float(self.rn[i]+(PI/2-Ffull[i])*(self.rn[i+1]-self.rn[i])/(Ffull[i+1]-Ffull[i]))
        rho2=.5*er**2+et**2
        geff=float(np.dot(self.w,self.model.g*rho2*(1-self.model.g*s['h'])))
        ah=self.field_A(s['h'])
        source_balance=float(np.sum(ah)-geff)
        return dict(time=float(t),E=E,Ebase=base,Emem=mem,Tq=Tq,Th=Th,cumulative_dissipation=float(s['diss'][0]),
                    Dmem=Dmem,Dq=Dq,Dh=Dh,Dtotal=Dmem+Dq+Dh,
                    residual_amplitude=amp,radius=rad,eff_charge=geff,
                    source_balance=source_balance,max_mismatch=yabs,
                    max_memory_tangent_modulus=incmod,max_h=float(max(abs(s['h']))))
    def audit_gradient(self,y):
        rng=np.random.default_rng(20261122)
        s=self.unpack(y)
        E,gF,gH,_,_,_=self.potential(s['F'],s['h'],s['zr'],s['zt'],gradient=True)
        err=[]
        for name,grad in [('F',gF),('h',gH)]:
            for j in rng.choice(len(grad),size=min(7,len(grad)),replace=False):
                v=y.copy();v[self.slices[name].start+j]+=1e-6
                w=y.copy();w[self.slices[name].start+j]-=1e-6
                gradfd=(self.energy(v)[0]-self.energy(w)[0])/2e-6
                err.append(abs(gradfd-grad[j])/max(1e-2,abs(gradfd),abs(grad[j])))
        return max(err)
    def audit_power(self,y):
        vec=self.rhs(0,y);eps=1e-5
        Ep=self.energy(y+eps*vec)[0]
        Em=self.energy(y-eps*vec)[0]
        Dsum=sum(self.dissipation(y))
        return abs((Ep-Em)/(2*eps)+Dsum)/max(.01,Dsum)


def run_one(p,tag):
    ev=Evolution(p)
    y0,F0,h0=ev.init()
    print(tag,'gradient-error',ev.audit_gradient(y0),'power-error',ev.audit_power(y0),flush=True)
    assert ev.audit_gradient(y0)<4e-5
    assert ev.audit_power(y0)<3e-5
    t_eval=np.linspace(0,p.t_final,161)
    sol=solve_ivp(ev.rhs,(0,p.t_final),y0,t_eval=t_eval,method='DOP853',rtol=2e-7,atol=1e-9,max_step=.025)
    if not sol.success:raise RuntimeError(sol.message)
    rows=[ev.observable(t,sol.y[:,j],F0) for j,t in enumerate(sol.t)]
    Es=np.array([row['E'] for row in rows]);D=np.array([row['Dtotal'] for row in rows])
    num_dE=np.diff(Es)
    nonmono=float(max(0,np.max(num_dE)))
    dissipated=rows[-1]['cumulative_dissipation']
    balance_error=float(abs(Es[0]-Es[-1]-dissipated))
    print(tag,'nfev',sol.nfev,'E0,Eend',Es[0],Es[-1],'nonmono',nonmono,'energy_balance',balance_error,
          'relative',balance_error/(Es[0]-Es[-1]),'radius0,end',rows[0]['radius'],rows[-1]['radius'],
          'amp0,end',rows[0]['residual_amplitude'],rows[-1]['residual_amplitude'],flush=True)
    assert nonmono < 2e-5
    assert balance_error < max(0.003,0.008*abs(Es[0]-Es[-1]))
    for j in [0,len(sol.t)//2,len(sol.t)-1]:
        assert ev.audit_power(sol.y[:,j])<3e-5,(tag,j,ev.audit_power(sol.y[:,j]))
    with (OUT/f'{tag}_timeseries.csv').open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=list(rows[0]));writer.writeheader();writer.writerows(rows)
    return ev,sol,rows,dict(tag=tag,dr=p.dr,tau=p.tau,k=p.k,eta=p.eta,
          nfev=sol.nfev,energy_initial=Es[0],energy_final=Es[-1],
          dissipated=dissipated,energy_balance_error=balance_error,energy_nonmonotonic_max=nonmono,
          max_grad_error=ev.audit_gradient(y0),power_error_initial=ev.audit_power(y0),
          final_radius=rows[-1]['radius'],initial_radius=rows[0]['radius'],
          final_amplitude=rows[-1]['residual_amplitude'],initial_amplitude=rows[0]['residual_amplitude'],
          initial_tangent_modulus=rows[0]['max_memory_tangent_modulus'],
          max_tangent_modulus=max(row['max_memory_tangent_modulus'] for row in rows),
          effective_charge_final=rows[-1]['eff_charge'])


def plots(output):
    colors=None
    fig,ax=plt.subplots(figsize=(8.7,5.1))
    for name,rows in output.items():
        if name.startswith('fine'):continue
        ax.plot([r['time'] for r in rows],[r['residual_amplitude'] for r in rows],label=name)
    ax.set(xlabel='Time (model units)',ylabel='RMS profile displacement',title='Dynamical recovery after a local deformation')
    ax.legend(fontsize=9);ax.grid(alpha=.2);fig.tight_layout();fig.savefig(OUT/'defect_recovery.png',dpi=160);plt.close(fig)
    fig,ax=plt.subplots(figsize=(8.7,5.1))
    Eref=Radial(L=16.,dr=.16,alpha=.25).optimize(maxiter=2500).fun
    for name,rows in output.items():
        if name.startswith('fine'):continue
        ax.plot([r['time'] for r in rows],[r['E']-Eref for r in rows],label=name)
    ax.set(xlabel='Time (model units)',ylabel='Energy above static reference',yscale='log',
           title='Dissipation of excess energy (kinetic + elastic + memory)')
    ax.legend(fontsize=9);ax.grid(alpha=.2);fig.tight_layout();fig.savefig(OUT/'energy_decay.png',dpi=160);plt.close(fig)
    # Frequency-dependent storage modulus from analytic solution of tau dz/dt=e-z.
    x=np.logspace(-2,2,200)
    fig,ax=plt.subplots(figsize=(8.7,5.1))
    ax.plot(x,x*x/(1+x*x),label="Storage modulus G'/k",lw=2)
    ax.plot(x,x/(1+x*x),label="Loss modulus G''/k",lw=2)
    ax.set(xscale='log',xlabel='Dimensionless frequency ωτ',ylabel='Modulus / k',ylim=(0,1.05),
           title='Retarded strain produces frequency-dependent stiffness and loss')
    ax.legend();ax.grid(alpha=.2);fig.tight_layout();fig.savefig(OUT/'frequency_response.png',dpi=160);plt.close(fig)


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--quick',action='store_true')
    args=parser.parse_args()
    if args.quick:
        cases=[('none',Params(dr=.16,k=0,eta=0,t_final=3)),('delay_nonlinear',Params(dr=.16,tau=1,k=.9,eta=20,t_final=3))]
    else:
        cases=[('no_memory',Params(k=0,eta=0,tau=1)),
               ('fast_memory',Params(k=.9,eta=20,tau=.08)),
               ('delayed_memory',Params(k=.9,eta=20,tau=1.2)),
               ('slow_memory',Params(k=.9,eta=20,tau=4.0)),
               ('linear_memory',Params(k=.9,eta=0,tau=1.2)),
               ('fine_delayed',Params(dr=.08,k=.9,eta=20,tau=1.2))]
    rows={};summary=[]
    for name,p in cases:
        ev,sol,res,r=run_one(p,name)
        rows[name]=res;summary.append(r)
    with (OUT/'dynamics_summary.csv').open('w',newline='') as f:
        wr=csv.DictWriter(f,fieldnames=list(summary[0]));wr.writeheader();wr.writerows(summary)
    plots(rows)
    print('ALL TESTS PASSED',flush=True)
if __name__=='__main__':main()
