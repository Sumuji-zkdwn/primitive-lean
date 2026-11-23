#!/usr/bin/env python3
"""Dynamic test of a bounded but nonlinearly stiffening memory term.

Psi(y) = (k+Delta)y^2/2 - Delta*a^2 log cosh(y/a).
Psi''(y) = k+Delta tanh(y/a)^2, hence k <= Psi'' <= k+Delta.
This bounds *the memory tangent modulus only*, not the entire Skyrme
field's characteristic speed on strong backgrounds.
"""
from pathlib import Path
import csv
import numpy as np
from scipy.integrate import solve_ivp
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from delayed_hardening_dynamics import Evolution, Params, run_one
P=Path(__file__).resolve().parent
PI=np.pi

DELTA=6.0;TRANSITION=.05

def logcosh(x):return np.logaddexp(x,-x)-np.log(2.)

def psi(y,k,Delta=DELTA,a=TRANSITION):return (k+Delta)*y*y/2-Delta*a*a*logcosh(y/a)
def stress(y,k,Delta=DELTA,a=TRANSITION):return (k+Delta)*y-Delta*a*np.tanh(y/a)
def tangent(y,k,Delta=DELTA,a=TRANSITION):return k+Delta*np.tanh(y/a)**2

class BoundedEvolution(Evolution):
    def potential(self,x,h,zr,zt,gradient=False):
        p=self.p;m=self.model;dr=m.dr;r=self.r;w=self.w
        df,st,fm=self.strain(x)
        ss=np.sin(fm);cc=np.cos(fm)
        rho2=.5*df*df+st*st
        rho4=st*st*df*df+.5*st**4
        v=m.g*h; cf=1-v+.5*v*v
        yr=df-zr;yt=st-zt
        mem=psi(yr,p.k)+2*psi(yt,p.k)
        Ah=self.field_A(h)
        Ebase=float(np.dot(w,cf*rho2+rho4)+.5*np.dot(h,Ah))
        Emem=float(np.dot(w,mem))
        if not gradient:return Ebase+Emem,Ebase,Emem
        sr=stress(yr,p.k);stt=stress(yt,p.k)
        dEddf=w*(cf*df+2*st*st*df+sr)
        dEdfm=w*(cf*2*st*cc/r+2*st*cc*df*df/r+2*st**3*cc/r+2*stt*cc/r)
        gradnodes=np.zeros(self.n+1)
        gradnodes[:-1]+=-dEddf/dr+.5*dEdfm
        gradnodes[1:]+=dEddf/dr+.5*dEdfm
        gradF=gradnodes[1:-1]
        gradH=w*m.g*(v-1)*rho2+Ah
        loss_mem=float(np.dot(w,(sr*yr+2*stt*yt))/p.tau)
        return Ebase+Emem,gradF,gradH,loss_mem,Ebase,Emem
    def observable(self,t,y,F0):
        row=super().observable(t,y,F0)
        row['max_memory_tangent_modulus']=float(tangent(row['max_mismatch'],self.p.k))
        return row


def bounded_run(p,tag):
    ev=BoundedEvolution(p);y0,F0,h0=ev.init(quiet=True)
    grad_err=ev.audit_gradient(y0);power_err=ev.audit_power(y0)
    assert grad_err<4e-5 and power_err<3e-5,(grad_err,power_err)
    t_eval=np.linspace(0,p.t_final,161)
    result=solve_ivp(ev.rhs,(0,p.t_final),y0,t_eval=t_eval,method='DOP853',rtol=2e-7,atol=1e-9,max_step=.025)
    assert result.success,result.message
    rows=[ev.observable(t,result.y[:,j],F0) for j,t in enumerate(result.t)]
    energies=np.array([r['E'] for r in rows]);diss=np.array([r['cumulative_dissipation'] for r in rows])
    balance=float(np.max(np.abs(energies+diss-energies[0])))
    max_increment=float(np.max(np.diff(energies)))
    assert max_increment<2e-5 and balance<.003,(max_increment,balance)
    assert max(r['max_memory_tangent_modulus'] for r in rows) <= p.k+DELTA+1e-11
    for j in [0,len(t_eval)//2,len(t_eval)-1]: assert ev.audit_power(result.y[:,j])<3e-5
    with (P/f'{tag}_timeseries.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
    return rows,dict(tag=tag,gradient_rel_error=grad_err,power_rel_error=power_err,
                     energy_initial=energies[0],energy_final=energies[-1],energy_balance_max_abs=balance,
                     positive_energy_step_max=max(0,max_increment),initial_profile_deviation=rows[0]['residual_amplitude'],
                     final_profile_deviation=rows[-1]['residual_amplitude'],
                     max_extra_modulus=max(row['max_memory_tangent_modulus'] for row in rows))

def main():
    p=Params(dr=.16,tau=1.2,k=.9,eta=20.0,gamma_q=.25,gamma_h=.4,
             mass_q=1.9,mass_h=1.,alpha=.25,t_final=8.,amplitude=.19)
    _,_,rquartic,squartic=run_one(p,'quartic_tuned')
    rbounded,sbounded=bounded_run(p,'bounded_memory_tuned')
    qsummary=dict(tag='quartic_tuned',energy_initial=squartic['energy_initial'],energy_final=squartic['energy_final'],
                  energy_balance_max_abs=squartic['energy_balance_error'],
                  positive_energy_step_max=squartic['energy_nonmonotonic_max'],
                  initial_profile_deviation=squartic['initial_amplitude'],final_profile_deviation=squartic['final_amplitude'],
                  max_extra_modulus=squartic['max_tangent_modulus'],gradient_rel_error=squartic['max_grad_error'],power_rel_error=squartic['power_error_initial'])
    summary=[qsummary,sbounded]
    with (P/'saturated_dynamics_summary.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(qsummary));w.writeheader();w.writerows(summary)
    fig,axs=plt.subplots(2,1,figsize=(9,7.6),sharex=True)
    for name,rows in [('Unbounded quartic',rquartic),('Bounded hardening',rbounded)]:
        tt=[r['time'] for r in rows]
        axs[0].plot(tt,[r['residual_amplitude'] for r in rows],label=name)
        axs[1].plot(tt,[r['max_memory_tangent_modulus'] for r in rows],label=name)
    axs[0].set(ylabel='RMS profile perturbation',title='Bounded-hardening dynamic test (radial time evolution only)')
    axs[1].set(xlabel='Time',ylabel='Peak memory tangent modulus')
    for ax in axs:ax.grid(alpha=.22);ax.legend()
    fig.tight_layout();fig.savefig(P/'bounded_memory_time_evolution.png',dpi=165);plt.close(fig)
    Y=np.linspace(-.5,.5,1001)
    fig,ax=plt.subplots(figsize=(8.8,5.1))
    ax.plot(Y,p.k+3*p.eta*Y*Y,label='Old quartic memory modulus')
    ax.plot(Y,tangent(Y,p.k),label='New saturated memory modulus')
    ax.axhline(p.k+DELTA,color='black',ls='--',lw=1,label='Hardening cap')
    ax.set(xlabel='Memory mismatch y',ylabel='Local additional tangent modulus',title='Saturating memory removes one unbounded stiffness channel')
    ax.legend();ax.grid(alpha=.2);fig.tight_layout();fig.savefig(P/'bounded_memory_modulus.png',dpi=165);plt.close(fig)
    print('SUMMARY')
    for d in summary:print(d)

if __name__=='__main__':main()
