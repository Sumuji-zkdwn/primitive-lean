#!/usr/bin/env python3
"""Radially optimized 3D Skyrme defect plus bounded scalar deformation.

Positive static energy density:
    (1-g*h+0.5*g*g*h*h)*rho2(q)+rho4(q)+0.5*K*|grad h|^2
The static scalar h solves a radial SPD finite-volume equation.
Only radial variations are optimized: this is not a full 3D PDE stability proof.
"""
from __future__ import annotations
import csv
import math
from pathlib import Path
import numpy as np
from scipy.optimize import minimize
from scipy.linalg import solve_banded
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

OUT=Path(__file__).resolve().parent
PI=np.pi

class Radial:
    def __init__(self, L=16., dr=.08, alpha=.25):
        self.n=int(round(L/dr)); self.L=self.n*dr;self.dr=dr;self.alpha=alpha
        self.g=math.sqrt(alpha);self.K=1.
        self.r=(np.arange(self.n)+.5)*dr
        self.w=4*PI*self.r**2*dr
        # K∫ |grad h|^2 from finite volume radial fluxes, continued to h~C/r beyond last cell.
        face=4*PI*self.K*(np.arange(1,self.n)*dr)**2/dr
        self.diag=np.zeros(self.n)
        self.diag[:-1]+=face
        self.diag[1:]+=face
        self.diag[-1]+=4*PI*self.K*self.r[-1]  # exterior harmonic potential from last cell
        self.sub=-face
    def init(self,R=1.):
        rn=np.arange(self.n+1)*self.dr
        F=2*np.arctan((R/np.maximum(rn,1e-12))**2)
        F[0]=PI;F[-1]=0.
        return F[1:-1]
    def evaluate(self,x,gradient=True,details=False):
        F=np.r_[PI,x,0.]
        fm=(F[1:]+F[:-1])/2
        df=np.diff(F)/self.dr
        s=np.sin(fm);c=np.cos(fm)
        r=self.r;w=self.w
        rho2=0.5*df**2+s**2/r**2
        rho4=s**2*df**2/r**2+0.5*s**4/r**4
        mass=w*rho2
        # Static radial h, variation of the (discrete) positive-definite energy.
        ab=np.zeros((3,self.n))
        ab[1,:]=self.diag +self.g**2*mass
        ab[0,1:]=self.sub
        ab[2,:-1]=self.sub
        h=solve_banded((1,1),ab,self.g*mass,check_finite=False)
        v=self.g*h
        stiffness=1-v+.5*v*v  # Always >= 1/2 (pointwise, even outside current solution)
        E2=float(np.sum(mass));E4=float(np.dot(w,rho4))
        energy=E2+E4-.5*self.g*float(np.dot(mass,h))
        if details:
            # cubic baryon-density integration exact using antiderivative of sin^2F dF,
            # not the midpoint approximation in the energy integral.
            def primitive(f):return f/2-np.sin(2*f)/4
            degree= -2/PI*(primitive(F[-1])-primitive(F[0]))
            gradient_inf_norm=np.linalg.norm(self.evaluate(x)[1],np.inf)
            return dict(r=r,Fmid=fm,rho2=rho2,rho4=rho4,h=h,
                        energy=energy,E2=E2,E4=E4,
                        scalar_reduction=.5*self.g*np.dot(mass,h),
                        effective_charge=self.g*float(np.dot(mass,1-v)),
                        source_mass=E2,
                        stiffness_min=float(np.min(stiffness)),
                        gh_max=float(max(v)),degree=degree,
                        gradient_inf_norm=float(gradient_inf_norm))
        if not gradient:return energy
        dEdDf=w*(stiffness*df+2*s**2*df/r**2)
        dEdFm=w*(stiffness*2*s*c/r**2+2*s*c*df**2/r**2+2*s**3*c/r**4)
        gr=np.zeros(self.n+1)
        gr[:-1]+=-dEdDf/self.dr+.5*dEdFm
        gr[1:]+=dEdDf/self.dr+.5*dEdFm
        return energy,gr[1:-1]
    def optimize(self,seed=None,maxiter=6000):
        initial=self.init() if seed is None else seed
        return minimize(self.evaluate,initial,jac=True,method='L-BFGS-B',
                        options={'maxiter':maxiter,'gtol':1e-7,'ftol':2e-13,'maxls':40})


def main():
    results=[]; profiles={}
    for alpha in (0.,.25):
        coarse=Radial(L=16.,dr=.12,alpha=alpha)
        x0=coarse.init()
        # finite difference check: compare envelope gradient to h elimination numerically
        _,grad=coarse.evaluate(x0)
        indices=np.random.default_rng(123).choice(len(x0),size=12,replace=False)
        err=[]
        for i in indices:
            h=1e-6
            xp=x0.copy();xm=x0.copy();xp[i]+=h;xm[i]-=h
            fd=(coarse.evaluate(xp,gradient=False)-coarse.evaluate(xm,gradient=False))/(2*h)
            err.append(abs(fd-grad[i])/max(0.01,abs(fd),abs(grad[i])))
        assert max(err)<1e-5,max(err)
        old_nodes=np.arange(coarse.n+1)*coarse.dr
        seed=x0
        for dx in (.12,.08):
            model=Radial(L=16.,dr=dx,alpha=alpha)
            new_nodes=np.arange(model.n+1)*dx
            if dx!=.12:
                seed=np.interp(new_nodes[1:-1],old_nodes,np.r_[PI,previous_result.x,0.])
            res=model.optimize(seed)
            d=model.evaluate(res.x,details=True)
            data={k:d[k] for k in ('energy','E2','E4','scalar_reduction','effective_charge','source_mass','stiffness_min','gh_max','degree','gradient_inf_norm')}
            row={'alpha':alpha,'dr':dx,'N':model.n,'converged':res.success,'iterations':res.nit,
                 'initial_energy':model.evaluate(seed,gradient=False),**data}
            results.append(row)
            profiles[(alpha,dx)]=d
            print(row,flush=True)
            if d['gradient_inf_norm']>.007:
                raise RuntimeError(f'large residual alpha={alpha} dr={dx}: {d["gradient_inf_norm"]}')
            previous_result=res
            old_nodes=new_nodes
        d=profiles[(alpha,.08)]
        with open(OUT/f'positive_profile_alpha_{str(alpha).replace(".","p")}.csv','w',newline='') as f:
            w=csv.writer(f);w.writerow(['radius','F','rho2','rho4','h'])
            for i in range(len(d['r'])):
                w.writerow([d[k][i] for k in ('r','Fmid','rho2','rho4','h')])
    with open(OUT/'positive_radial_results.csv','w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(results[0]));w.writeheader();w.writerows(results)
    fig,ax=plt.subplots(figsize=(8.7,5.2))
    for alpha in (0.,.25):
        d=profiles[(alpha,.08)]
        mask=d['r']<6
        ax.plot(d['r'][mask],d['Fmid'][mask],label=f'alpha={alpha}',lw=2)
    ax.set(xlabel='Radius',ylabel='Orientation F(r)',title='Radially optimized Skyrme defect with a positive-energy scalar coupling')
    ax.legend();ax.grid(alpha=.25);fig.tight_layout();fig.savefig(OUT/'positive_radial_profiles.png',dpi=160);plt.close(fig)
    fig,ax=plt.subplots(figsize=(8.7,5.2))
    d=profiles[(.25,.08)];mask=d['r']<7
    ax.plot(d['r'][mask],d['rho2'][mask]/np.max(d['rho2']),label='Deformation source density (normalized)')
    ax.plot(d['r'][mask],d['h'][mask]/np.max(d['h']),label='Massless field response (normalized)')
    ax.set(xlabel='Radius',ylabel='Relative magnitude',title='A localized deformation sources a spatially extended field')
    ax.legend();ax.grid(alpha=.25);fig.tight_layout();fig.savefig(OUT/'positive_source_and_field.png',dpi=160);plt.close(fig)

if __name__=='__main__': main()
