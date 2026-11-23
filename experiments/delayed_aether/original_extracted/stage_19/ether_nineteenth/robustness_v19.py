#!/usr/bin/env python3
"""v19 robustness: multistart equilibrium, resolution continuation, richer l=2 subspaces."""
import csv,json
from pathlib import Path
import numpy as np
from scipy.optimize import minimize
from scipy.interpolate import PchipInterpolator
from verify_v19 import Radial,projected_matrices,background,R0,W,R,taper_start
OUT=Path(__file__).resolve().parent

def run_opt(model,x0):
    return minimize(model.energy_grad,x0,method='L-BFGS-B',jac=True,
        bounds=[(0,np.pi)]*(model.n-1)+[(-1.5,1.5)]*(model.n-1),
        options={'maxiter':8000,'maxfun':18000,'gtol':1e-8,'ftol':4e-15,'maxls':60,'maxcor':30})

def initial_scales(model,scale):
    r=model.r
    amp=R0*scale*np.exp(-r*r/(2*(W*scale)**2))
    f=2*np.arctan2(amp,r)
    u=np.clip((r-9)/(12-9),0,1)
    taper=1-10*u**3+15*u**4-6*u**5
    f=f*taper;f[0]=np.pi;f[-1]=0
    chi=np.cos(f);chi[0]=chi[1];chi[-1]=1
    return model.pack(f,chi)

def main():
    model=Radial(120)
    start=[]
    for scale in [.55,.8,1.,1.3,1.8,2.4]:
        x0=initial_scales(model,scale)
        res=run_opt(model,x0)
        entry={'scale':scale,'initial_energy':float(model.energy_grad(x0)[0]),
               'final_energy':float(res.fun),'iterations':int(res.nit),
               'optimizer_success':bool(res.success),'gradmax':float(np.max(abs(res.jac)))}
        start.append(entry)
        print('start',entry,flush=True)
    ref=np.genfromtxt(OUT/'radial_profile_n180.csv',delimiter=',',names=True)
    refs=PchipInterpolator(ref['r'],ref['f']);refc=PchipInterpolator(ref['r'],ref['chi'])
    converge=[]
    for n in [240,320]:
        model=Radial(n)
        f=refs(model.r);chi=refc(model.r)
        f[0]=np.pi;f[-1]=0;chi[0]=chi[1];chi[-1]=1
        x0=model.pack(f,chi)
        res=run_opt(model,x0)
        ff,cc=model.unpack(res.x)
        entry={'n':n,'h':model.h,'energy':float(res.fun),'components':list(map(float,model.energy_grad(res.x,True))),
               'optimizer_success':bool(res.success),'iterations':int(res.nit),'gradmax':float(np.max(abs(res.jac))),
               'f_at_r1':float(np.interp(1,model.r,ff)), 'max_memory_lag':float(np.max(abs(cc-np.cos(ff))))}
        print('refine',entry,flush=True)
        converge.append(entry)
        with (OUT/f'radial_profile_n{n}.csv').open('w',newline='') as file:
            w=csv.writer(file);w.writerow(['r','f','chi','cos_f','lag']);w.writerows(np.c_[model.r,ff,cc,np.cos(ff),cc-np.cos(ff)])
        refs=PchipInterpolator(model.r,ff);refc=PchipInterpolator(model.r,cc)
    m=Radial(320)
    dat=np.genfromtxt(OUT/'radial_profile_n320.csv',delimiter=',',names=True)
    sf=PchipInterpolator(m.r,dat['f']);sc=PchipInterpolator(m.r,dat['chi'])
    r=np.linspace(1e-4,12.,2401)
    families={
       'original_8':(.6,.95,1.4,2.,2.9,4.1,5.8,8.2),
       'expanded_10':(.38,.55,.8,1.15,1.6,2.2,3.,4.2,5.8,8.2),
       'broad_10':(.5,.7,1.0,1.45,2.,2.8,3.9,5.4,7.4,10.)
    }
    modes=[]
    for label,widths in families.items():
        for l in [2,3]:
            K,M,ew,_=projected_matrices(r,sf,sc,l=l,widths=widths)
            entry={'family':label,'l':l,'dim':len(ew),'minimum_omega_squared':float(ew[0]),
                 'second_omega_squared':float(ew[1]),'min_kinetic_eig':float(np.min(np.linalg.eigvalsh(M)))}
            print('basis',entry,flush=True)
            modes.append(entry)
    allout={'multistart':start,'continuation':converge,'basis_stress':modes}
    (OUT/'robustness_v19.json').write_text(json.dumps(allout,indent=2))

if __name__=='__main__':main()
