#!/usr/bin/env python3
"""Independent audits for v17: fixed-background Hamiltonian gradients and
independent integration of the Einstein radial constraints.
"""
import json
import numpy as np
from pathlib import Path
from scipy.integrate import solve_ivp
from scipy.interpolate import PchipInterpolator
from verify_v17 import Model, run, A_and_derivative, FOURPI

OUT=Path(__file__).resolve().parent


def fixed_metric_hamiltonian(model,y,metric):
    f,chi,pf,pc=model.unpack(y)
    F,C=model.full(f,chi)
    ri=model.ri; rm=model.rm;h=model.h
    lag=chi-np.cos(f)
    A,_=A_and_derivative(lag,model.delta,model.scale)
    Sigma=A+2*model.lam*np.sin(f)**2/ri**2
    mc=model.fac*ri**2*metric.a[1:-1]/metric.alpha[1:-1]
    kinetic=np.sum(pf*pf/(2*mc*Sigma)+pc*pc/(2*mc))
    fm=(F[:-1]+F[1:])/2;cm=(C[:-1]+C[1:])/2
    lagm=cm-np.cos(fm);Am,_=A_and_derivative(lagm,model.delta,model.scale)
    df=np.diff(F)/h;dc=np.diff(C)/h
    gw=.5*((metric.alpha/metric.a)[:-1]+(metric.alpha/metric.a)[1:])
    grad=model.fac*np.sum(gw*((.5*rm**2*Am+model.lam*np.sin(fm)**2)*df*df+.5*rm**2*dc*dc))
    pot=model.fac*np.sum((metric.alpha*metric.a)[1:-1]*(A*np.sin(f)**2+.5*model.lam*np.sin(f)**4/ri**2+
                                ri**2*(.5*model.kappa*lag**2+.5*model.mu**2*(chi-1)**2)))
    return float(kinetic+grad+pot)


def gradient_check(n=72,G=.0015,trials=15):
    model=Model(n=n,G=G)
    y=model.initial()
    rng=np.random.default_rng(401)
    y=y.copy()
    # perturb current state to ensure nonzero y and all nonlinear derivatives
    y[:model.k] +=.016*rng.normal(size=model.k)*np.exp(-((model.ri-2)/2)**2)
    y[model.k:2*model.k] +=.006*rng.normal(size=model.k)*np.exp(-((model.ri-2)/2)**2)
    metric=model.snapshot(y)
    deriv=model.derivative(0,y)
    base=fixed_metric_hamiltonian(model,y,metric)
    err=[]
    for i in range(trials):
        d=rng.normal(size=y.size)
        d/=np.linalg.norm(d)
        eps=3e-6
        num=(fixed_metric_hamiltonian(model,y+eps*d,metric)-fixed_metric_hamiltonian(model,y-eps*d,metric))/(2*eps)
        # E-L Hamiltonian vector field in ordering (f,chi,p_f,p_chi).
        k=model.k
        analytical=-(np.dot(deriv[2*k:3*k],d[:k])+np.dot(deriv[3*k:4*k],d[k:2*k])) +np.dot(deriv[:k],d[2*k:3*k])+np.dot(deriv[k:2*k],d[3*k:4*k])
        err.append(abs(analytical-num)/max(1,abs(analytical),abs(num)))
    return {'fixed_metric_hamiltonian_initial':base,'directional_gradient_max_relative':float(max(err)),
            'directional_gradient_median_relative':float(np.median(err)),
            'n_trials':trials,'G':G,'n':n}


def independent_constraint_solve(n=160):
    model=Model(n=n,G=.0012)
    y=model.initial()
    metric=model.snapshot(y)
    r=model.r
    b=8*np.pi*model.G*r*metric.K
    c=FOURPI*r*r*(metric.K+metric.W)
    ib=PchipInterpolator(r,b,extrapolate=False)
    ic=PchipInterpolator(r,c,extrapolate=False)
    def rhs(rr,Y):return [ic(rr)-ib(rr)*Y[0]]
    sol=solve_ivp(rhs,(0,model.R),[0],rtol=2e-12,atol=2e-13,t_eval=r,method='DOP853')
    if not sol.success:raise RuntimeError(sol.message)
    m_ind=sol.y[0]
    # As n doubles, the existing trapezoid quadrature should converge to the
    # ODE integration at O(h^2).
    return {'G':model.G,'n':n,
        'source_quadrature_vs_independent_ode_absolute_at_R':float(abs(m_ind[-1]-metric.m[-1])),
        'source_quadrature_vs_independent_ode_relative_at_R':float(abs(m_ind[-1]-metric.m[-1])/m_ind[-1]),
        'metric_positive':bool((metric.a>0).all() and (metric.alpha>0).all()),
        'radial_hamiltonian_relative_residual':float(model.snapshot(y,audit=True).radial_ham_rms)}


def frozen_metric_control(n=128,G=.002,T=.9):
    from scipy.integrate import solve_ivp
    model=Model(n=n,G=G)
    y0=model.initial()
    fixed=model.snapshot(y0)
    # External metric prescribed to be equal to the initial self-consistent solution.
    original=model.snapshot
    model.snapshot=lambda y,audit=False: fixed
    sol=solve_ivp(model.derivative,(0,T),y0,method='DOP853',rtol=1e-10,atol=2e-12,t_eval=[T])
    model.snapshot=original
    if not sol.success:raise RuntimeError(sol.message)
    _,dynamic,_,dynamic_summary=run(n=n,G=G,T=T,dt=.015,rtol=1e-10,atol=2e-12)
    yd=dynamic.y[:,-1]; yf=sol.y[:,-1]
    k=model.k
    err_f=float(np.sqrt(np.mean((yd[:k]-yf[:k])**2)))
    err_chi=float(np.sqrt(np.mean((yd[k:2*k]-yf[k:2*k])**2)))
    amp_f=float(np.sqrt(np.mean((yd[:k]-y0[:k])**2)))
    return {'n':n,'G':G,'T':T,
            'same_initial_matter_canonical_data':True,
            'dynamic_vs_frozen_metric_f_RMS':err_f,
            'dynamic_vs_frozen_metric_chi_RMS':err_chi,
            'dynamic_f_change_RMS':amp_f,
            'relative_f_difference_to_dynamic_change':err_f/amp_f,
            'dynamic_metric_center_lapse_change':dynamic_summary['center_lapse_change'],
            'note':'This checks backreaction beyond propagation in a fixed initial gravitational metric.'}


def flat_energy_check():
    model,sol,diagnostics,_=run(n=128,G=0.,T=.9,dt=.015,rtol=1e-10,atol=1e-12)
    fixed=model.snapshot(sol.y[:,0])
    energies=np.array([fixed_metric_hamiltonian(model,sol.y[:,j],fixed) for j in range(sol.y.shape[1])])
    return {'n':128,'T':.9,'energy_initial':float(energies[0]),
            'max_relative_matter_hamiltonian_drift':float(np.max(np.abs(energies-energies[0]))/energies[0])}


def run_all():
    grad=gradient_check()
    quad=[independent_constraint_solve(n) for n in (80,160,320)]
    frozen=frozen_metric_control()
    answer={'fixed_metric_variation':grad,'radial_ode_quadrature_cross_check':quad,'time_varying_metric_vs_fixed_metric':frozen,'flat_space_hamiltonian_conservation':flat_energy_check()}
    (OUT/'independent_audit.json').write_text(json.dumps(answer,indent=2,ensure_ascii=False)+'\n')
    print(json.dumps(answer,indent=2))
    assert grad['directional_gradient_max_relative']<1e-7,grad
    assert quad[-1]['source_quadrature_vs_independent_ode_relative_at_R'] <quad[-2]['source_quadrature_vs_independent_ode_relative_at_R']/3,quad
    assert frozen['relative_f_difference_to_dynamic_change']>0.001,frozen
    assert answer['flat_space_hamiltonian_conservation']['max_relative_matter_hamiltonian_drift']<1e-9, answer
    return answer

if __name__=='__main__':run_all()
