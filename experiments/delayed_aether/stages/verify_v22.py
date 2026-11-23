#!/usr/bin/env python3
"""V22: exactly constrained Bianchi-I Noether bootstrap, memory coupling & numerical test.

Restricted homogeneous test, NOT a derivation of full 3+1 Einstein gravity
or emergence of spin-2 from a medium. Python 3 with sympy/numpy/scipy/matplotlib.
"""
from __future__ import annotations
import csv, hashlib, json, math
from pathlib import Path

import numpy as np
import sympy as sp
from scipy.integrate import solve_ivp
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parent


def exact_checks():
    vs = sp.symbols('v1 v2 v3', real=True)
    aa = sp.symbols('a1 a2 a3', real=True)
    S, Sd, n, nd, xi, xid, coeff, beta = sp.symbols('S Sd n nd xi xid coeff beta', real=True)
    vv = sum(vs)
    Q = sum(v**2 for v in vs) - vv**2
    Qdot = sum(sp.diff(Q, v)*a for v, a in zip(vs, aa))
    # Delta_1 under nonlinear time diffeomorphism beta_i -> xi beta_i' .
    delta1_L2 = xi*Qdot + 2*xid*Q
    generic_L3 = (coeff*S + beta*n)*Q
    delta0_L3 = sp.diff(generic_L3, n)*xid
    desired_L2 = xi*Qdot+xid*Q
    defect_generic = sp.factor(delta1_L2+delta0_L3-desired_L2)
    assert sp.simplify(defect_generic-(beta+1)*xid*Q) == 0
    assert sp.solve(sp.Eq(beta+1, 0), beta) == [-1]

    # Fourth-order Noether equation: nonlinear xi transformation and quadratic action.
    L3 = (coeff*S-n)*Q
    L4 = (coeff**2*S**2/sp.Integer(2)-coeff*S*n+n**2)*Q
    d1_L3 = (coeff*xi*Sd-(xi*nd+n*xid))*Q + (coeff*S-n)*(xi*Qdot+2*xid*Q)
    d0_L4 = sp.diff(L4, n)*xid
    dtotal_xi_L3 = xid*L3+xi*((coeff*Sd-nd)*Q+(coeff*S-n)*Qdot)
    quartic_residual=sp.factor(d1_L3+d0_L4-dtotal_xi_L3)
    assert quartic_residual == 0

    # Arbitrary e^(coeff*S) prefactor is TIME reparam invariant, so coeff isn't fixed.
    N, V, K, expS = sp.symbols('N V K expS', positive=True)
    L = expS*((Q+K)/N-N*V)
    # Euler weighted homogeneity under time changes: 2*velocity-kinetic + N*dL/dN == L.
    covariance_identity = sp.factor(2*expS*(Q+K)/N+N*sp.diff(L,N)-L)
    assert covariance_identity == 0
    Lbad = expS*(Q/N + K-N*V)
    bad_covariance=sp.simplify((2*expS*(Q/N+K)+N*sp.diff(Lbad,N))-Lbad)
    assert sp.simplify(bad_covariance-expS*K)==0

    # Explicit counterexample: adding an arbitrary lapse-covariant spatial-volume multiplier.
    cfree=sp.symbols('c_free')
    Lfamily=sp.exp(cfree*S)*Q/N
    family_identity=sp.simplify(2*Lfamily+N*sp.diff(Lfamily,N)-Lfamily)
    assert family_identity==0

    return {
        'cubic_noether_defect': str(defect_generic),
        'required_lapse_cubic_coefficient': -1,
        'volume_cubic_coefficient_fixed_by_time_diff': False,
        'quartic_noether_defect': str(quartic_residual),
        'exact_lapse_covariance_identity': str(covariance_identity),
        'wrong_kinetic_memory_noether_defect': str(bad_covariance),
        'arbitrary_volume_prefactor_time_invariant': True,
        'gravitational_kinetic_Q': str(sp.expand(Q)),
    }


def model_parameters():
    return {'Delta':3.0, 'width':0.45, 'mu':1.2}


def stiffness(y, pars):
    t = np.tanh(y/pars['width'])
    A = 1+pars['Delta']*t*t
    Ap = 2*pars['Delta']/pars['width'] * t * (1-t*t)
    return A, Ap


def quantities(w, pars):
    b=w[:3]; q,z=w[3:5]; v=w[5:8]; u,r=w[8:10]
    S=np.sum(b)
    H=np.sum(v)
    Q=np.dot(v,v)-H**2
    y=z-q
    A,Ap=stiffness(y,pars)
    K=.5*(A*u*u+r*r)
    V=.5*pars['mu']**2*y*y
    C=Q+K+V
    E_N=-np.exp(S)*C
    return {'S':S, 'H':H, 'Q':Q, 'y':y,'A':A,'Ap':Ap,'K':K,'V':V,
            'C':C, 'E_N':E_N,'shear':float(np.linalg.norm(v-H/3)),
            'scale':np.exp(S/3)}


def rhs(t,w,pars):
    b=w[:3]; q,z=w[3:5]; v=w[5:8]; u,r=w[8:10]
    data=quantities(w,pars)
    Sdot=data['H']; Q=data['Q']; K=data['K']; V=data['V']; y=data['y']; A=data['A']; Ap=data['Ap']
    F=Q+K-V
    target=.5*F-Sdot*(v-Sdot)
    # 2(a_i-sum_j a_j)= F - 2 Sdot(v_i-Sdot)
    avec=target-.5*sum(target)
    dy_dt=r-u
    dVdy=pars['mu']**2*y
    du=( -Sdot*A*u -Ap*dy_dt*u -.5*Ap*u*u +dVdy)/A
    dr= -Sdot*r +.5*Ap*u*u-dVdy
    return np.r_[v, u, r, avec, du, dr]


def integrate(pars):
    b0=np.zeros(3)
    q0,z0=.55,-.16
    u0,r0=.18,-.075
    y0=z0-q0
    A0,_=stiffness(y0,pars)
    matter_energy=.5*(A0*u0*u0 + r0*r0)+.5*pars['mu']**2*y0*y0
    anis=np.array([.048,-.032,-.016])
    H0=np.sqrt((float(anis@anis)+matter_energy)/6)
    vb0=H0+anis
    w0=np.r_[b0,q0,z0,vb0,u0,r0]
    assert abs(quantities(w0,pars)['C']) < 2e-15
    t_eval=np.linspace(0,7,701)
    sol=solve_ivp(lambda t,w: rhs(t,w,pars), (0,7), w0, method='DOP853',
                  atol=2e-12,rtol=2e-12,t_eval=t_eval)
    assert sol.success,sol.message
    data=[quantities(w,pars) for w in sol.y.T]
    C=np.array([d['C'] for d in data]); E=np.array([d['E_N'] for d in data])
    maxC=float(np.max(np.abs(C)))
    maxE=float(np.max(np.abs(E)))
    scale=float(np.max([abs(d['Q'])+d['K']+d['V'] for d in data]))
    normC=maxC/max(scale,1e-30)
    assert normC<2e-10, normC
    assert maxE<2e-9,maxE
    # Finite difference check for non-circular test: dot of lapse constraint is tiny.
    max_deriv=float(np.max(np.abs(np.gradient(E,t_eval))))
    assert max_deriv<2e-7,max_deriv
    cols=['time','beta1','beta2','beta3','q','z','vbeta1','vbeta2','vbeta3','vq','vz','A','relative_y','scale_factor','shear','constraint_C','lapse_EL_E_N','grav_Q','matter_K','potential_V']
    with (ROOT/'coupled_bianchiI_v22.csv').open('w',newline='') as f:
        writer=csv.writer(f);writer.writerow(cols)
        for t,w,d in zip(t_eval,sol.y.T,data):
            writer.writerow([float(t),*map(float,w[:10]),d['A'],d['y'],d['scale'],d['shear'],d['C'],d['E_N'],d['Q'],d['K'],d['V']])
    fig, axes=plt.subplots(3,1,figsize=(8,9),sharex=True)
    axes[0].plot(t_eval,[d['A'] for d in data],label='effective inertia A')
    axes[0].plot(t_eval,[d['y'] for d in data],label='memory-state offset z-q')
    axes[0].legend(); axes[0].set_ylabel('internal state')
    axes[1].plot(t_eval,[d['scale'] for d in data],label='volume scale exp(S/3)')
    axes[1].plot(t_eval,[d['shear'] for d in data],label='shear amplitude')
    axes[1].legend(); axes[1].set_ylabel('geometric evolution')
    axes[2].semilogy(t_eval,np.maximum(np.abs(C),1e-17),label='|Hamiltonian constraint|')
    axes[2].semilogy(t_eval,np.maximum(np.abs(E),1e-17),label='|lapse EL equation|')
    axes[2].legend();axes[2].set_ylabel('absolute residual');axes[2].set_xlabel('model time')
    fig.tight_layout(); fig.savefig(ROOT/'bianchiI_gauge_memory_v22.png',dpi=170);plt.close(fig)
    return {
        'n_steps':len(t_eval), 'initial_H':float(H0), 'initial_relative_y':float(y0),
        'A_initial':float(data[0]['A']), 'A_min':float(min(d['A'] for d in data)),
        'A_max':float(max(d['A'] for d in data)),
        'A_final':float(data[-1]['A']), 'shear_initial':float(data[0]['shear']),
        'shear_final':float(data[-1]['shear']), 'scale_final':float(data[-1]['scale']),
        'max_abs_hamiltonian_constraint':maxC, 'max_rel_constraint':normC,
        'max_abs_lapse_euler_equation':maxE, 'max_fd_lapse_euler_derivative':max_deriv,
        'final_q':float(sol.y[3,-1]), 'final_z':float(sol.y[4,-1]),
        'final_relative_y':float(data[-1]['y']),
    }


def dissipative_source_obstruction(pars):
    """Adding friction to z WITHOUT its bath stress tensor violates lapse constraint.

    Exact identity: d/dt(exp(S)*C)=-gamma*exp(S)*zdot**2.
    This is a deliberately inconsistent deformation, not an inevitable property
    of all covariant dissipative theories.
    """
    gamma=.65
    q0,z0=.55,-.16
    u0,r0=.18,-.075
    y0=z0-q0
    A0,_=stiffness(y0,pars)
    mat=.5*(A0*u0*u0+r0*r0)+.5*pars['mu']**2*y0*y0
    anis=np.array([.048,-.032,-.016])
    H0=np.sqrt((float(anis@anis)+mat)/6)
    w0=np.r_[np.zeros(3),q0,z0,H0+anis,u0,r0]
    t=np.linspace(0,7,701)
    def bad_rhs(time,w):
        result=rhs(time,w,pars)
        result[-1]-=gamma*w[-1]  # omit energy-momentum of the bath
        return result
    sol=solve_ivp(bad_rhs, (0,7),w0,method='DOP853',atol=2e-12,rtol=2e-12,t_eval=t)
    assert sol.success
    diags=[quantities(w,pars) for w in sol.y.T]
    E=np.array([d['E_N'] for d in diags])
    C=np.array([d['C'] for d in diags])
    src=gamma*np.array([np.exp(d['S']) for d in diags])*sol.y[-1]**2
    # integral of the missing bath energy, using cumulative trapezoid
    from scipy.integrate import cumulative_trapezoid
    predicted=cumulative_trapezoid(src,t,initial=0)
    discrepancy=float(max(abs(E-predicted)))
    assert discrepancy<2e-5, discrepancy
    with (ROOT/'inconsistent_friction_v22.csv').open('w',newline='') as f:
        writer=csv.writer(f);writer.writerow(['time','constraint_C','minus_expS_C','integrated_missing_source','source_rate'])
        for ti,ci,ei,pi,si in zip(t,C,E,predicted,src): writer.writerow([ti,ci,ei,pi,si])
    fig,ax=plt.subplots(figsize=(8,4.5))
    ax.plot(t,E,label='lapse-constraint violation: -exp(S) C')
    ax.plot(t,predicted,linestyle='--',label='integrated omitted bath source')
    ax.set_xlabel('model time');ax.set_ylabel('constraint violation')
    ax.legend();fig.tight_layout()
    fig.savefig(ROOT/'friction_constraint_failure_v22.png',dpi=170);plt.close(fig)
    return {'gamma':gamma,'final_abs_constraint':float(abs(C[-1])),
            'final_lapse_violation':float(E[-1]),
            'max_evolution_identity_discrepancy':discrepancy,
            'physical_interpretation':'Energy sink must be included in stress tensor to preserve gravitational constraint.'}


def reciprocal_example(pars):
    mu=pars['mu']
    frequency=np.sqrt(2)*mu
    t=np.linspace(0,4*np.pi/frequency,2001)
    q=(1+np.cos(frequency*t))/2
    z=(1-np.cos(frequency*t))/2
    qdot= -frequency*np.sin(frequency*t)/2
    zdot= +frequency*np.sin(frequency*t)/2
    E= .5*(qdot*qdot+zdot*zdot)+.5*mu**2*(q-z)**2
    return {'period':float(2*np.pi/frequency), 'energy':float(E[0]),
            'energy_relative_error':float(np.max(abs(E-E[0]))/E[0]),
            'return_error_after_two_periods':float(max(abs(q[-1]-q[0]),abs(z[-1]-z[0]))) }


def main():
    checks=exact_checks(); pars=model_parameters(); num=integrate(pars)
    oscillator=reciprocal_example(pars)
    bad_friction=dissipative_source_obstruction(pars)
    audit={'title':'v22 homogeneous nonlinear Noether & memory benchmark',
           'scope':'Homogeneous Bianchi I/0+1D only, not full spin2 bootstrap; GR ADM action is assumed',
           'parameters':pars,'exact_symbolic':checks,'dynamics':num,'reversible_memory':oscillator,'omitted_bath_friction':bad_friction,
           'all_assertions_passed':True}
    (ROOT/'audit_v22.json').write_text(json.dumps(audit,indent=2,ensure_ascii=False)+'\n')
    print(json.dumps(audit,indent=2,ensure_ascii=False))

if __name__=='__main__': main()