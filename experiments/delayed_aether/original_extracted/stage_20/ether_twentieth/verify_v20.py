#!/usr/bin/env python3
"""v20: conditional massless spin-2 uniqueness and universal coupling Ward test.
All results are explicit conditional model checks, NOT an emergence of GR.
"""
from pathlib import Path
import json, hashlib
import sympy as s
import numpy as np
from scipy.integrate import solve_ivp, trapezoid
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

OUT = Path(__file__).resolve().parent
eta = s.diag(-1, 1, 1, 1)
coeff = s.symbols('a b c d')

def euler_symbol(k, h, cs=coeff):
    """Symbol of the Euler operator for four Lorentz-invariant derivative terms.

    L = a (dh)^2 + b (div h)^2 + c div(h) dot grad(tr h)
        + d grad(tr h)^2, integrating by parts and ignoring common signs.
    """
    a,b,c,d = cs
    ku = eta*k
    k2 = (k.T*eta*k)[0]
    A = h*ku
    t = s.trace(eta*h)
    kA = (ku.T*A)[0]
    return 2*a*k2*h + b*(k*A.T + A*k.T) + c*(k*k.T*t + eta*kA) + 2*d*eta*k2*t

def components(M):
    return s.Matrix([M[i,j] for i in range(4) for j in range(i,4)])

def spin2_audit():
    eqs=[]
    for p in [(-1,0,0,1), (1,2,3,4), (2,0,-1,3)]:
        k=s.Matrix(p)
        for j in range(4):
            xi=s.eye(4).col(j)
            H=k*xi.T + xi*k.T
            eqs += list(components(euler_symbol(k,H)))
    mat,_=s.linear_eq_to_matrix(eqs,coeff)
    kernel=mat.nullspace()
    assert mat.rank()==3 and len(kernel)==1
    v=kernel[0]
    normalized=s.simplify(v/v[0])
    assert list(normalized)==[1,-2,2,-1],normalized

    # Universal (arbitrary 4-wavevector and gauge parameter) polynomial identity.
    k=s.Matrix(s.symbols('k0:4'))
    xi=s.Matrix(s.symbols('xi0:4'))
    h=k*xi.T + xi*k.T
    identity=euler_symbol(k,h,list(normalized))
    assert all(s.expand(v)==0 for v in components(identity))

    # Rank / gauge quotient: 10 components - rank(E) - rank(gauge) = 2 on light cone.
    slots=[(i,j) for i in range(4) for j in range(i,4)]
    def counts(p):
        k=s.Matrix(p)
        cols=[]
        for i,j in slots:
            H=s.zeros(4)
            H[i,j]=1
            H[j,i]=1
            cols.append(components(euler_symbol(k,H,list(normalized))))
        A=s.Matrix.hstack(*cols)
        gauges=[]
        for j in range(4):
            x=s.eye(4).col(j)
            gauges.append(components(k*x.T + x*k.T))
        G=s.Matrix.hstack(*gauges)
        assert A*G == s.zeros(10,4)
        return {'rank_of_euler_operator':A.rank(),'kernel_dimension':10-A.rank(),
                'rank_of_gauge':G.rank(),'kernel_mod_gauge':10-A.rank()-G.rank()}
    null=counts((-1,0,0,1))
    nonnull=counts((1,0,0,0))
    assert null=={'rank_of_euler_operator':4,'kernel_dimension':6,'rank_of_gauge':4,'kernel_mod_gauge':2}
    assert nonnull['kernel_mod_gauge']==0
    # Higher derivatives preserve gauge symmetry but introduce an extra dispersion root.
    # For ell²=1, P'(k)=(1+k²)P_FP(k), so a timelike k²=-1 makes P' identically zero.
    extra_k=s.Matrix((1,0,0,0))
    extra_factor=1+(extra_k.T*eta*extra_k)[0]
    assert extra_factor==0
    higher_derivative={'kinetic_symbol':'(1+ell²*k²)*P_FP(k)',
                       'on_pure_gauge':'zero for all k and ell², because P_FP(k)*gauge=0',
                       'TT_dispersion_polynomial':'k²*(1+ell²*k²)=0',
                       'additional_root_for_ell_squared_1':'k²=-1',
                       'additional_root_is_not_allowed_in_two_derivative_class':True,
                       'interpretation':'linear gauge invariance by itself does not exclude higher-derivative extra modes'}
    # Check mass terms cannot remain gauge invariant under same symmetry.
    a,b=s.symbols('mass_a mass_b')
    ke=s.Matrix((1,2,0,3))
    mass_eq=[]
    for j in range(4):
        x=s.eye(4).col(j)
        H=ke*x.T+x*ke.T
        massOp=2*a*H+2*b*eta*s.trace(eta*H)
        mass_eq+=list(components(massOp))
    Amm,_=s.linear_eq_to_matrix(mass_eq,[a,b])
    assert Amm.rank()==2
    return {'assumptions':'symmetric rank-2 field; flat Minkowski; parity-even Lorentz-invariant quadratic action with two derivatives; linear gauge δh=∂ξ+∂ξ',
            'derivative_invariants':4,'coefficient_equations_rank':mat.rank(),
            'unique_coefficients_up_to_scale':[int(v) for v in normalized],
            'exact_universal_polynomial_gauge_identity':True,
            'null_wave_vector':null,'non_null_wave_vector':nonnull,
            'gauge_invariant_mass_term_coefficient_rank':Amm.rank(),
            'allowed_mass_terms_without_new_fields':0,
            'higher_derivative_counterexample':higher_derivative}

def stress_ward_audit():
    t,x=s.symbols('t x',real=True)
    q=s.Function('q')(t,x)
    z=s.Function('z')(t,x)
    k,lam=s.symbols('k lam',real=True)
    V=k*(q-z)**2/s.Integer(2)+lam*(q-z)**4/s.Integer(4)
    qt,qx=s.diff(q,t),s.diff(q,x)
    zt,zx=s.diff(z,t),s.diff(z,x)
    L=(qt**2+zt**2-qx**2-zx**2)/2-V
    derivatives=[s.Matrix([-qt,qx]),s.Matrix([-zt,zx])]
    mink=s.diag(-1,1)
    T=derivatives[0]*derivatives[0].T + derivatives[1]*derivatives[1].T + mink*L
    # EOM in signature (-,+): □q - Vq =0
    Eq=-s.diff(q,t,2)+s.diff(q,x,2)-s.diff(V,q)
    Ez=-s.diff(z,t,2)+s.diff(z,x,2)-s.diff(V,z)
    for nu in range(2):
        div=s.diff(T[0,nu],t)+s.diff(T[1,nu],x)
        rhs=Eq*derivatives[0][nu]+Ez*derivatives[1][nu]
        assert s.simplify(s.expand(div-rhs))==0,(nu,s.simplify(div-rhs))
    # Separate energy-weight check: E = cq*Kq + cz*Kz + cV*V.
    cq,cz,cv,v,w,F=s.symbols('c_q c_z c_V v w F')
    # dv/dt=-F, dw/dt=+F, dV/dt=F(v-w)
    energy_rate=s.factor(-cq*v*F+cz*w*F+cv*F*(v-w))
    M,_=s.linear_eq_to_matrix([energy_rate.diff(v),energy_rate.diff(w)],[cq,cz,cv])
    assert M.rank()==2
    kvec=M.nullspace()[0]
    result=[s.simplify(a/kvec[0]) for a in kvec]
    assert result==[1,1,1]
    return {'flat_1_plus_1_stress_divergence_ward_identity':'∂μ T^{μν} = E_q ∂^ν q + E_z ∂^ν z',
            'ward_identity_checked_for_time_and_space_components':True,
            'interaction_potential':'V=k(q-z)^2/2 + lam(q-z)^4/4',
            'weighted_energy_source':'F*((cV-cq)*v+(cz-cV)*w)',
            'weighted_conservation_rank':M.rank(),
            'universal_coupling_weights_up_to_scale':[int(z) for z in result],
            'qualification':'conditional on splitting source into Kq, Kz, V with constant weights; this is not full universality / equivalence principle'}

def simulate_and_plot():
    k=.9
    lam=.35
    y0=[1.1, -0.25, .4, -.15]
    def ode(t,y):
        q,z,v,w=y
        d=q-z
        F=k*d+lam*d**3
        return [v,w,-F,F]
    times=np.linspace(0,24,1601)
    sol=solve_ivp(ode,(times[0],times[-1]),y0,method='DOP853',rtol=2e-13,atol=2e-14,t_eval=times)
    assert sol.success
    q,z,v,w=sol.y
    d=q-z
    F=k*d+lam*d**3
    Kq=v*v/2
    Kz=w*w/2
    V=k*d*d/2+lam*d**4/4
    Et=Kq+Kz+V
    rel_err=np.max(np.abs(Et-Et[0]))/Et[0]
    cases={'universal_total':(1.,1.,1.),'only_q':(1.,0.,0.),
           'no_potential':(1.,1.,0.),'unequal_species':(1.,2.,1.)}
    results={}
    for key,(cq,cz,cv) in cases.items():
        weighted=cq*Kq+cz*Kz+cv*V
        rate=F*((cv-cq)*v+(cz-cv)*w)
        derived=np.gradient(weighted,times,edge_order=2)
        # Rate numerical check away from extrema; magnitude or normalized error
        err=np.max(np.abs(derived[3:-3]-rate[3:-3]))
        results[key]={'weights':[cq,cz,cv],
                      'max_abs_source_divergence':float(np.max(np.abs(rate))),
                      'energy_span':float(np.max(weighted)-np.min(weighted)),
                      'numerical_derivative_rate_residual':float(err)}
    assert rel_err<1e-9,rel_err
    assert results['universal_total']['max_abs_source_divergence']==0
    assert results['only_q']['max_abs_source_divergence']>0.1
    arr=np.column_stack((times,q,z,v,w,Kq,Kz,V,Et,F))
    header='t,q,z,dot_q,dot_z,Kq,Kz,V,E_total,force'
    np.savetxt(OUT/'coupled_memory_timeseries.csv',arr,delimiter=',',header=header,comments='')
    plt.figure(figsize=(9.5,5.8))
    plt.plot(times,Kq,label='kinetic q')
    plt.plot(times,Kz,label='kinetic z')
    plt.plot(times,V,label='interaction potential')
    plt.plot(times,Et,'k--',label='total energy')
    plt.xlabel('Model time'); plt.ylabel('Model energy')
    plt.title('Interacting fields exchange energy, while the total is conserved')
    plt.legend(); plt.grid(alpha=.2); plt.tight_layout()
    plt.savefig(OUT/'energy_exchange_v20.png',dpi=165);plt.close()
    names=list(cases)
    amounts=[results[key]['max_abs_source_divergence'] for key in names]
    plt.figure(figsize=(9.3,4.4))
    plt.bar(np.arange(len(names)),amounts)
    plt.xticks(np.arange(len(names)),names,rotation=15,ha='right')
    plt.ylabel('max |d(weighted energy)/dt|')
    plt.title('Only universal weighting of interacting sectors is conserved')
    plt.grid(axis='y',alpha=.2)
    plt.tight_layout();plt.savefig(OUT/'source_ward_failure_v20.png',dpi=165);plt.close()
    return {'ode':'qddot=-Vq; zddot=+Vq; V=k(q-z)^2/2+lam(q-z)^4/4',
            'k':k,'lam':lam,'time_interval':[0,24], 'samples':len(times),
            'total_energy_initial':float(Et[0]),
            'max_relative_total_energy_drift':float(rel_err),
            'source_tests':results,
            'derivative_check_caveat':'finite-difference derivative residual is discretization error, not violation of exact identity'}

def main():
    audit={'test':'v20 massless spin-2 gauge constraints and interacting source conservation',
           'spin_two':spin2_audit(), 'stress_conservation':stress_ward_audit(),
           'dynamics':simulate_and_plot(),
           'scientific_boundary':'This reconstructs conditional linear spin-2 structure and source consistency only. It neither derives GR from the gel-like medium nor solves Einstein-Skyrme static or time-dependent equations.'}
    (OUT/'audit_v20.json').write_text(json.dumps(audit,indent=2,ensure_ascii=False)+'\n')
    print(json.dumps(audit,ensure_ascii=False,indent=2))
if __name__=='__main__':main()
