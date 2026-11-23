#!/usr/bin/env python3
"""V24: Poisson bracket of two coupled scalar fields on an external 1D spatial metric.

All result files are written beside this script. No network access required.
The full gravity constraint algebra is NOT computed here.
"""
from __future__ import annotations
import json, csv
from pathlib import Path
import numpy as np
import sympy as sp
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

OUT = Path(__file__).resolve().parent


def deriv(f, dx):
    return (np.roll(f, -1, axis=-1) - np.roll(f, 1, axis=-1))/(2*dx)


def system(n, L=2*np.pi):
    x = L*np.arange(n)/n
    dx=L/n
    q = 0.25*np.sin(x+.18)+0.08*np.cos(2*x-.37)+0.03*np.sin(3*x+.21)
    z = -0.12*np.cos(x-.35)+0.06*np.sin(2*x+.58)-0.025*np.cos(3*x-.21)
    pq = 0.37 + 0.16*np.cos(x-.29)+0.035*np.sin(2*x+.41)
    pz = -0.22 + 0.19*np.sin(x+.49)-0.045*np.cos(3*x-.20)
    a = 1.16 + .13*np.sin(x+.38)+.07*np.cos(2*x+.31)
    N = 1.1 + .32*np.sin(x+.29)+.11*np.cos(2*x+.2)
    M = .65 + .29*np.cos(x-.71)+.20*np.sin(3*x+.57)
    return {'x':x,'dx':dx,'f':np.stack([q,z]),'p':np.stack([pq,pz]),
            'a':a,'N':N,'M':M}


def coeff(f, matched=True, delta=2.3, sigma=.44):
    q,z=f
    y=(q-z)/sigma
    ty=np.tanh(y)
    A=1+delta*ty**2
    Ap=2*delta*ty*(1-ty**2)/sigma
    B=A if matched else np.ones_like(A)
    Bp=Ap if matched else np.zeros_like(A)
    return A,Ap,B,Bp


def densities(d, N, matched=True, kappa=1.7, derivatives=True):
    # Exact derivatives of the sampled finite-dimensional lattice Hamiltonian.
    # The canonical lattice bracket is {f_{Ai},p_{Bj}}=deltaAB deltaij/dx.
    f,p,a,dx=d['f'],d['p'],d['a'],d['dx']
    q,z=f; pq,pz=p; y=q-z
    A,Ap,B,Bp=coeff(f,matched)
    fq,fz=deriv(f,dx)
    e= (pq**2/A + pz**2 + B*fq**2 + fz**2)/(2*a) + a*.5*kappa*y*y
    H=dx*np.sum(N*e)
    dP=np.stack([N*pq/(a*A), N*pz/a])
    if not derivatives:
        return H
    # Local derivatives in N cancel out of the antisymmetrized bracket.
    local= N*((-pq**2*Ap/A**2 + Bp*fq**2)/(2*a) + a*kappa*y)
    dFq=local-deriv(N*B*fq/a,dx)
    dFz=-local-deriv(N*fz/a,dx)
    dF=np.stack([dFq,dFz])
    return H,dF,dP


def bracket(d,matched=True,kappa=1.7):
    _,dFN,dPN=densities(d,d['N'],matched,kappa)
    _,dFM,dPM=densities(d,d['M'],matched,kappa)
    return d['dx']*np.sum(dFN*dPM-dPN*dFM)


def continuum_rhs(d,matched=True):
    f,p,a,dx=d['f'],d['p'],d['a'],d['dx']
    A,_,B,_=coeff(f,matched)
    fprime=deriv(f,dx)
    base= p[0]*fprime[0] + p[1]*fprime[1]
    weighted = (B/A)*p[0]*fprime[0] + p[1]*fprime[1]
    W=(d['N']*deriv(d['M'],dx)-d['M']*deriv(d['N'],dx))/a**2
    return dx*np.sum(W*base),dx*np.sum(W*weighted)


def continuum_high_precision(n=131072):
    # Smooth sampled functions and spectrally accurate reference derivative.
    # For checks of convergence use a sufficiently dense grid.
    d=system(n)
    def spec(f):
        modes=np.fft.fftfreq(n,d['dx'])*2*np.pi
        return np.fft.ifft(1j*modes*np.fft.fft(f)).real
    f,p,a=d['f'],d['p'],d['a']
    N,M=d['N'],d['M']
    W=(N*spec(M)-M*spec(N))/a**2
    A,_,Bbad,_=coeff(f,matched=False)
    base=p[0]*spec(f[0])+p[1]*spec(f[1])
    bad=(Bbad/A)*p[0]*spec(f[0])+p[1]*spec(f[1])
    return float(d['dx']*np.sum(W*base)),float(d['dx']*np.sum(W*bad))


def symbolic():
    k11,k12,k22,s11,s12,s22=sp.symbols('k11 k12 k22 s11 s12 s22',real=True)
    K=sp.Matrix([[k11,k12],[k12,k22]])
    S=sp.Matrix([[s11,s12],[s12,s22]])
    conditions=list(K*S-sp.eye(2))
    sol=sp.solve(conditions,(s11,s12,s22),dict=True)
    assert len(sol)==1
    assert sp.simplify(sp.Matrix([[sol[0][s11],sol[0][s12]],[sol[0][s12],sol[0][s22]]])-K.inv())==sp.zeros(2)
    # Nondegeneracy of K is assumed. Tensor product fields require K S = I
    return {'equations':[str(e) for e in conditions],
            'solution':{str(k):str(v) for k,v in sol[0].items()},
            'assumption':'det(K) != 0; K and S symmetric',
            'verified':'S=K^-1 uniquely, for this 2x2 quadratic ansatz'}


def derivative_check():
    d=system(28)
    rng=np.random.default_rng(24012026)
    eps=1e-6
    checks=[]
    for matched in (True,False):
        _,dF,dP=densities(d,d['N'],matched=matched)
        for _ in range(16):
            field_type=int(rng.integers(0,2))
            A=int(rng.integers(0,2)); j=int(rng.integers(0,28))
            data_field='f' if field_type==0 else 'p'
            field=d[data_field]
            old=field[A,j]
            field[A,j]=old+eps
            hp=densities(d,d['N'],matched=matched,derivatives=False)
            field[A,j]=old-eps
            hm=densities(d,d['N'],matched=matched,derivatives=False)
            field[A,j]=old
            numeric=(hp-hm)/(2*eps)/d['dx']
            exact=(dF if field_type==0 else dP)[A,j]
            checks.append([matched,data_field,A,j,float(numeric),float(exact),float(abs(numeric-exact))])
    return checks


def cases():
    table=[]
    for n in (24,32,48,64,96,128,192,256,384,512):
        d=system(n)
        for label,matched in (('matched',True),('mismatched',False)):
            pb=bracket(d,matched)
            conventional,weighted=continuum_rhs(d,matched)
            row={'n':n,'dx':d['dx'],'model':label,'poisson_bracket':pb,
                 'standard_D_rhs':conventional,'modified_rhs':weighted,
                 'standard_abs_error':abs(pb-conventional),
                 'modified_abs_error':abs(pb-weighted)}
            table.append(row)
    return table


def test_kappa_invariance():
    d=system(80)
    vals=[bracket(d,True,kappa=k) for k in (0.,.1,1.7,4.2,11.)]
    return vals,max(vals)-min(vals)


def plot(table,ref):
    fig,ax=plt.subplots(figsize=(8,4.5))
    for model,marker in [('matched','o'),('mismatched','s')]:
        rows=[r for r in table if r['model']==model]
        ax.loglog([r['dx'] for r in rows],[r['standard_abs_error'] for r in rows],
                  marker=marker,label=f'{model}: standard constraint target')
    # independent matched/mismatched continuum limit
    ax.set(xlabel='Grid spacing Δx',ylabel='| {H[N],H[M]} − D[a⁻²(NM′−MN′)] |',
           title='Two-field Poisson bracket: matched and mismatched propagation')
    ax.grid(True,which='both',alpha=.2)
    ax.legend()
    fig.tight_layout()
    fig.savefig(OUT/'constraint_closure_v24.png',dpi=180)
    plt.close(fig)
    fig,ax=plt.subplots(figsize=(8,4.2))
    for model,marker in [('matched','o'),('mismatched','s')]:
        rows=[r for r in table if r['model']==model]
        ax.loglog([r['dx'] for r in rows],[max(r['modified_abs_error'],1e-18) for r in rows],
                  marker=marker,label=f'{model}: own continuum target')
    ax.set(xlabel='Grid spacing Δx',ylabel='Discrete bracket error to derived continuum expression',
           title='Second-order convergence of the discrete bracket')
    ax.grid(True,which='both',alpha=.2)
    ax.legend()
    fig.tight_layout()
    fig.savefig(OUT/'bracket_discretization_v24.png',dpi=180)
    plt.close(fig)
    y=np.linspace(-1.5,1.5,400)
    A=1+2.3*np.tanh(y/.44)**2
    fig,ax=plt.subplots(figsize=(8,4.3))
    ax.plot(y,np.sqrt(A/A),label='Matched: q and z front speed')
    ax.plot(y,1/np.sqrt(A),label='Mismatched: q speed')
    ax.plot(y,np.ones_like(y),linestyle=':',label='Mismatched: z speed')
    ax.set(xlabel='Lag y = q − z',ylabel='Local characteristic speed / c',
           title='Common-cone condition demands matched stiffness and inertia')
    ax.legend();ax.grid(alpha=.2)
    fig.tight_layout();fig.savefig(OUT/'characteristic_speeds_v24.png',dpi=180);plt.close(fig)


def main():
    symbolic_output=symbolic()
    tests=derivative_check()
    tab=cases()
    reference=continuum_high_precision()
    kappas,kspread=test_kappa_invariance()
    plot(tab,reference)
    keys=list(tab[0].keys())
    with (OUT/'bracket_convergence_v24.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=keys);w.writeheader();w.writerows(tab)
    with (OUT/'gradient_audit_v24.csv').open('w',newline='') as f:
        w=csv.writer(f);w.writerow(['matched','field','component','site','finite_diff','analytic','abs_difference']);w.writerows(tests)
    best=[r for r in tab if r['n']==512]
    report={
       'model':'1+1 dimensional coupled scalar matter on externally prescribed spatial metric gamma_xx=a(x)^2',
       'not_a_gravity_constraint_test':True,
       'analytic_condition':'K S = identity is necessary and sufficient within the quadratic scalar ansatz for standard matter H-H bracket; matrix K positive definite',
       'symbolic':symbolic_output,
       'reference_continuum':{'standard':reference[0],'mismatched_weighted':reference[1],
                               'mismatched_difference':reference[1]-reference[0]},
       'n512':best,
       'gradient_max_abs_error':max(t[6] for t in tests),
       'potential_variation_bracket_range':kspread,
       'potential_variation_brackets':kappas,
       'finite_lattice_closure_exact':False,
       'convergence_test':{'matched_256_to_512_error_ratio': [r['standard_abs_error'] for r in tab if r['model']=='matched' and r['n']==256][0]/best[0]['standard_abs_error'],
                           'bad_model_standard_256_to_512_error_ratio': [r['standard_abs_error'] for r in tab if r['model']=='mismatched' and r['n']==256][0]/best[1]['standard_abs_error']},
       'scope':'matter sector alone, reversible local memory, no spatial metric momentum, full 3+1 Einstein constraint algebra not checked',
    }
    (OUT/'audit_v24.json').write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n')
    print(json.dumps({k:report[k] for k in ['reference_continuum','n512','gradient_max_abs_error','potential_variation_bracket_range','convergence_test']},indent=2))
    assert report['gradient_max_abs_error']<1e-7,report['gradient_max_abs_error']
    assert abs(report['convergence_test']['matched_256_to_512_error_ratio']-4)<.12,report['convergence_test']
    assert abs(best[0]['poisson_bracket']-reference[0])<2e-4
    assert abs(best[1]['poisson_bracket']-reference[1])<2e-4
    assert abs(reference[1]-reference[0])>1e-3
    assert abs(kspread)<1e-12
    print('V24 verification PASSED')


if __name__=='__main__':main()
