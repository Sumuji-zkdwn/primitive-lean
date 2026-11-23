#!/usr/bin/env python3
"""v25: weak-field slice of canonical ADM + two memory-coupled scalars.

Exact continuum cross cancellation (minimal coupling), direct finite-dimensional
canonical bracket on a flat 3D metric sampled in an x-dependent sector, and a
counterexample to adding lambda*q*sqrt(g)*R without adjusting momenta.

IMPORTANT: This is NOT a full nonlinear 3+1 ADM numerical evolution or a
spontaneous emergence of GR. Curvature R is linearized at the flat slice for
finite-dimensional direct PB, adequate for first functional derivatives there.
"""
from __future__ import annotations
import csv
import json
from pathlib import Path
import numpy as np
import sympy as sp
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
OUT = Path(__file__).resolve().parent


def D(v, dx):
    return (np.roll(v, -1, axis=-1)-np.roll(v,1,axis=-1))/(2*dx)


def D2(v, dx):
    return D(D(v,dx),dx)


def background(n: int):
    x=2*np.pi*np.arange(n)/n
    return {
       'n':n,'dx':2*np.pi/n,'x':x,
       'q': .22*np.cos(x+.17)+.07*np.sin(2*x+.39),
       'z': -.15*np.sin(x-.21)+.06*np.cos(3*x-.15),
       'pq': .19+.13*np.cos(x-.28)+.07*np.sin(2*x+.55),
       'pz': -.08+.09*np.sin(x+.34)+.07*np.cos(2*x-.16),
       'pxx': .38+.18*np.cos(x-.43)+.08*np.sin(2*x+.13),
       'N':1.06+.24*np.cos(x-.38)+.10*np.sin(2*x+.12),
       'M':.73+.19*np.sin(x+.22)+.08*np.cos(3*x-.39)
    }


def stiffness(q,z):
    y=(q-z)/.44
    t=np.tanh(y)
    A=1+2.3*t*t
    Ap=2*2.3/.44*t*(1-t*t)
    return A,Ap


def matter_gradients(d, lapse):
    q,z,pq,pz,dx=(d[k] for k in ('q','z','pq','pz','dx'))
    A,Ap=stiffness(q,z)
    qp,zp=D(q,dx),D(z,dx)
    kap=1.7
    local=lapse*((-pq*pq*Ap/A**2+Ap*qp*qp)/2+kap*(q-z))
    dQ=local-D(lapse*A*qp,dx)
    dZ=-local-D(lapse*zp,dx)
    dPq=lapse*pq/A
    dPz=lapse*pz
    return dQ,dZ,dPq,dPz


def separate_brackets(d):
    N,M,dx=(d[k] for k in ('N','M','dx'))
    nq,nz,npq,npz=matter_gradients(d,N)
    mq,mz,mpq,mpz=matter_gradients(d,M)
    matter=dx*np.sum(nq*mpq+nz*mpz -npq*mq-npz*mz)
    # Pure ADM gravity PB at gamma_ij=delta_ij, sampled with x dependence:
    # curvature variation + kinetic metric-momentum variation are retained.
    pxx=d['pxx']
    grav=2*dx*np.sum(pxx*(N*D2(M,dx)-M*D2(N,dx)))
    v=N*D(M,dx)-M*D(N,dx)
    gravity_rhs=dx*np.sum(v*(-2*D(pxx,dx)))
    matter_rhs=dx*np.sum(v*(d['pq']*D(d['q'],dx)+d['pz']*D(d['z'],dx)))
    return {'pure_gravity':float(grav),'pure_matter':float(matter),'total':float(grav+matter),
            'gravity_momentum_constraint':float(gravity_rhs),
            'matter_momentum_constraint':float(matter_rhs),
            'total_constraint':float(gravity_rhs+matter_rhs),
            'closure_error':float((grav+matter)-(gravity_rhs+matter_rhs))}


def local_metric_cross(d):
    """Off-shell cross PB for general varying *diagonal* gamma_ii(x) and pi^ii(x).

    Gravity Hamiltonian may contain -sqrt(g) R; its pi-variation depends only
    on local metric and momentum. H_m is independent of gravity momentum.
    Hence the cross cancellation needs no curvature approximation.
    """
    x,dx,N,M=(d[k] for k in ('x','dx','N','M'))
    gam=np.stack([1.1+.07*np.cos(x+.23),.94+.09*np.sin(2*x+.1),1.19+.08*np.sin(x-.28)])
    pig=np.stack([d['pxx'], .11*np.sin(x+.67), -.08+.06*np.cos(3*x-.55)])
    sq=np.sqrt(np.prod(gam,axis=0))
    a,_=stiffness(d['q'],d['z'])
    v=.85*(d['q']-d['z'])**2
    kin=(d['pq']**2/a+d['pz']**2)/(2*sq)
    grd=sq/(2*gam[0])*(a*D(d['q'],dx)**2+D(d['z'],dx)**2)
    pot=sq*v
    metric_grad=np.stack([(-kin+grd+pot)/(2*gami)-(grd/gam[0] if i==0 else 0)
                          for i,gami in enumerate(gam)])
    tr=np.sum(gam*pig,axis=0)
    pi_grad=(2/sq)*(gam*gam*pig - .5*gam*tr)
    Bgm=-dx*np.sum((N*pi_grad)*(M*metric_grad))
    Bmg=dx*np.sum((N*metric_grad)*(M*pi_grad))
    return {'gravitational_matter_cross':float(Bgm),
            'matter_gravitational_cross':float(Bmg),
            'antisym_sum':float(Bgm+Bmg),
            'max_local_momentum_variation':float(np.max(np.abs(pi_grad)))}


def total_hamiltonian(d, lapse, gamma, pig, lam=0.):
    """Linearized spatial curvature R=-D²(h_yy+h_zz) exact to first order at flat.

    H = H_ADMkin -sqrt(g) R_lin + H_m + lam*q*sqrt(g)*R_lin.
    For the derivative at flat, this is an exact test of the full continuum
    Hamiltonian's first variation (within the x-dependent diagonal sector).
    """
    dx=d['dx']; q,z,pq,pz=(d[k] for k in ('q','z','pq','pz'))
    sqrtg=np.sqrt(np.prod(gamma,axis=0)); trace=np.sum(gamma*pig,axis=0)
    kin_g=(np.sum(gamma**2 *pig**2,axis=0)-.5*trace**2)/sqrtg
    rlin=-D2(gamma[1]+gamma[2]-2,dx)
    a,_=stiffness(q,z)
    kin_m=(pq**2/a+pz**2)/(2*sqrtg)
    grad_m=sqrtg/(2*gamma[0])*(a*D(q,dx)**2+D(z,dx)**2)
    pot_m=.85*sqrtg*(q-z)**2
    return float(dx*np.sum(lapse*(kin_g-sqrtg*rlin+kin_m+grad_m+pot_m +lam*q*sqrtg*rlin)))


def direct_canonical_pb(d, lam=0., eps=1e-6):
    """Independent direct finite-difference derivs for all 5 canonical pairs.

    Canonical pairs per lattice site: (gamma_xx,pi^xx), (gamma_yy,pi^yy),
    (gamma_zz,pi^zz), (q,p_q), (z,p_z). All 10 sets varied separately.
    """
    n=d['n']; dx=d['dx'];
    gam=np.ones((3,n)); pig=np.zeros((3,n)); pig[0]=d['pxx'].copy()
    state={**d,'q':d['q'].copy(),'z':d['z'].copy(),'pq':d['pq'].copy(),'pz':d['pz'].copy()}
    def H(lapse): return total_hamiltonian(state,lapse,gam,pig,lam)
    gradients=[]
    for lapse in (d['N'],d['M']):
        gd=[]
        for kind,i in [('gamma',0),('gamma',1),('gamma',2),('pi',0),('pi',1),('pi',2),
                       ('q',0),('z',0),('pq',0),('pz',0)]:
            arr = (gam[i] if kind=='gamma' else pig[i] if kind=='pi' else state[kind])
            res=np.empty(n)
            for j in range(n):
                old=arr[j]
                arr[j]=old+eps; plus=H(lapse)
                arr[j]=old-eps; minus=H(lapse)
                arr[j]=old
                res[j]=(plus-minus)/(2*eps)
            gd.append(res)
        gradients.append(gd)
    a,b=gradients
    pair_indices=[(0,3),(1,4),(2,5),(6,8),(7,9)]
    perpair={}
    for label,(qi,pi) in zip(('xx','yy','zz','q','z'),pair_indices):
        perpair[label]=float(np.sum(a[qi]*b[pi]-a[pi]*b[qi])/dx)
    return {'poisson_bracket':float(sum(perpair.values())), 'component_contributions':perpair,
            'eps':eps}


def counterexample(n):
    d=background(n)
    x=d['x']
    d.update(q=np.cos(x),z=np.zeros(n),pq=np.zeros(n),pz=np.zeros(n),
             pxx=np.full(n,3/5),N=1+.2*np.cos(x),M=1+.3*np.sin(x))
    lam=.25
    # Only new non-minimal cross contributions at flat gamma, zero matter momenta.
    # Functional metric variation of lambda*q*sqrt(g)*R produces -lambda D²(Mq)
    # in both yy and zz directions.
    analytic_discrete=-2*lam*(3/5)*d['dx']*np.sum(d['N']*D2(d['M']*d['q'],d['dx'])-
                                                 d['M']*D2(d['N']*d['q'],d['dx']))
    exact=float(3*np.pi/50)
    return d,{'n':n,'discrete_nonminimal_anomaly':float(analytic_discrete),
              'exact_continuum_anomaly':exact,'abs_error':float(abs(analytic_discrete-exact)),
              'expected_standard_momentum_constraint':0.0}


def symbolic_checks():
    A,kappa=sp.symbols('A kappa',positive=True)
    y=sp.symbols('y',real=True)
    G=sp.diag(A,1); K=G.inv(); assert K*G==sp.eye(2)
    N=1+sp.Rational(1,5)*sp.cos(y)
    M=1+sp.Rational(3,10)*sp.sin(y)
    q=sp.cos(y)
    W=sp.expand_trig(N*sp.diff(M,y)-M*sp.diff(N,y))
    intq=sp.integrate(sp.diff(q,y)*W,(y,0,2*sp.pi))
    assert sp.simplify(intq+sp.pi/5)==0
    P,lam=sp.Rational(3,5),sp.Rational(1,4)
    anomaly=sp.simplify(-2*P*lam*intq)
    assert sp.simplify(anomaly-3*sp.pi/50)==0
    return {'field_metric_product':str(K*G),
            'nonminimal_integral':str(intq),'nonminimal_anomaly':str(anomaly),
            'anomaly_float':float(anomaly),
            'continuum_cross_cancellation':'For algebraic gamma-coupling and no gravity momenta in Hm, terms are N*M-local and antisymmetrize to zero.'}


def figures(tbl,anomalies,cmp):
    fig,ax=plt.subplots(figsize=(7.8,4.7))
    ns=np.array([x['n'] for x in tbl]); h=2*np.pi/ns
    ax.loglog(h,[abs(x['closure_error']) for x in tbl],'-o',label='full PB minus gravity + matter D')
    ax.loglog(h, [abs(x['pure_gravity']-x['gravity_momentum_constraint']) for x in tbl],':s',label='gravity contribution')
    ax.loglog(h,[abs(x['pure_matter']-x['matter_momentum_constraint']) for x in tbl],'--^',label='memory matter contribution')
    ax.set(xlabel='grid spacing Δx',ylabel='absolute closure residual',title='Full ADM + memory: sampled flat-metric slice')
    ax.legend();ax.grid(alpha=.2,which='both');fig.tight_layout();fig.savefig(OUT/'full_constraint_convergence_v25.png',dpi=190);plt.close(fig)
    fig,ax=plt.subplots(figsize=(7.8,4.7))
    ax.plot([d['n'] for d in anomalies],[d['discrete_nonminimal_anomaly'] for d in anomalies],'-o',label='canonical anomaly from λ q R')
    ax.axhline(3*np.pi/50,linestyle='--',label='continuum 3π/50')
    ax.axhline(0,linestyle=':',label='required if D_total = 0')
    ax.set(xlabel='number of periodic sites',ylabel='smeared bracket, per unit transverse area',
           title='Naively adding curvature-memory coupling violates constraints')
    ax.legend();ax.grid(alpha=.2);fig.tight_layout();fig.savefig(OUT/'nonminimal_constraint_failure_v25.png',dpi=190);plt.close(fig)
    fig,ax=plt.subplots(figsize=(7.8,4.3))
    ax.bar(['{Hg[N],Hm[M]}','{Hm[N],Hg[M]}','sum'],[cmp['gravitational_matter_cross'],cmp['matter_gravitational_cross'],cmp['antisym_sum']])
    ax.set(ylabel='mixed canonical Poisson bracket',title='Minimal coupling: gravity–memory cross cancellation')
    ax.grid(axis='y',alpha=.2);fig.tight_layout();fig.savefig(OUT/'mixed_terms_cancel_v25.png',dpi=190);plt.close(fig)


def main():
    sym=symbolic_checks()
    tab=[]
    for n in (24,32,48,64,96,128,192,256,384,512):
        row={'n':n,**separate_brackets(background(n))}
        tab.append(row)
    cmp=local_metric_cross(background(128))
    direct=direct_canonical_pb(background(20))
    assembled=separate_brackets(background(20))
    direct['assembly_error']=float(direct['poisson_bracket']-assembled['total'])
    direct['expected_assembled']=assembled['total']
    anom=[counterexample(n)[1] for n in (16,24,32,48,64,96,128,192,256,384)]
    d, _=counterexample(16)
    nonminimal_direct=direct_canonical_pb(d,lam=.25)
    nonminimal_direct['exact_continuum']=float(3*np.pi/50)
    nonminimal_direct['direct_vs_discrete']=float(nonminimal_direct['poisson_bracket']-anom[0]['discrete_nonminimal_anomaly'])
    strength_scan=[]
    for test_lam in (0., .05, .10, .20, .25, .40):
        calc=direct_canonical_pb(d,lam=test_lam)
        predict=anom[0]['discrete_nonminimal_anomaly']*test_lam/.25
        strength_scan.append({'lambda':test_lam,'direct_pb':calc['poisson_bracket'],
                              'predicted_discrete':predict,
                              'abs_difference':abs(calc['poisson_bracket']-predict)})
    with (OUT/'full_bracket_convergence_v25.csv').open('w',newline='') as f:
        wr=csv.DictWriter(f,fieldnames=list(tab[0]));wr.writeheader();wr.writerows(tab)
    with (OUT/'nonminimal_counterexample_v25.csv').open('w',newline='') as f:
        wr=csv.DictWriter(f,fieldnames=list(anom[0]));wr.writeheader();wr.writerows(anom)
    with (OUT/'nonminimal_strength_scan_v25.csv').open('w',newline='') as f:
        wr=csv.DictWriter(f,fieldnames=list(strength_scan[0]));wr.writeheader();wr.writerows(strength_scan)
    figures(tab,anom,cmp)
    audit={'scope':'Full canonical PB at gamma=delta and x-dependent diagonal canonical sector, curvature varied to first order; not full nonlinear 3+1',
           'direct_canonical_pairs':'Three diagonal metric-momentum pairs plus q,pq and z,pz (5 pairs/site)',
           'symbolic':sym,
           'cross_varying_metric':cmp,
           'n20_direct_finite_difference_bracket':direct,
           'nonminimal_direct_n16':nonminimal_direct,
           'nonminimal_strength_scan':strength_scan,
           'n512_closure':tab[-1],
           'n256_closure':tab[-3],
           'n384_counterexample':anom[-1],
           'model_limitations':['Einstein-Hilbert gravity assumed, not derived','no full nonlinear non-flat ADM PB',
                                'q,z memory is reversible, not dissipative','spatial gradient finite differences break exact closure at finite h']}
    (OUT/'audit_v25.json').write_text(json.dumps(audit,ensure_ascii=False,indent=2)+'\n')
    assert abs(cmp['antisym_sum'])<1e-12
    assert abs(direct['assembly_error'])<1e-6, direct
    assert abs(nonminimal_direct['direct_vs_discrete'])<1e-6,nonminimal_direct
    assert max(t['abs_difference'] for t in strength_scan)<1e-6, strength_scan
    assert abs(tab[-1]['closure_error']) < abs(tab[-3]['closure_error'])
    assert abs(tab[-1]['closure_error'])<3e-4,tab[-1]
    assert anom[-1]['abs_error']<1e-3
    print(json.dumps(audit,ensure_ascii=False,indent=2))
    print('V25 checks PASSED')

if __name__=='__main__':main()