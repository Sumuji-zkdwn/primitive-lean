#!/usr/bin/env python3
"""Independent NumPy/finite-difference checks of v26 output (no JAX derivatives)."""
import json, csv
from pathlib import Path
import numpy as np
ROOT=Path(__file__).resolve().parent
rng=np.random.default_rng(261123)

def parameters(chi,q):
    F=2+.35*np.tanh(chi)
    P=.35/(np.cosh(chi)**2)
    A=1+1.8*np.tanh((q-chi)/.5)**2
    D=1+1.5*P**2/F
    V=.5*(q-chi)**2+.07*chi**2
    return F,P,A,D,V

def H_numpy(y):
    bet=y[:3]; chi,q=y[3:5]; Pbeta=y[5:8]; pc,pq=y[8:10]
    vol=np.exp(sum(bet))
    F,Fp,A,D,V=parameters(chi,q)
    pi=Pbeta/2; ptr=sum(pi)
    return 2*np.sum((pi-ptr/3)**2)/(vol*F)-ptr**2/(3*vol*F)+(pc-Fp/F*ptr)**2/(2*vol*D)+pq**2/(2*vol*A)+vol*V

largest_leg=0; largest_momentum=0; min_F=999;min_D=999
for i in range(1000):
    beta=rng.normal(0,.4,3); chi=float(rng.normal()); q=float(rng.normal())
    ki=rng.normal(0,.6,3); nc=float(rng.normal()); nq=float(rng.normal())
    vol=np.exp(beta.sum()); F,Fp,A,D,V=parameters(chi,q)
    K=ki.sum()
    Lkin=vol*(F/2*(sum(ki**2)-K**2)-Fp*K*nc+.5*nc**2 +.5*A*nq**2)
    pi=vol/2*(F*(ki-K)-Fp*nc)
    pc=vol*(nc-Fp*K); pq=vol*A*nq
    Ltest=(2*np.dot(pi,ki)+pc*nc+pq*nq)-Lkin
    pt=pi.sum()
    Htest=2*np.sum((pi-pt/3)**2)/(vol*F)-pt**2/(3*vol*F)+(pc-Fp/F*pt)**2/(2*vol*D)+pq**2/(2*vol*A)
    largest_leg=max(largest_leg,abs(Ltest-Htest)/(1+abs(Ltest)))
    # derivative checks w.r.t velocities using finite differences
    def v_lagr(v):
        kk=np.array(v[:3]); cc=v[3]; qq=v[4]
        kk_sum=kk.sum()
        return vol*(F/2*(sum(kk**2)-kk_sum**2)-Fp*kk_sum*cc+.5*cc**2+.5*A*qq**2)
    ve=np.array([*ki,nc,nq]); grads=[]
    for k in range(5):
        eps=1e-6
        h=np.zeros(5);h[k]=eps
        grads.append((v_lagr(ve+h)-v_lagr(ve-h))/(2*eps))
    exp=np.array([*(2*pi),pc,pq])
    largest_momentum=max(largest_momentum,float(np.max(np.abs(np.array(grads)-exp)/(1+np.abs(exp)))))
    min_F=min(min_F,F); min_D=min(min_D,D)
assert largest_leg<1e-12,(largest_leg)
assert largest_momentum<2e-8,largest_momentum

with open(ROOT/'bianchi_evolution_v26.csv') as f:
    data=list(csv.DictReader(f))
residuals=[]
for row in data:
    y=np.array([float(row[key]) for key in ['beta1','beta2','beta3','chi','q','Pbeta1','Pbeta2','Pbeta3','pchi','pq']])
    residuals.append(abs(H_numpy(y)-float(row['constraint_correct'])))
assert max(residuals)<1e-11,max(residuals)
# Do own finite difference gradient on time slices, independent of autodiff.
samples=[data[i] for i in (0,len(data)//2,len(data)-1)]
from verify_v26 import jgrad
max_gradient_err=0
for row in samples:
    y=np.array([float(row[key]) for key in ['beta1','beta2','beta3','chi','q','Pbeta1','Pbeta2','Pbeta3','pchi','pq']])
    grad=[]
    for i in range(10):
        h=2e-6
        yp=y.copy();ym=y.copy();yp[i]+=h;ym[i]-=h
        grad.append((H_numpy(yp)-H_numpy(ym))/(2*h))
    from_jax=np.array(jgrad(y))
    max_gradient_err=max(max_gradient_err,float(np.max(np.abs(np.array(grad)-from_jax)/(1+np.abs(from_jax)))))
assert max_gradient_err<1e-8,max_gradient_err

sym=json.loads((ROOT/'audit_v26.json').read_text())['symbolic']
assert sym['legendre_identity_exact'] and sym['spatial_sector_symplectic_bracket_defect_count']==0
report={'status':'PASS', 'random_velocity_states':1000,
        'max_relative_legendre_residual':largest_leg,
        'max_relative_finite_difference_momentum_residual':largest_momentum,
        'max_abs_time_series_constraint_reconstruction':max(residuals),
        'max_relative_hamiltonian_gradient_error_vs_jax':max_gradient_err,
        'min_F_random_sample':min_F,'min_D_random_sample':min_D,
        'state_count':len(data),
        'strict_scope':'Only 3+1 kinetic ADM algebra and homogeneous Bianchi I evolution; not full field Dirac bracket.'}
(ROOT/'independent_audit_v26.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
