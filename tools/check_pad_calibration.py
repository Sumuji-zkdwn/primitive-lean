#!/usr/bin/env python3
"""PR #97/#101 finite PAD follow-up; mathematical toy, NOT experimental eKE.

Exact Fraction witnesses + local Jacobian analysis for the illustrative
shared calibration scale s_i(alpha)=u_i**alpha. No PAD measurements used.
"""
import json
from fractions import Fraction as F
from pathlib import Path
import numpy as np
from scipy.optimize import differential_evolution, minimize_scalar

sigma = .001
alpha_sd = .05
H=np.array([[1.,1,1,1],[0,1,2,3]])
_,_,vh=np.linalg.svd(H,full_matrices=True)
N=vh[2:].T
assert np.allclose(H@N,0) and np.allclose(N.T@N,np.eye(2))

def row(u): return np.array([1.,u,u*u,u**3])
def f(u,p): return row(u)@p
def df(u,p): return p[1]+2*p[2]*u+3*p[3]*u*u
def jac(us,p):
    return np.array([np.r_[row(u)@N,df(u,p)*u*np.log(u)] for u in us])

def profile_rms(us,p,with_prior=False):
    J=jac(us,p)
    info=J.T@J/sigma**2
    if with_prior: info[2,2]+=1/alpha_sd**2
    if np.linalg.matrix_rank(info)<3: return float('inf')
    return float(np.sqrt(np.trace(np.linalg.inv(info)[:2,:2])))

def exact_checks():
    p=(F(1,4),)*4
    t,s=F(1,20),F(7,20)
    t1,s1=t+F(1,1000),s+F(1,1000)
    R=lambda x,q:sum(v*x**i for i,v in enumerate(q))
    m=sum(p);mu=sum(i*p[i] for i in range(4))
    rt=(R(t,p)-m-(t-1)*mu)/(t-1)**2
    rs=(R(s,p)-m-(s-1)*mu)/(s-1)**2
    d=(rs-rt)/(s-t);c=((s+2)*rt-(t+2)*rs)/(s-t)
    assert (m-mu+c+2*d,mu-2*c-3*d,c,d)==p
    y=[m,mu,R(t,p),R(s,p)]
    A=[[F(1)]*4,[F(0),F(1),F(2),F(3)],
       [F(1),t1,t1*t1,t1**3],[F(1),s1,s1*s1,s1**3]]
    T=[a+[v] for a,v in zip(A,y)]
    for j in range(4):
        i=next(i for i in range(j,4) if T[i][j])
        T[i],T[j]=T[j],T[i]
        z=T[j][j];T[j]=[v/z for v in T[j]]
        for i in range(4):
            if i!=j:
                z=T[i][j];T[i]=[a-z*b for a,b in zip(T[i],T[j])]
    q=tuple(r[-1] for r in T)
    assert q!=p and min(q)>0
    assert sum(q)==m and sum(i*q[i] for i in range(4))==mu
    assert R(t1,q)==y[2] and R(s1,q)==y[3]
    return dict(original_s=list(map(str,(t,s))),new_s=list(map(str,(t1,s1))),
                original_profile=list(map(str,p)),new_profile=list(map(str,q)),
                exact_responses=list(map(str,y[2:])),status='PASS')

def numerical(p):
    pair=[.05,.369]
    J=jac(pair,p)
    _,_,vh=np.linalg.svd(J,full_matrices=True)
    assert np.linalg.norm(J@vh[-1])<1e-12
    base=np.array([row(u)@N for u in pair])
    exact_alpha_rms=sigma*np.linalg.norm(np.linalg.inv(base),'fro')
    prior_rms=profile_rms(pair,p,True)
    # The rank-one shared systematic covariance is exactly the marginalized
    # Gaussian prior for alpha in the first-order linear model.
    v=J[:,2];C=sigma**2*np.eye(2)+alpha_sd**2*np.outer(v,v)
    marginal=np.linalg.inv(base.T@np.linalg.solve(C,base))
    assert np.isclose(np.sqrt(np.trace(marginal)),prior_rms,rtol=1e-8)
    opt=minimize_scalar(lambda z:profile_rms([*pair,z],p),bounds=(.05,.95),
                        method='bounded',options={'xatol':1e-10})
    candidates=[(.05,profile_rms([*pair,.05],p)),(.95,profile_rms([*pair,.95],p)),
                (float(opt.x),float(opt.fun))]
    third,third_rms=min(candidates,key=lambda x:x[1])
    de=differential_evolution(lambda x:profile_rms(sorted(x),p),
                              [(.05,.95)]*3,seed=20261107,popsize=18,
                              tol=3e-9,maxiter=1100)
    assert de.success
    return dict(two_probe_rank=2,alpha_known_rms=float(exact_alpha_rms),
                alpha_prior_5pct_rms=prior_rms,
                third_probe_at_fixed_pair=float(third),
                three_probe_alpha_free_rms=third_rms,
                global_three_probe_candidate=sorted(map(float,de.x)),
                global_three_probe_rms=float(de.fun),
                nuisance_correlated_covariance=C.tolist())

def main():
    profiles={'uniform':[.25]*4,
              'plus':[11/60,7/15,1/60,1/3],
              'minus':[19/60,1/30,29/60,1/6]}
    out={'scope':'toy local linearization, no experimental calibration',
         'noise_sigma':sigma,'alpha_prior_sd':alpha_sd,
         'exact_counterexample':exact_checks(),
         'results':{name:numerical(np.array(p)) for name,p in profiles.items()}}
    path=Path('docs/pad_calibration_results.json')
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(out,indent=2)+'\n')
    print('Exact calibration ambiguity PASS; independent Fisher covariance PASS')
    for name,v in out['results'].items():
        print(name,'third',round(v['third_probe_at_fixed_pair'],6),
              'three-probe RMS',round(v['three_probe_alpha_free_rms'],6),
              'two-probe uncertain alpha RMS',round(v['alpha_prior_5pct_rms'],6))
    print('Saved',path)

if __name__=='__main__': main()
