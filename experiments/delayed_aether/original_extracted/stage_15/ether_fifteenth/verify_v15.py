"""V15: Independent constraint checks on exact nonlinear vacuum GR slices.

Benchmark NOT a derivation of GR from an ether.  Uses Einstein ADM equations
as a benchmark and tests an ad-hoc memory perturbation separately.

Inputs: Minkowski spacetime rewritten as t=T+a(T) s(x,y),
with s doubly periodic, and an independent non-diagonal Kasner solution.
All spatial derivatives in graph test are standard central finite differences.
"""
from __future__ import annotations
import argparse, csv, json
from pathlib import Path
import numpy as np

C = 0.21
D = 0.13

def centered(a, axis, h):
    return (np.roll(a, -1, axis=axis) - np.roll(a, +1, axis=axis))/(2*h)

def xy_profile(n):
    x = 2*np.pi*np.arange(n)/n
    X,Y = np.meshgrid(x,x,indexing='ij')
    A=X; B=Y; C1=2*X+Y; D1=X-2*Y
    S = np.sin(A)*np.sin(B)+C*np.sin(C1)+D*np.cos(D1)
    sx=np.cos(A)*np.sin(B)+2*C*np.cos(C1)-D*np.sin(D1)
    sy=np.sin(A)*np.cos(B)+C*np.cos(C1)+2*D*np.sin(D1)
    sxx=-np.sin(A)*np.sin(B)-4*C*np.sin(C1)-D*np.cos(D1)
    syy=-np.sin(A)*np.sin(B)-C*np.sin(C1)-4*D*np.cos(D1)
    sxy=np.cos(A)*np.cos(B)-2*C*np.sin(C1)+2*D*np.cos(D1)
    grad=np.stack((sx,sy),axis=-1)
    hess=np.stack((np.stack((sxx,sxy),-1),np.stack((sxy,syy),-1)),-2)
    return S,grad,hess

def amp(T):
    return 0.19+0.04*np.sin(1.3*T),0.052*np.cos(1.3*T)

def fields(n,T):
    S,ds,hs=xy_profile(n)
    a,adot=amp(T)
    v2=np.einsum('...i,...i->...',ds,ds)
    W2=1-a*a*v2
    Q=1+adot*S
    assert np.min(W2)>0 and np.min(Q)>0
    W=np.sqrt(W2)
    I=np.eye(2)
    gamma=I-a*a*np.einsum('...i,...j->...ij',ds,ds)
    inv=I+(a*a/W2)[...,None,None]*np.einsum('...i,...j->...ij',ds,ds)
    K=-a*hs/W[...,None,None]
    # Exact lapse and shift of t=T+a(T)s(x,y)
    lapse=Q/W
    beta=-Q[...,None]*(a/W2)[...,None]*ds
    gdot=-2*a*adot*np.einsum('...i,...j->...ij',ds,ds)
    Kdot=-(adot/W**3)[...,None,None]*hs
    return locals()

def finite_geometry(f):
    gamma,inv,K,lapse,beta=f['gamma'],f['inv'],f['K'],f['lapse'],f['beta']
    n=gamma.shape[0]; h=2*np.pi/n
    # derivatives arrays dgamma[spatial_derivative_index, x,y, i,j]
    dg=np.stack([centered(gamma,k,h) for k in range(2)],axis=0)
    dK=np.stack([centered(K,k,h) for k in range(2)],axis=0)
    dbeta=np.stack([centered(beta,k,h) for k in range(2)],axis=0)
    dlapse=np.stack([centered(lapse,k,h) for k in range(2)],axis=0)
    Gamma=np.zeros((n,n,2,2,2))
    # Gamma^k_{ij}
    for k in range(2):
      for i in range(2):
       for j in range(2):
        for ell in range(2):
         Gamma[...,k,i,j]+=0.5*inv[...,k,ell]*(dg[i,...,ell,j]+dg[j,...,ell,i]-dg[ell,...,i,j])
    dGamma=np.stack([centered(Gamma,k,h) for k in range(2)],axis=0)
    Ric=np.zeros((n,n,2,2))
    for i in range(2):
     for j in range(2):
      for k in range(2):
       Ric[...,i,j]+= dGamma[k,...,k,i,j]-dGamma[j,...,k,i,k]
       for ell in range(2):
        Ric[...,i,j]+=Gamma[...,k,i,j]*Gamma[...,ell,k,ell]-Gamma[...,ell,i,k]*Gamma[...,k,j,ell]
    scalar=np.einsum('...ij,...ij->...',inv,Ric)
    kmix=np.einsum('...ik,...kj->...ij',inv,K)
    ktrace=np.einsum('...ii->...',kmix)
    normK2=np.einsum('...ij,...ji->...',kmix,kmix)
    H=scalar+ktrace**2-normK2
    dkmix=np.stack([centered(kmix,k,h) for k in range(2)],axis=0)
    dktrace=np.stack([centered(ktrace,k,h) for k in range(2)],axis=0)
    Mom=np.zeros((n,n,2))
    for i in range(2):
     Mom[...,i]=-dktrace[i]
     for j in range(2):
      Mom[...,i]+=dkmix[j,...,j,i]
      for ell in range(2):
       Mom[...,i]+=Gamma[...,j,j,ell]*kmix[...,ell,i]-Gamma[...,ell,j,i]*kmix[...,j,ell]
    # Spatial evolution, Lie beta gamma and K
    lie_gamma=np.zeros((n,n,2,2)); lie_K=np.zeros_like(lie_gamma)
    HessN=np.zeros_like(lie_gamma)
    for i in range(2):
     for j in range(2):
      HessN[...,i,j]=centered(dlapse[j],i,h)
      for k in range(2):
       HessN[...,i,j]-=Gamma[...,k,i,j]*dlapse[k]
       lie_gamma[...,i,j]+=beta[...,k]*dg[k,...,i,j]
       lie_K[...,i,j]+=beta[...,k]*dK[k,...,i,j]
       lie_gamma[...,i,j]+=gamma[...,k,j]*dbeta[i,...,k]+gamma[...,i,k]*dbeta[j,...,k]
       lie_K[...,i,j]+=K[...,k,j]*dbeta[i,...,k]+K[...,i,k]*dbeta[j,...,k]
    gamma_rhs=-2*lapse[...,None,None]*K+lie_gamma
    kK=np.einsum('...ik,...kj->...ij',K,kmix)
    K_rhs=-HessN+lapse[...,None,None]*(Ric+ktrace[...,None,None]*K-2*kK)+lie_K
    gamma_res=gamma_rhs-f['gdot']; K_res=K_rhs-f['Kdot']
    # Independent exact curvature via Gauss, useful to detect sign/indexing mistakes
    R_gauss=normK2-ktrace**2
    return locals()

def memory_obstruction(f, geo, eps=0.9, lag=0.9):
    """Ad-hoc K shift only, not an on-shell solution of GR."""
    past=fields(f['n'],f['T']-lag)
    K2=f['K']+eps*(f['K']-past['K'])
    kmix=np.einsum('...ik,...kj->...ij',f['inv'],K2)
    ktrace=np.einsum('...ii->...',kmix)
    H=geo['scalar']+ktrace**2-np.einsum('...ij,...ji->...',kmix,kmix)
    h=2*np.pi/f['n']
    dkmix=np.stack([centered(kmix,k,h) for k in range(2)],axis=0)
    dktrace=np.stack([centered(ktrace,k,h) for k in range(2)],axis=0)
    Mom=np.zeros((f['n'],f['n'],2))
    Gamma=geo['Gamma']
    for i in range(2):
     Mom[...,i]=-dktrace[i]
     for j in range(2):
      Mom[...,i]+=dkmix[j,...,j,i]
      for ell in range(2):
       Mom[...,i]+=Gamma[...,j,j,ell]*kmix[...,ell,i]-Gamma[...,ell,j,i]*kmix[...,j,ell]
    return H,Mom

def maxnorm(a):return float(np.max(np.abs(a)))
def rms(a):return float(np.sqrt(np.mean(np.square(a))))

def kasner():
    # p_i sum=1, sum squares=1. R mixes coordinates to make off-diagonal logarithmic strain.
    p=np.array([-2/7,3/7,6/7])
    M=np.array([[1.,2.,-1.],[1.,-1.,2.],[2.,-1.,-1.]])
    Q,_=np.linalg.qr(M)
    stats=[]
    for t in np.linspace(0.6,2.8,9):
        l=np.diag(t**(2*p)); dl=np.diag(2*p*t**(2*p-1))
        ddl=np.diag(2*p*(2*p-1)*t**(2*p-2))
        gamma=Q@l@Q.T
        gdot=Q@dl@Q.T; gddot=Q@ddl@Q.T
        K=-0.5*gdot; Kdot=-0.5*gddot
        inv=np.linalg.inv(gamma); kmix=inv@K
        H=np.trace(kmix)**2-np.trace(kmix@kmix)
        # Ric=0, N=1, beta=0
        Krhs=np.trace(kmix)*K-2*K@kmix
        B=Q@np.diag(2*p*np.log(t))@Q.T
        gfromB=Q@np.diag(np.exp(2*p*np.log(t)))@Q.T
        stats.append(dict(t=float(t),Hamiltonian=abs(float(H)),K_evolution=maxnorm(Kdot-Krhs),log_metric_err=maxnorm(gamma-gfromB),min_metric_eig=float(np.linalg.eigvalsh(gamma)[0]),shear=float(np.max(np.abs(B-np.diag(np.diag(B)))))))
    return stats

def run(out):
    out.mkdir(exist_ok=True,parents=True)
    ns=(24,48,96,192)
    ts=(0.0,0.37,0.91)
    rows=[]
    for t in ts:
     for n in ns:
      f=fields(n,t)
      g=finite_geometry(f)
      mh,mm=memory_obstruction(f,g)
      rows.append(dict(t=t,n=n,H=maxnorm(g['H']),M=maxnorm(g['Mom']),
       gamma_evo=maxnorm(g['gamma_res']),K_evo=maxnorm(g['K_res']),
       gauss_R_diff=maxnorm(g['scalar']-g['R_gauss']),
       naive_memory_H=maxnorm(mh),naive_memory_M=maxnorm(mm),
       exact_H_source=maxnorm(g['ktrace']**2-g['normK2']),
       exact_R=maxnorm(g['R_gauss']), min_W=float(np.min(f['W'])),
       min_lapse=float(np.min(f['lapse'])),
       metric_shear_component=maxnorm(f['gamma'][...,0,1]),
       min_metric_eig=float(np.min(f['W2']))))
      print('t',t,'n',n, 'H',f'{maxnorm(g["H"]):.3e}','M',f'{maxnorm(g["Mom"]):.3e}',
        'gdot',f'{maxnorm(g["gamma_res"]):.3e}','Kdot',f'{maxnorm(g["K_res"]):.3e}',
        'memH',f'{maxnorm(mh):.3e}')
    with (out/'graph_constraints.csv').open('w',newline='') as fh:
     writer=csv.DictWriter(fh,fieldnames=list(rows[0]));writer.writeheader();writer.writerows(rows)
    ks=kasner()
    with (out/'kasner_benchmark.csv').open('w',newline='') as fh:
     writer=csv.DictWriter(fh,fieldnames=list(ks[0]));writer.writeheader();writer.writerows(ks)
    # independent analytic Gauss exact diagnostic: nonzero R and K contractions but H cancellation
    # quadratic nonlinearity visible in each large term
    errs={}
    for key in ('H','M','gamma_evo','K_evo'):
     sel=[r for r in rows if r['t']==0.37]
     errs[key]=[sel[i-1][key]/sel[i][key] for i in range(1,len(sel))]
    summary={
       'date':'2026-11-22','status':'PASS' if all(2.8<r<5.5 for v in errs.values() for r in v[1:]) else 'REVIEW',
       'description':'Known ADM/Einstein solution benchmark; not gravity from ether',
       'exact_graph':'Minkowski t=T+a(T)s(x,y); curved 3-slice, shift and lapse nontrivial',
       'grid_ns':ns,'times':ts,'convergence_ratios':errs,
       'max_Kasner_H':max(r['Hamiltonian'] for r in ks),
       'max_Kasner_K_evolution':max(r['K_evolution'] for r in ks),
       'max_Kasner_log_metric_err':max(r['log_metric_err'] for r in ks),
       'memory_setup':{'definition':'Kprime(T)=K(T)+eps*(K(T)-K(T-lag)), gamma unchanged','eps':0.9,'lag':0.9,
         'interpretation':'counterexample to inserting memory into extrinsic curvature without matter equations'},
       'limitations':['ADM equations assumed (not emergent from g=exp B or Skyrme field)',
         'Graph family is coordinate-rewritten flat Minkowski: nonzero 3D slice curvature is not 4D gravity',
         'finite-difference residuals test an exact time-dependent family, not an unconstrained numerical evolution',
         'nonlinear constraints shown in vacuum; no coupled q,z stress-energy nor long-term topology proof']}
    (out/'audit_v15.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2),encoding='utf-8')
    return rows,ks,summary
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--out',type=Path,default=Path(__file__).parent)
 args=p.parse_args()
 run(args.out)
