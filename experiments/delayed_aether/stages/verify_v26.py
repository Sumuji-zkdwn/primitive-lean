#!/usr/bin/env python3
"""v26: ADM canonical momenta of scalar-tensor memory coupling, plus Bianchi I IVP.
All physical parameters are dimensionless model parameters. No Einstein-gravity emergence claimed.
"""
import os, json, csv
from pathlib import Path
os.environ.setdefault('XLA_FLAGS', '--xla_cpu_multi_thread_eigen=false intra_op_parallelism_threads=1')
os.environ.setdefault('OMP_NUM_THREADS','1')
import numpy as np
import sympy as sp
import jax
jax.config.update('jax_enable_x64', True)
import jax.numpy as jnp
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ROOT=Path(__file__).resolve().parent

def symbolic_checks():
    F,P,Z,A,s,vq,n=sp.symbols('F P Z A s vq n', nonzero=True, real=True)
    k=sp.symbols('k1 k2 k3',real=True)
    K=sum(k)
    L=sp.expand(s*(F/2*(sum(t*t for t in k)-K*K)-P*K*n+Z*n*n/2+A*vq*vq/2))
    pi=[sp.diff(L,x)/2 for x in k]  # pi_i^i; conjugate to beta_i=2pi_i
    pc=sp.diff(L,n)
    pq=sp.diff(L,vq)
    pitr=sum(pi)
    D=Z+3*P**2/(2*F)
    ham= 2/(s*F)*sum((x-pitr/3)**2 for x in pi)-pitr**2/(3*s*F)+(pc-P/F*pitr)**2/(2*s*D)+pq**2/(2*s*A)
    leg=2*sum(x*y for x,y in zip(pi,k))+pc*n+pq*vq-L
    assert sp.simplify(sp.cancel(leg-ham))==0, 'Legendre identity failed'
    hess=sp.hessian(L, (*k,n))
    determinant=sp.factor(hess.det())
    assert sp.simplify(determinant+2*s**4*F**3*D)==0
    # Canonical transformation on (gamma,pi) plus chi scalar: lapse/shift NOT included.
    chi=sp.symbols('chi',real=True)
    g=sp.symbols('g0 g1 g2',positive=True)
    p=sp.symbols('p0 p1 p2',real=True)
    pchi=sp.symbols('pchi',real=True)
    ff=2+sp.Rational(7,20)*sp.tanh(chi)
    fp=sp.diff(ff,chi)
    tr=sum(g[i]*p[i] for i in range(3))
    qtilde=[ff*g0 for g0 in g]+[chi]
    ptilde=[x/ff for x in p]+[pchi-fp/ff*tr]
    qs=[*g,chi]; ps=[*p,pchi]
    def PB(x,y):
        return sp.simplify(sum(sp.diff(x,qs[i])*sp.diff(y,ps[i])-sp.diff(x,ps[i])*sp.diff(y,qs[i]) for i in range(4)))
    defects=[]
    for i in range(4):
        for j in range(4):
            defects.extend([PB(qtilde[i],qtilde[j]), PB(ptilde[i],ptilde[j]),
                            PB(qtilde[i],ptilde[j])-int(i==j)])
    assert all(sp.simplify(x)==0 for x in defects), f'not canonical: {defects}'
    # nontrivial mixed momentum / shift: derive exactly from Lagrangian
    assert sp.simplify(pc-s*(Z*n-P*K))==0
    assert sp.simplify(pitr-s*(-F*K-sp.Rational(3,2)*P*n))==0
    out={
       'legendre_identity_exact':True,
       'kinetic_hessian_determinant':str(determinant),
       'hessian_nondegenerate_condition':'F != 0 and D=Z+3*Fprime^2/(2F) != 0',
       'spatial_sector_symplectic_bracket_defect_count':sum(x!=0 for x in defects),
       'spatial_sector_symplectic_entries_tested':len(defects),
       'caveat':'This is a spatial canonical sector transformation; lapse/shift phase space not transformed.'
    }
    return out

@jax.jit
def H_true(y):
    beta=y[:3]; chi=y[3]; q=y[4]; Pi=y[5:8]; pc=y[8]; pq=y[9]
    vol=jnp.exp(jnp.sum(beta))
    F=2+.35*jnp.tanh(chi)
    Fp=.35*(1-jnp.tanh(chi)**2)
    ylag=(q-chi)
    A=1+1.8*jnp.tanh(ylag/.5)**2
    D=1+1.5*Fp*Fp/F
    p=Pi/2
    ptr=jnp.sum(p)
    tf=jnp.sum((p-ptr/3)**2)
    V=.5*ylag**2+.07*chi**2
    return 2*tf/(vol*F)-ptr**2/(3*vol*F)+(pc-Fp/F*ptr)**2/(2*vol*D)+pq**2/(2*vol*A)+vol*V

@jax.jit
def H_naive(y):
    beta=y[:3]; chi=y[3]; q=y[4]; Pi=y[5:8]; pc=y[8]; pq=y[9]
    vol=jnp.exp(jnp.sum(beta))
    F=2+.35*jnp.tanh(chi)
    A=1+1.8*jnp.tanh((q-chi)/.5)**2
    p=Pi/2; ptr=jnp.sum(p); tf=jnp.sum((p-ptr/3)**2)
    V=.5*(q-chi)**2+.07*chi**2
    return 2*tf/(vol*F)-ptr**2/(3*vol*F)+pc**2/(2*vol)+pq**2/(2*vol*A)+vol*V

jgrad= jax.jit(jax.grad(H_true))
ngrad= jax.jit(jax.grad(H_naive))
@jax.jit
def rhs_true(y):
    d=jgrad(y)
    return jnp.concatenate((d[5:],-d[:5]))
@jax.jit
def rhs_naive(y):
    d=ngrad(y)
    return jnp.concatenate((d[5:],-d[:5]))

def initial_state():
    beta=np.zeros(3)
    chi=-.16; q=.34; dc=.24; dq=-.45
    sh=np.array([.06,-.045,-.015])
    F=2+.35*np.tanh(chi); Fp=.35/np.cosh(chi)**2
    A=1+1.8*np.tanh((q-chi)/.5)**2
    V=.5*(q-chi)**2+.07*chi**2
    RHS=.5*F*sum(sh*sh)+.5*dc*dc+.5*A*dq*dq+V
    H=(-3*Fp*dc + np.sqrt((3*Fp*dc)**2+12*F*RHS))/(6*F)
    K=3*H
    Ki=H+sh
    Pi=np.array([F*(v-K)-Fp*dc for v in Ki])
    pc=dc-Fp*K
    pq=A*dq
    state=np.array([*beta,chi,q,*Pi,pc,pq],dtype=float)
    assert abs(float(H_true(jnp.array(state))))<2e-13
    return state, {'initial_mean_expansion':float(H),'initial_lag':q-chi,
                   'initial_hardness':float(A), 'initial_curvature_scalar_R3':0.0,
                   'initial_chi_momentum':float(pc),
                   'naive_chi_momentum_sqrtgamma_Z_nchi':float(dc),
                   'initial_chi_momentum_shift':float(pc-dc)}

def rk4(y0,dt,T,rhs):
    count=int(round(T/dt)); assert abs(count*dt-T)<1e-10
    y=jnp.array(y0); out=np.zeros((count+1,len(y0)))
    out[0]=np.asarray(y)
    for t in range(count):
        k1=rhs(y); k2=rhs(y+dt*k1/2); k3=rhs(y+dt*k2/2); k4=rhs(y+dt*k3)
        y=y+dt*(k1+2*k2+2*k3+k4)/6
        out[t+1]=np.asarray(y)
    return np.linspace(0,T,count+1),out

def to_csv(name,header,rows):
    with open(ROOT/name,'w',newline='') as f:
        w=csv.writer(f);w.writerow(header);w.writerows(rows)

def numerics():
    y0,initial=initial_state()
    T=3.2
    runs={}; stats={}
    for dt in (.08,.04,.02):
        ts,xx=rk4(y0,dt,T,rhs_true)
        C=np.array([float(H_true(jnp.array(y))) for y in xx]);
        assert np.all(np.isfinite(xx))
        stats[str(dt)]={'max_abs_constraint':float(np.max(np.abs(C))),
                        'endpoint_state':xx[-1].tolist(),'endpoint_constraint':float(C[-1])}
        runs[dt]=(ts,xx,C)
    # independent scipy DOP853 reference uses exactly same analytic gradient but different integrator
    from scipy.integrate import solve_ivp
    sol=solve_ivp(lambda t,y: np.asarray(rhs_true(jnp.array(y))), (0,T), y0, method='DOP853',rtol=5e-13,atol=2e-14)
    assert sol.success,sol.message
    ref=sol.y[:,-1]
    for dt,(ts,xx,C) in runs.items():
        stats[str(dt)]['endpoint_error_vs_DOP853']=float(np.linalg.norm(xx[-1]-ref))
    ratio=stats['0.08']['endpoint_error_vs_DOP853']/stats['0.04']['endpoint_error_vs_DOP853']
    ratio2=stats['0.04']['endpoint_error_vs_DOP853']/stats['0.02']['endpoint_error_vs_DOP853']
    assert 9<ratio<23 and 9<ratio2<23,(ratio,ratio2)
    ts,x,C =runs[.02]
    F=2+.35*np.tanh(x[:,3]); Fp=.35/np.cosh(x[:,3])**2
    lag=x[:,4]-x[:,3]
    stiffness=1+1.8*np.tanh(lag/.5)**2
    volume=np.exp(np.sum(x[:,:3],axis=1))
    trace_pi=np.sum(x[:,5:8],axis=1)/2
    mixed=x[:,8]-Fp/F*trace_pi
    # naive dynamics, compare to TRUE constraint, not as a proof of 3+1 closure
    tna,xna=rk4(y0,.02,T,rhs_naive)
    Ctrue_on_naive=np.array([float(H_true(jnp.array(y))) for y in xna]);
    naive_loss=float(np.max(np.abs(Ctrue_on_naive)))
    assert naive_loss>1e-4,naive_loss
    to_csv('bianchi_evolution_v26.csv', ['t','beta1','beta2','beta3','chi','q','Pbeta1','Pbeta2','Pbeta3','pchi','pq','constraint_correct','F','Fprime','A','lag','pchi_shifted','volume'],
           [[ts[i],*x[i],C[i],F[i],Fp[i],stiffness[i],lag[i],mixed[i],volume[i]] for i in range(len(ts))])
    to_csv('naive_comparison_v26.csv',['t','true_constraint_correct_flow','true_constraint_under_naive_flow','naive_constraint_under_naive_flow'],
           [[ts[i],C[i],Ctrue_on_naive[i],float(H_naive(jnp.array(xna[i])))] for i in range(len(ts))])
    to_csv('integration_convergence_v26.csv',['dt','endpoint_error_vs_DOP853','max_abs_constraint','endpoint_constraint'],
           [[dt, stats[str(dt)]['endpoint_error_vs_DOP853'],stats[str(dt)]['max_abs_constraint'],stats[str(dt)]['endpoint_constraint']] for dt in (.08,.04,.02)])
    plt.rcParams.update({'font.size':10})
    fig,axs=plt.subplots(3,1,figsize=(9.0,8.8),sharex=True)
    axs[0].plot(ts, x[:,3],label='Memory field χ'); axs[0].plot(ts, x[:,4],label='Local-state proxy q');axs[0].plot(ts,lag,label='q−χ',linestyle='--');axs[0].legend(ncol=3,fontsize=8);axs[0].set_ylabel('Scalar states')
    axs[1].plot(ts,stiffness,label='A(q−χ)');axs[1].plot(ts,F,label='F(χ), curvature coupling'); axs[1].legend();axs[1].set_ylabel('Coupling coefficient')
    axs[2].plot(ts,x[:,0],label='β₁');axs[2].plot(ts,x[:,1],label='β₂');axs[2].plot(ts,x[:,2],label='β₃');axs[2].legend(ncol=3,fontsize=8);axs[2].set_ylabel('Log scale');axs[2].set_xlabel('Model time')
    fig.suptitle('Covariant memory–geometry minisuperspace, self-consistent evolution');fig.tight_layout();fig.savefig(ROOT/'coupled_dynamics_v26.png',dpi=175);plt.close(fig)
    fig, ax=plt.subplots(figsize=(9,4.8))
    ax.plot(ts,C,label='Correct Hamiltonian, correct evolution')
    ax.plot(ts,Ctrue_on_naive,label='Correct constraint evaluated on naive evolution')
    ax.axhline(0,lw=0.7,color='grey'); ax.set(xlabel='Model time',ylabel='True Hamiltonian constraint',title='Effect of dropping the curvature–memory momentum mixing')
    ax.legend();fig.tight_layout();fig.savefig(ROOT/'constraint_comparison_v26.png',dpi=175);plt.close(fig)
    fig,ax=plt.subplots(figsize=(8.4,5))
    ax.loglog([.08,.04,.02],[stats[str(dt)]['endpoint_error_vs_DOP853'] for dt in (.08,.04,.02)],'o-',label='RK4 endpoint error')
    ax.set(xlabel='Time step',ylabel='L2 error vs high-accuracy DOP853',title='Integration refinement (expected 4th order)');ax.legend();fig.tight_layout();fig.savefig(ROOT/'integrator_refinement_v26.png',dpi=175);plt.close(fig)
    return {'initial':initial,'integration':stats,'RK4_ratio_coarse_medium':float(ratio),'RK4_ratio_medium_fine':float(ratio2),
            'true_flow_max_abs_constraint_dt_0p02':float(np.max(np.abs(C))),
            'true_constraint_on_naive_flow_max_abs':naive_loss,
            'max_stiffness':float(stiffness.max()),'min_F':float(F.min()),'min_D':float(np.min(1+1.5*Fp**2/F)),
            'final_lag':float(lag[-1]),'final_mean_volume':float(volume[-1]),
            'scope':'Homogeneous Bianchi I Hamiltonian constraint, not full inhomogeneous Dirac algebra.'}

if __name__=='__main__':
   sym=symbolic_checks(); print('symbolic:',sym)
   num=numerics(); print('numerics:',json.dumps({k:v for k,v in num.items() if k!='integration'},indent=2))
   output={'symbolic':sym,'numeric':num}
   (ROOT/'audit_v26.json').write_text(json.dumps(output,indent=2,ensure_ascii=False)+'\n')
   print('PASS: symbolic identities, canonical brackets, Bianchi I IVP and convergence')