#!/usr/bin/env python3
"""v27: Inhomogeneous 1D slice of 3+1 scalar-tensor ADM with full 5 canonical pairs.

The finite difference bracket approximates (not exactly realizes) the hypersurface deformation algebra.
Run: python verify_v27.py
"""
from __future__ import annotations
import os, json, csv
from pathlib import Path
import numpy as np
import sympy as sp
import jax
jax.config.update('jax_enable_x64', True)
import jax.numpy as jnp
from jax import grad, jit
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
BASE=Path(__file__).resolve().parent

def symbolic_check():
    F,X,b,c,n,np_,W,k = sp.symbols('F X b c n np W k', real=True, nonzero=True)
    r=X/F
    D=1+sp.Rational(3,2)*X**2/(F*k**2)
    J=-W*(n*(F*b*c+X*(b+c))+np_*(F*(b+c)+X))+W*n*k**2/2
    E=-W*(n*F*(b+r/2)*(c+r/2)+(np_*F+n*X/2)*(b+c+r))+W*n*D*k**2/2
    diff=sp.factor(E-J)
    assert diff==0, diff
    Pa,Pb,Pc,pchi,Fchi,dchi,da,db,dc=sp.symbols('Pa Pb Pc pchi Fchi dchi da db dc')
    lhs=Pa*da+Pb*db+Pc*dc+pchi*dchi
    rhs=Pa*(da+Fchi/(2*F)*dchi)+Pb*(db+Fchi/(2*F)*dchi)+Pc*(dc+Fchi/(2*F)*dchi)+(pchi-Fchi*(Pa+Pb+Pc)/(2*F))*dchi
    assert sp.simplify(lhs-rhs)==0
    return {'einstein_jordan_hamiltonian_identity':str(diff),'spatial_canonical_one_form_identity':str(sp.simplify(lhs-rhs))}

def deriv(v,dx):
    return (jnp.roll(v,-1,axis=-1)-jnp.roll(v,1,axis=-1))/(2*dx)

def hamiltonian(fields,mom,smear,dx,variant='correct'):
    alpha,beta,gamma,chi,q=fields
    Pa,Pb,Pc,pchi,pq=mom
    V3=jnp.exp(alpha+beta+gamma)
    W=jnp.exp(beta+gamma-alpha)
    F=2.0+0.35*jnp.tanh(chi)
    Fc=0.35/(jnp.cosh(chi)**2)
    D=1.+1.5*Fc**2/F
    Amem=1.+1.8*jnp.tanh((q-chi)/0.5)**2
    potential=0.5*(q-chi)**2+0.07*chi**2
    psum=Pa+Pb+Pc
    grav_kin=(Pa*Pa+Pb*Pb+Pc*Pc-0.5*psum*psum)/(2.*F*V3)
    mix=pchi-Fc*psum/(2*F) if variant!='omit_mixing' else pchi
    chi_kin=mix*mix/(2.*V3*D)
    q_kin=pq*pq/(2.*V3*Amem)
    a_x,b_x,c_x,chi_x,q_x=deriv(fields,dx)
    Fx=Fc*chi_x
    spatial_n=(-W*(F*b_x*c_x+Fx*(b_x+c_x)) +0.5*W*(chi_x**2+Amem*q_x**2)+V3*potential)
    spatial_np=-W*(F*(b_x+c_x)+Fx)
    integrand=smear*(grav_kin+chi_kin+q_kin+spatial_n)+deriv(smear,dx)*spatial_np
    return dx*jnp.sum(integrand)

def poiss(fields,mom,N,M,dx,variant='correct'):
    gN=grad(lambda f,p: hamiltonian(f,p,N,dx,variant),argnums=(0,1))
    gM=grad(lambda f,p: hamiltonian(f,p,M,dx,variant),argnums=(0,1))
    FN,PN=gN(fields,mom)
    FM,PM=gM(fields,mom)
    # canonical momentum samples refer to continuous densities; hence 1/dx.
    return jnp.sum(FN*PM-PN*FM)/dx

def diffeo_rhs(fields,mom,N,M,dx):
    a=fields[0]
    beta_ginv=jnp.exp(-2*a)
    v=beta_ginv*(N*deriv(M,dx)-M*deriv(N,dx))
    grad_fields=deriv(fields,dx)
    Pα=mom[0]
    Ddens=jnp.sum(mom*grad_fields,axis=0)-deriv(Pα,dx)
    return dx*jnp.sum(v*Ddens)

def make_state(n):
    x=jnp.linspace(0.,2*np.pi,n,endpoint=False)
    dx=float(2*np.pi/n)
    a=.12*jnp.sin(x+.1)+.04*jnp.cos(2*x-.6)
    b=-.11*jnp.cos(x+.3)+.06*jnp.sin(3*x)
    c=.09*jnp.sin(2*x+.5)+.035*jnp.cos(x-.9)
    chi=.27*jnp.sin(x-.2)+.17*jnp.cos(2*x+.1)
    q=.20*jnp.cos(x+.4)+.28*jnp.sin(3*x-.1)
    Pa=.22+.16*jnp.sin(x+.35)+.08*jnp.cos(3*x-.3)
    Pb=-.10+.17*jnp.cos(2*x+.2)+.13*jnp.sin(x-.5)
    Pc=.08+.14*jnp.sin(3*x+.3)+.05*jnp.cos(x+.9)
    pchi=.26+.25*jnp.sin(2*x-.7)+.16*jnp.cos(x-.1)
    pq=-.15+.23*jnp.cos(3*x+.4)+.12*jnp.sin(x+.5)
    N=1+.31*jnp.cos(x+.25)+.13*jnp.sin(2*x+.7)+.07*jnp.cos(4*x)
    M=.90+.27*jnp.sin(x+.12)+.11*jnp.cos(3*x-.2)+.09*jnp.sin(4*x+.3)
    return jnp.stack([a,b,c,chi,q]),jnp.stack([Pa,Pb,Pc,pchi,pq]),N,M,dx

@jit
def _pair_cache(f,p,N,M,dx):
    return jnp.array([poiss(f,p,N,M,dx,'correct'),poiss(f,p,N,M,dx,'omit_mixing'),diffeo_rhs(f,p,N,M,dx)])

def compare_einstein_numerically(fields,mom,N,dx):
    # Eigenframe Hamiltonian in first-derivative integrated form; includes E-frame scalar metric D/F, A/F.
    a,b,c,chi,q=fields
    Pa,Pb,Pc,pchi,pq=mom
    F=2+.35*jnp.tanh(chi)
    Fc=.35/jnp.cosh(chi)**2
    D=1+1.5*Fc**2/F
    Amem=1+1.8*jnp.tanh((q-chi)/.5)**2
    vol=jnp.exp(a+b+c)*F**1.5
    Wx=jnp.exp(b+c-a)*jnp.sqrt(F)
    q_new=jnp.stack([a+.5*jnp.log(F),b+.5*jnp.log(F),c+.5*jnp.log(F),chi,q])
    pe=pchi-Fc*(Pa+Pb+Pc)/(2*F)
    kin=(Pa**2+Pb**2+Pc**2-0.5*(Pa+Pb+Pc)**2)/(2*vol)
    kin+=pe**2/(2*vol*(D/F))+pq**2/(2*vol*(Amem/F))
    _,bx,cx,chix,qx=deriv(q_new,dx)
    potential=.5*(q-chi)**2+.07*chi**2
    spatial=-Wx*bx*cx+.5*Wx*((D/F)*chix**2+(Amem/F)*qx**2)+vol*(potential/F**2)
    spatial_smear_prime=-Wx*(bx+cx)
    NE=jnp.sqrt(F)*N
    HE=dx*jnp.sum(NE*(kin+spatial)+deriv(NE,dx)*spatial_smear_prime)
    HJ=hamiltonian(fields,mom,N,dx)
    return float(HJ),float(HE),float(HE-HJ)

def independent_grad_check(n=16):
    # Numerically differentiate small subset in raw NumPy (not JAX), checking first variation.
    f,p,N,M,dx=make_state(n)
    rawf=np.array(f);rawp=np.array(p);rawN=np.array(N)
    dHf,dHp=grad(lambda x,y:hamiltonian(x,y,N,dx),argnums=(0,1))(f,p)
    out=[]
    eps=1e-6
    for typ,i,k in [('field',0,3),('field',3,5),('field',4,1),('mom',0,8),('mom',3,2),('mom',4,12)]:
        fplus=rawf.copy(); fminus=rawf.copy(); pplus=rawp.copy();pminus=rawp.copy()
        if typ=='field': fplus[i,k]+=eps;fminus[i,k]-=eps
        else: pplus[i,k]+=eps;pminus[i,k]-=eps
        plus=float(hamiltonian(jnp.array(fplus),jnp.array(pplus),N,dx))
        minus=float(hamiltonian(jnp.array(fminus),jnp.array(pminus),N,dx))
        fd=(plus-minus)/(2*eps)
        ad=float(dHf[i,k] if typ=='field' else dHp[i,k])
        out.append(dict(variable=typ,index=i,site=k,finite_difference=fd,autodiff=ad,abs_error=abs(fd-ad)))
    return out


def main():
    print('Symbolic identity checks...',flush=True)
    proof=symbolic_check()
    print('1D full canonical off-shell brackets...',flush=True)
    rows=[]
    for n in [24,32,48,64,96,128,192,256]:
        f,p,N,M,dx=make_state(n)
        bracket,bad,target=map(float,_pair_cache(f,p,N,M,dx))
        HJ,HE,deltaH=compare_einstein_numerically(f,p,N,dx)
        rows.append(dict(n=n,dx=dx,bracket=bracket,momentum_constraint=target,error=bracket-target,
                         relative_error=abs(bracket-target)/max(abs(target),1e-15),
                         bad_bracket=bad,bad_error=bad-target,HE_minus_HJ=deltaH,
                         HJ=HJ,HE=HE))
        print(f' n={n:<3} bracket={bracket:.10f} rhs={target:.10f} err={bracket-target:+.3e} bad={bad-target:+.3e} HE-HJ={deltaH:+.3e}',flush=True)
    assert abs(rows[-1]['error']) < abs(rows[-3]['error']) / 2
    assert abs(rows[-1]['bad_error']) > abs(rows[-1]['error'])*5
    checks=independent_grad_check()
    print('independent finite differences max error',max(o['abs_error'] for o in checks),flush=True)
    with open(BASE/'bracket_convergence_v27.csv','w',newline='') as fp:
        writer=csv.DictWriter(fp,fieldnames=list(rows[0]));writer.writeheader();writer.writerows(rows)
    with open(BASE/'gradient_checks_v27.csv','w',newline='') as fp:
        writer=csv.DictWriter(fp,fieldnames=list(checks[0]));writer.writeheader();writer.writerows(checks)
    def scatter_log(ax,field,label,color):
        ax.loglog([row['dx'] for row in rows],[abs(row[field]) for row in rows], 'o-',label=label,color=color)
    fig,ax=plt.subplots(figsize=(8.0,4.8))
    scatter_log(ax,'error','Correct nonminimal canonical mixing','tab:blue')
    scatter_log(ax,'bad_error','Omit momentum mixing (incorrect)','tab:red')
    ax.loglog([row['dx'] for row in rows],[abs(rows[-1]['error'])*(row['dx']/rows[-1]['dx'])**2 for row in rows],'--',label='quadratic convergence',color='gray')
    ax.set(xlabel='Grid spacing Δx',ylabel='Absolute off-shell bracket residual',title='Inhomogeneous scalar–tensor constraint bracket (5 canonical pairs)')
    ax.legend(fontsize=9);ax.grid(True,which='both',alpha=.2);fig.tight_layout();fig.savefig(BASE/'bracket_convergence_v27.png',dpi=175);plt.close(fig)
    fig,ax=plt.subplots(figsize=(8,4.8))
    scatter_log(ax,'HE_minus_HJ','Conformal-frame Hamiltonian difference','tab:purple')
    ax.set(xlabel='Grid spacing Δx',ylabel='|H_E[√F N] − H_J[N]|',title='Conformal canonical equivalence, discrete derivative')
    ax.grid(True,which='both',alpha=.2);ax.legend();fig.tight_layout();fig.savefig(BASE/'frame_identity_convergence_v27.png',dpi=175);plt.close(fig)
    summary={'symbolic':proof,'finite_grid':rows,'gradient_checks':checks,
             'convergence_ratio_128_to_256':abs(rows[-2]['error'])/abs(rows[-1]['error']),
             'bad_limit_estimate':rows[-1]['bad_error'],
             'notes':'Symmetry reduced 1D-inhomogeneous 3+1 plane-diagonal slice; finite central differences, not full 3D unconstrained Einstein theory.'}
    (BASE/'audit_v27.json').write_text(json.dumps(summary,indent=2,ensure_ascii=False)+'\n')
    print('passed',flush=True)
if __name__=='__main__':main()

# Extra verification callable independently of the main run:
def direct_curvature_check(n):
    f,p,N,M,dx=make_state(n)
    a,b,c,chi,q=f
    W=jnp.exp(b+c-a); vol=jnp.exp(a+b+c)
    F=2+.35*jnp.tanh(chi)
    ax,bx,cx=deriv(jnp.stack([a,b,c]),dx)
    bxx=deriv(bx,dx); cxx=deriv(cx,dx)
    Fx=deriv(F,dx); Fxx=deriv(Fx,dx)
    R3=-2*jnp.exp(-2*a)*(bxx+cxx+bx*bx+cx*cx+bx*cx-ax*(bx+cx))
    lapF=jnp.exp(-2*a)*(Fxx+(bx+cx-ax)*Fx)
    direct=dx*jnp.sum(N*vol*(-F*R3/2+lapF))
    # Independently assembled expression with N' and exact derivative of F.
    Fx_code=.35/(jnp.cosh(chi)**2)*deriv(chi,dx)
    integrated=dx*jnp.sum(-N*W*(F*bx*cx+Fx_code*(bx+cx))-deriv(N,dx)*W*(F*(bx+cx)+Fx_code))
    return float(direct),float(integrated),float(direct-integrated)


def supplemental_tests():
    rows=[]
    for n in [32,64,128,256]:
        direct,integrated,delta=direct_curvature_check(n)
        rows.append(dict(n=n,direct_curvature=direct,integrated_by_parts=integrated,difference=delta))
        print(' curvature',n,'direct',direct,'integrated',integrated,'difference',delta,flush=True)
    assert abs(rows[-1]['difference']) < abs(rows[-2]['difference'])/3.5
    with open(BASE/'curvature_crosscheck_v27.csv','w',newline='') as fp:
        wr=csv.DictWriter(fp,list(rows[0]));wr.writeheader();wr.writerows(rows)
    # Distinct inhomogeneous configurations; compare bracket closure as dx decreases.
    adversarial=[]
    for variant in ['reverse_memory','shifted_momenta','amplified_shear']:
        for n in [64,128,256]:
            f,p,N,M,dx=make_state(n)
            if variant=='reverse_memory':
                f=f.at[3].set(-f[3]+.11*jnp.sin(5*jnp.linspace(0,2*jnp.pi,n,endpoint=False)))
                p=p.at[3].set(-.7*p[3]+.09*jnp.cos(2*jnp.linspace(0,2*jnp.pi,n,endpoint=False)))
            elif variant=='shifted_momenta':
                p=jnp.roll(p,n//7,axis=-1)
            elif variant=='amplified_shear':
                f=f.at[1].set(f[1]*1.6)
                f=f.at[2].set(f[2]*1.5)
            proper,bad,target=map(float,_pair_cache(f,p,N,M,dx))
            adversarial.append(dict(variant=variant,n=n,correct_residual=proper-target,incorrect_residual=bad-target))
            print(' variant',variant,n,'correct',proper-target,'incorrect',bad-target,flush=True)
    for name in ('reverse_memory','shifted_momenta','amplified_shear'):
        s=[r for r in adversarial if r['variant']==name]
        assert abs(s[-1]['correct_residual']) < abs(s[0]['correct_residual'])/12
        assert abs(s[-1]['incorrect_residual']) > abs(s[-1]['correct_residual'])*5
    with open(BASE/'other_profiles_v27.csv','w',newline='') as fp:
        wr=csv.DictWriter(fp,list(adversarial[0]));wr.writeheader();wr.writerows(adversarial)
    return rows,adversarial

if __name__=='__main__':
    r,a=supplemental_tests()
    audit=json.loads((BASE/'audit_v27.json').read_text())
    audit['direct_ricci_laplacian_checks']=r
    audit['additional_off_shell_profiles']=a
    (BASE/'audit_v27.json').write_text(json.dumps(audit,indent=2,ensure_ascii=False)+'\n')