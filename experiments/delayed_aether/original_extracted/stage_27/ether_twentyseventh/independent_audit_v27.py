#!/usr/bin/env python3
"""Independent NumPy finite-difference Hamiltonian and Poisson-bracket audit of v27.
Does not import the JAX model's Hamiltonian; matches the same analytic equations.
"""
from pathlib import Path
import json
import numpy as np
from importlib.util import spec_from_file_location, module_from_spec
ROOT=Path(__file__).resolve().parent

def D(v,h):return (np.roll(v,-1,axis=-1)-np.roll(v,1,axis=-1))/(2*h)

def h_np(Q,P,smear,h,omit_mixing=False):
    a,b,c,chi,q=Q
    p_a,p_b,p_c,p_chi,p_q=P
    volume=np.exp(a+b+c)
    W=np.exp(b+c-a)
    coupling=2+0.35*np.tanh(chi)
    fchi=0.35/np.cosh(chi)**2
    degen=1+1.5*fchi**2/coupling
    hardness=1+1.8*np.tanh((q-chi)/0.5)**2
    pot=.5*(q-chi)**2+.07*chi**2
    pm=p_a+p_b+p_c
    kg=(p_a**2+p_b**2+p_c**2-.5*pm**2)/(2*coupling*volume)
    shift=0 if omit_mixing else fchi*pm/(2*coupling)
    kin=kg+(p_chi-shift)**2/(2*volume*degen)+p_q**2/(2*volume*hardness)
    ax,bx,cx,chix,qx=D(Q,h)
    fx=fchi*chix
    gsp=-W*(coupling*bx*cx+fx*(bx+cx))+.5*W*(chix**2+hardness*qx**2)+volume*pot
    gb=-W*(coupling*(bx+cx)+fx)
    return float(h*np.sum(smear*(kin+gsp)+D(smear,h)*gb))

def num_grad(Q,P,N,h,omit_mixing=False):
    gq=np.zeros_like(Q);gp=np.zeros_like(P)
    eps=2e-6
    for i in range(Q.shape[0]):
        for j in range(Q.shape[1]):
            Qp=Q.copy(); Qm=Q.copy(); Qp[i,j]+=eps; Qm[i,j]-=eps
            gq[i,j]=(h_np(Qp,P,N,h,omit_mixing)-h_np(Qm,P,N,h,omit_mixing))/(2*eps)
            Pp=P.copy();Pm=P.copy();Pp[i,j]+=eps;Pm[i,j]-=eps
            gp[i,j]=(h_np(Q,Pp,N,h,omit_mixing)-h_np(Q,Pm,N,h,omit_mixing))/(2*eps)
    return gq,gp

def main():
    n=12;x=np.arange(n)*2*np.pi/n;h=2*np.pi/n
    a=.12*np.sin(x+.1)+.04*np.cos(2*x-.6)
    b=-.11*np.cos(x+.3)+.06*np.sin(3*x)
    c=.09*np.sin(2*x+.5)+.035*np.cos(x-.9)
    chi=.27*np.sin(x-.2)+.17*np.cos(2*x+.1)
    q=.20*np.cos(x+.4)+.28*np.sin(3*x-.1)
    Pa=.22+.16*np.sin(x+.35)+.08*np.cos(3*x-.3)
    Pb=-.10+.17*np.cos(2*x+.2)+.13*np.sin(x-.5)
    Pc=.08+.14*np.sin(3*x+.3)+.05*np.cos(x+.9)
    pchi=.26+.25*np.sin(2*x-.7)+.16*np.cos(x-.1)
    pq=-.15+.23*np.cos(3*x+.4)+.12*np.sin(x+.5)
    N=1+.31*np.cos(x+.25)+.13*np.sin(2*x+.7)+.07*np.cos(4*x)
    M=.90+.27*np.sin(x+.12)+.11*np.cos(3*x-.2)+.09*np.sin(4*x+.3)
    Q=np.stack([a,b,c,chi,q]);P=np.stack([Pa,Pb,Pc,pchi,pq])
    out={}
    for omit in [False,True]:
        qN,pN=num_grad(Q,P,N,h,omit)
        qM,pM=num_grad(Q,P,M,h,omit)
        bracket=float(np.sum(qN*pM-pN*qM)/h)
        out['bad' if omit else 'correct']=bracket
    # Load the computation only to compare its independently derived gradients/brackets.
    spec=spec_from_file_location('verify_v27',str(ROOT/'verify_v27.py'))
    mod=module_from_spec(spec);spec.loader.exec_module(mod)
    import jax.numpy as jnp
    fj=jnp.array(Q); pj=jnp.array(P)
    jaxbr=float(mod.poiss(fj,pj,jnp.array(N),jnp.array(M),h,'correct'))
    jaxbad=float(mod.poiss(fj,pj,jnp.array(N),jnp.array(M),h,'omit_mixing'))
    out['jax_correct']=jaxbr;out['jax_bad']=jaxbad
    out['agreement_correct']=abs(out['correct']-jaxbr)
    out['agreement_bad']=abs(out['bad']-jaxbad)
    out['gradient_method']='NumPy two-sided perturbations versus JAX autodiff; two independently coded Hamiltonians'
    assert out['agreement_correct']<1e-7,(out['correct'],jaxbr)
    assert out['agreement_bad']<1e-7,(out['bad'],jaxbad)
    (ROOT/'independent_audit_v27.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
if __name__=='__main__':main()
