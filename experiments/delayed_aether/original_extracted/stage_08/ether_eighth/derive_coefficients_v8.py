#!/usr/bin/env python3
"""Determine lattice spin-2 quadratic coefficients from gauge symmetry and constraints.

For spatial h_ij, assume translation-invariant rotation-invariant parity-even
quadratic energy built from ONE spatial derivative, with four contractions.
Under h -> h + D_i xi_j + D_j xi_i the Euler operator must annihilate
pure-gauge fields. This determines a,b,c,d up to an overall scale.

Independently, the canonical momentum quadratic invariant has parameter lambda.
Preservation of scalar constraint for arbitrary momentum-constrained pi fixes
lambda=1/2. This is a conditional uniqueness statement, NOT emergence of gravity.
"""
import json
from pathlib import Path
import numpy as np
import sympy as s
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from verify_v8 import D, tr, scalar_constraint, momentum_constraint, maxabs
OUT=Path(__file__).resolve().parent

def unique_spatial_potential():
    a,b,c,d=s.symbols('a b c d')
    results=[]
    # Fourier symbol for any commuting local difference derivatives.
    for q0 in [(1,0,0),(1,2,3),(2,-1,4)]:
        q=s.Matrix(q0); q2=q.dot(q)
        def Euler(H):
            A=H*q; t=s.trace(H); divA=(q.T*A)[0]
            return s.Matrix(3,3,lambda i,j:
                   2*a*q2*H[i,j]
                   +b*(q[i]*A[j]+q[j]*A[i])
                   +c*q[i]*q[j]*t
                   +c*int(i==j)*divA
                   +2*d*int(i==j)*q2*t)
        for xi in s.eye(3).columnspace():
            H=q*xi.T+xi*q.T
            results.extend(list(Euler(H)))
    A,_=s.linear_eq_to_matrix(results,[a,b,c,d])
    ker=A.nullspace()
    assert A.rank()==3 and len(ker)==1
    unique=ker[0]
    normalized=unique/(4*unique[0])
    assert list(normalized)==[s.Rational(1,4),-s.Rational(1,2),
                              s.Rational(1,2),-s.Rational(1,4)]
    # Exact universal polynomial check, rather than merely testing example q.
    q=s.Matrix(s.symbols('qx qy qz'))
    xi=s.Matrix(s.symbols('xi0 xi1 xi2'))
    H=q*xi.T+xi*q.T
    Afield=H*q; t=s.trace(H); divA=(q.T*Afield)[0]; q2=q.dot(q)
    aa,bb,cc,dd=normalized
    E=s.Matrix(3,3,lambda i,j: 2*aa*q2*H[i,j]
          +bb*(q[i]*Afield[j]+q[j]*Afield[i])
          +cc*q[i]*q[j]*t+cc*int(i==j)*divA
          +2*dd*int(i==j)*q2*t)
    assert all(s.expand(x)==0 for x in E)
    return {'basis':'a |D h|^2 + b |div h|^2 + c (div h)·D tr(h) + d |D tr(h)|^2',
            'number_of_basis_invariants':4,'gauge_invariance_equation_rank':int(A.rank()),
            'nullspace_dimension':len(ker),
            'universal_symbolic_identity_checked':True,
            'unique_coefficients_normalized':[str(x) for x in normalized],
            'assumptions':'quadratic, spatially isotropic, at most first derivatives in energy, parity-even, modulo integration by parts'}

def unique_kinetic():
    lam=s.symbols('lambda')
    # hdot_ij = 2 pi_ij - 2 lambda delta_ij tr(pi)
    # Cdot = 2 divdiv pi + (4lambda-2) lap tr(pi)
    symbolic=s.factor(4*lam-2)
    solution=s.solve(symbolic,lam)
    assert solution==[s.Rational(1,2)]
    N=17; dx=1.; zz=np.arange(N)[None,None,:]; coords=np.ones((N,N,1))
    p=np.zeros((3,3,N,N,N))
    for i in (0,1):p[i,i]=np.broadcast_to(np.cos(2*np.pi*zz/N),(N,N,N))
    assert maxabs(momentum_constraint(p,dx))<1e-14
    scalar0=np.zeros((N,N,N))
    lamvals=np.linspace(0,1,101)
    maxvals=[]
    for value in lamvals:
        hdot=2*p.copy()
        for i in range(3):hdot[i,i]-=2*value*tr(p)
        maxvals.append(maxabs(scalar_constraint(hdot,dx)))
    assert min(maxvals)<1e-14
    assert maxvals[0]>0.1
    fig,ax=plt.subplots(figsize=(8.6,4.4),layout='constrained')
    ax.plot(lamvals,maxvals)
    ax.axvline(.5,ls='--',label='constraint-preserving lambda = 1/2')
    ax.set(xlabel='trace coefficient lambda',ylabel='max |dC/dt|',
           title='Only one kinetic trace coefficient preserves the constraint')
    ax.grid(alpha=.2);ax.legend()
    fig.savefig(OUT/'lambda_constraint_no_go.png',dpi=160)
    plt.close(fig)
    return {'kinetic_energy':'pi_ij pi_ij - lambda (tr pi)^2',
           'scalar_constraint_rate':'2 D_i C_i + (4 lambda - 2) Delta tr(pi)',
           'unique_constraint_preserving_lambda':str(solution[0]),
           'finite_counterexample_grid':N,
           'momentum_constraint_residual':maxabs(momentum_constraint(p,dx)),
           'lambda_0_scalar_constraint_rate_max':float(maxvals[0]),
           'lambda_half_scalar_constraint_rate_max':float(maxvals[50]),
           'lambda_1_scalar_constraint_rate_max':float(maxvals[-1])}

def main():
    audit={'uniqueness_of_spatial_potential':unique_spatial_potential(),
           'uniqueness_of_kinetic_trace':unique_kinetic(),
           'warning':'These symmetry assumptions encode massless spin-2 structure, which is not derived from gel memory.'}
    with (OUT/'derivation_audit_v8.json').open('w') as f:json.dump(audit,f,ensure_ascii=False,indent=2)
    print(json.dumps(audit,ensure_ascii=False,indent=2))
if __name__=='__main__':main()
