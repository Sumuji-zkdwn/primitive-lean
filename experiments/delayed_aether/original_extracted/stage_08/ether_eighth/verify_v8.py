#!/usr/bin/env python3
"""v8: exactly constraint-preserving local lattice linearised ADM benchmark.

This is an IMPLEMENTATION OF THE KNOWN quadratic Einstein / Fierz--Pauli
Hamiltonian, NOT a derivation of gravity from delayed hardening.
All derivatives are commuting centered differences on a periodic odd-sized grid.
Dependencies: numpy, sympy, matplotlib.
"""
from __future__ import annotations
import csv
import json
from pathlib import Path
import numpy as np
import sympy as s
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

OUT = Path(__file__).resolve().parent

def D(a, i, dx=1.):
    axis = a.ndim - 3 + i
    return (np.roll(a, -1, axis=axis) - np.roll(a, 1, axis=axis))/(2*dx)

def lap(a, dx=1.):
    return sum(D(D(a,i,dx),i,dx) for i in range(3))

def tr(h):
    return np.trace(h,axis1=0,axis2=1)

def div(h, dx=1.):
    return np.stack([sum(D(h[i,j],i,dx) for i in range(3)) for j in range(3)])

def sym_grad(x,dx=1.):
    return np.stack([np.stack([D(x[j],i,dx)+D(x[i],j,dx)
                                    for j in range(3)]) for i in range(3)])

def scalar_constraint(h,dx=1.):
    a=div(h,dx)
    return sum(D(a[j],j,dx) for j in range(3))-lap(tr(h),dx)

def momentum_constraint(p,dx=1.):
    return div(p,dx)

def G3(h, dx=1.):
    a=div(h,dx)
    t=tr(h)
    R=scalar_constraint(h,dx)
    return np.stack([np.stack([.5*(D(a[j],i,dx)+D(a[i],j,dx)
                   -lap(h[i,j],dx)-D(D(t,i,dx),j,dx)
                   -(R if i==j else 0))
              for j in range(3)]) for i in range(3)])

def p_force(h,dx=1.):
    return -G3(h,dx)

def h_velocity(p):
    t=tr(p)
    out=2*p.copy()
    for i in range(3): out[i,i]-=t
    return out

def potential(h,dx=1.):
    grads=[D(h,i,dx) for i in range(3)]
    a=div(h,dx)
    t=tr(h)
    return ( .25*sum(np.sum(g*g) for g in grads)
        -.5*np.sum(a*a)
        +.5*sum(np.sum(a[i]*D(t,i,dx)) for i in range(3))
        -.25*sum(np.sum(D(t,i,dx)**2) for i in range(3)))

def hamiltonian(h,p,dx=1.):
    return float(np.sum(p*p)-.5*np.sum(tr(p)**2)+potential(h,dx))

def maxabs(a):
    return float(np.max(np.abs(a)))

def sym_constraints_exact():
    # Single Fourier mode q; six independent symmetric matrix coefficients.
    v=[(0,0),(1,1),(2,2),(0,1),(0,2),(1,2)]
    trials=[(1,0,0),(0,1,0),(0,0,1),(1,2,3),(2,-1,4)]
    audits=[]
    for q0 in trials:
        q=s.Matrix(q0); q2=q.dot(q)
        def unpack(b):
            H=s.zeros(3)
            for c,(i,j) in zip(b,v): H[i,j]=c; H[j,i]=c
            return H
        hvars=s.symbols('h0:6')
        pvars=s.symbols('p0:6')
        H=unpack(hvars); P=unpack(pvars)
        cons=[(q.T*H*q)[0]-q2*s.trace(H)]+[(P*q)[i] for i in range(3)]
        vars=list(hvars)+list(pvars)
        A=s.Matrix([[s.diff(f,v) for v in vars] for f in cons])
        xs=s.symbols('x0:3'); f=s.Symbol('f')
        gauge_h=q*s.Matrix(xs).T+s.Matrix(xs)*q.T
        gauge_p=q*q.T*f-s.eye(3)*q2*f
        B=s.Matrix([[s.diff((gauge_h if k<6 else gauge_p)[i,j],w)
              for w in list(xs)+[f]] for k,(i,j) in enumerate(v+v)])
        assert A.rank()==4 and B.rank()==4 and A*B==s.zeros(4,4)
        audits.append({'q':list(q0),'constraint_rank':4,'gauge_rank':4,
                       'phase_space_dimensions':12,'physical_phase_dimensions':4,
                       'physical_wave_polarizations':2})
    return audits

def tetra_edge_test():
    # A single tetrahedron: six squared edge lengths equivalent to its Gram matrix.
    rng=np.random.default_rng(260)
    err=0.
    for _ in range(100):
        M=rng.normal(size=(3,3)); h=.02*(M+M.T)/2
        g=np.eye(3)+h
        l0=[g[i,i] for i in range(3)]
        lij={(i,j):g[i,i]+g[j,j]-2*g[i,j] for i in range(3) for j in range(i+1,3)}
        G=np.zeros((3,3))
        for i in range(3):G[i,i]=l0[i]
        for (i,j),lij2 in lij.items():
            G[i,j]=G[j,i]=(l0[i]+l0[j]-lij2)/2
        assert min(np.linalg.eigvalsh(g))>0
        err=max(err,maxabs(G-g))
    assert err<1e-12
    return {'random_positive_tetrahedra':100,'max_metric_reconstruction_error':err,
            'caveat':'Shared-edge gluing across tetrahedra is not implemented.'}

def identity_tests(N=13,dx=1.):
    rng=np.random.default_rng(20261122)
    h=rng.normal(size=(3,3,N,N,N))*.02
    h=(h+h.transpose(1,0,2,3,4))*.5
    p=rng.normal(size=h.shape)*.01
    p=(p+p.transpose(1,0,2,3,4))*.5
    xi=rng.normal(size=(3,N,N,N))*.01
    f=rng.normal(size=(N,N,N))*.01
    gf=np.stack([np.stack([D(D(f,i,dx),j,dx)-(lap(f,dx) if i==j else 0)
                                for j in range(3)]) for i in range(3)])
    cchange=maxabs(scalar_constraint(h+sym_grad(xi,dx),dx)-scalar_constraint(h,dx))
    gchange=maxabs(G3(h+sym_grad(xi,dx),dx)-G3(h,dx))
    mchange=maxabs(momentum_constraint(p+gf,dx)-momentum_constraint(p,dx))
    bianchi=maxabs(div(G3(h,dx),dx))
    cp_identity=maxabs(scalar_constraint(h_velocity(p),dx)-
                     2*sum(D(momentum_constraint(p,dx)[i],i,dx) for i in range(3)))
    p_constraint_velocity=maxabs(momentum_constraint(p_force(h,dx),dx))
    gauged_pot=abs(potential(h+sym_grad(xi,dx),dx)-potential(h,dx))
    alltests={'spatial_points':N**3,'bianchi_max_abs':bianchi,
              'scalar_constraint_gauge_change':cchange,
              'metric_force_gauge_change':gchange,
              'momentum_constraint_gauge_change':mchange,
              'constraint_time_identity_error':cp_identity,
              'momentum_constraint_rate_error':p_constraint_velocity,
              'potential_gauge_change_abs':gauged_pot}
    assert max(cchange,gchange,mchange,bianchi,cp_identity,p_constraint_velocity)<2e-12
    assert gauged_pot<1e-10
    return alltests

def physical_initial_data(N=17,dx=1.):
    coords=np.meshgrid(*[np.arange(N)*dx]*3,indexing='ij')
    qxi=np.zeros((3,N,N,N))
    h=np.zeros((3,3,N,N,N));p=np.zeros_like(h)
    configs=[((1,0,0),.015,0.1),((0,1,2),.010,0.5),((1,1,1),.009,1.3),((2,1,0),.008,2.2)]
    for m,A,phase0 in configs:
        kvec=2*np.pi*np.array(m)/(N*dx)
        q=np.sin(kvec*dx)/dx
        n=q/np.linalg.norm(q)
        seed=np.array([0.,0.,1.]) if abs(n[2])<.9 else np.array([0.,1.,0.])
        e1=seed-n*np.dot(n,seed)
        e1/=np.linalg.norm(e1)
        e2=np.cross(n,e1)
        plus=np.outer(e1,e1)-np.outer(e2,e2)
        cross=np.outer(e1,e2)+np.outer(e2,e1)
        E=plus if m[0]%2==1 else cross
        phase=sum(kvec[j]*coords[j] for j in range(3))+phase0
        frequency=np.linalg.norm(q)
        h+=A*E[:,:,None,None,None]*np.cos(phase)
        p+=.5*frequency*A*E[:,:,None,None,None]*np.sin(phase)
    # Static pure-gauge part, a periodic 'displacement' of coordinates.
    qxi[0]=.012*np.sin(2*np.pi*coords[1]/(N*dx))
    qxi[1]=-.008*np.cos(2*np.pi*(coords[0]+coords[2])/(N*dx))
    qxi[2]=.004*np.cos(4*np.pi*coords[2]/(N*dx))
    h+=sym_grad(qxi,dx)
    return h,p,qxi

def evolve(N=17,steps=320,dt=.14,dx=1.,draw=True):
    h,p0,xi=physical_initial_data(N,dx)
    h0=h.copy()
    g0=sym_grad(xi,dx)
    p_half=p0+.5*dt*p_force(h,dx)
    E0=hamiltonian(h,p0,dx)
    records=[]
    C0=maxabs(scalar_constraint(h,dx))
    M0=maxabs(momentum_constraint(p_half,dx))
    maxC,maxM=0.,0.
    energy_rel=[]
    for n in range(steps+1):
        pinteger=p_half-.5*dt*p_force(h,dx)
        E=hamiltonian(h,pinteger,dx)
        cr=maxabs(scalar_constraint(h,dx))
        mr=maxabs(momentum_constraint(p_half,dx))
        maxC=max(maxC,cr);maxM=max(maxM,mr)
        er=(E-E0)/E0
        energy_rel.append(er)
        if n%8==0 or n==steps:
            records.append([n*dt,cr,mr,er,
                        float(h[0,0,N//2,N//2,N//2]),
                        float(h[0,1,N//2,N//2,N//2])])
        if n<steps:
            h=h+dt*h_velocity(p_half)
            p_half=p_half+dt*p_force(h,dx)
    with (OUT/'constraint_dynamics.csv').open('w',newline='') as f:
        w=csv.writer(f);w.writerow(['t','abs_hamiltonian_constraint_max',
             'abs_momentum_constraint_max','relative_H2_change',
             'hxx_center','hxy_center']);w.writerows(records)
    if draw:
        rr=np.array(records)
        fig,axes=plt.subplots(2,1,figsize=(9.4,6.5),sharex=True,layout='constrained')
        axes[0].semilogy(rr[:,0],np.maximum(rr[:,1],1e-18),label='scalar constraint')
        axes[0].semilogy(rr[:,0],np.maximum(rr[:,2],1e-18),label='momentum constraint')
        axes[0].legend(); axes[0].set_ylabel('maximum absolute residual'); axes[0].grid(alpha=.25)
        axes[1].plot(rr[:,0],rr[:,4],label='hxx at center')
        axes[1].plot(rr[:,0],rr[:,5],label='hxy at center')
        axes[1].set(xlabel='t (lattice units)',ylabel='internal metric perturbation')
        axes[1].legend(); axes[1].grid(alpha=.25)
        fig.suptitle('3D local lattice gravity: constraint preservation and two shear components')
        fig.savefig(OUT/'constraints_and_shear.png',dpi=160);plt.close(fig)
    assert maxC<1e-12 and maxM<1e-12,(maxC,maxM)
    # Symplectic integration of physical TT modes should leave H2 nearly constant.
    maxenergy=float(np.max(np.abs(energy_rel)))
    assert maxenergy<0.005,maxenergy
    return {'grid':f'{N}^3','steps':steps,'dt':dt,
            'initial_scalar_residual':C0,'initial_momentum_residual':M0,
            'max_scalar_residual':maxC,'max_momentum_residual':maxM,
            'max_rel_energy_change_H2':maxenergy,
            'initial_H2':E0,'final_H2':E,
            'caveat':'This is canonical linearized Einstein gravity put in by hand.'}

def main():
    audit={'tetrahedron_six_edges_to_metric':tetra_edge_test(),
           'exact_fourier_dof_count':sym_constraints_exact(),
           'local_constraint_identities':identity_tests(),
           'evolution_17':evolve(),
           'evolution_21':evolve(N=21,steps=96,draw=False)}
    with (OUT/'audit_v8.json').open('w') as f:json.dump(audit,f,indent=2,ensure_ascii=False)
    print(json.dumps(audit,indent=2,ensure_ascii=False))

if __name__=='__main__':main()
