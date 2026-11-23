#!/usr/bin/env python3
"""V10: Four-dimensional spacetime Z2 cocycle and dissipative topological memory toy.

Only topological constraints are represented: NOT Einstein constraints / a Lorentzian metric.
Run: python verify_v10.py
Dependencies: numpy, matplotlib (for plots).
"""
from __future__ import annotations
from dataclasses import dataclass
from pathlib import Path
from itertools import combinations, product
import json, csv, hashlib
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

HERE=Path(__file__).resolve().parent
RNG=np.random.default_rng(20261122)

@dataclass
class CubicalComplex:
    """Cartesian cells, periodic axes indicated by True, non-periodic axes have n intervals."""
    lengths: tuple[int,...]
    periodic: tuple[bool,...]

    def __post_init__(self):
        assert len(self.lengths)==len(self.periodic)
        assert all(n>=2 for n in self.lengths)
        self.dim=len(self.lengths)
        self.cells=[]
        self.idx=[]
        for k in range(self.dim+1):
            objs=[]
            for subset in combinations(range(self.dim),k):
                ranges=[range(L if self.periodic[d] or d in subset else L+1)
                        for d,L in enumerate(self.lengths)]
                for x in product(*ranges):
                    objs.append((tuple(subset),tuple(x)))
            self.cells.append(objs)
            self.idx.append({val:i for i,val in enumerate(objs)})
        self.d=[]
        for k in range(self.dim):
            rows=[]
            for subset,x in self.cells[k+1]:
                bits=0
                for ax in subset:
                    sub=tuple(v for v in subset if v!=ax)
                    y=list(x); y[ax]+=1
                    if self.periodic[ax]: y[ax]%=self.lengths[ax]
                    for base in (x,tuple(y)):
                        bits ^= 1<<self.idx[k][(sub,base)]
                rows.append(bits)
            self.d.append(rows)

    @staticmethod
    def rank(rows):
        pivots={}
        for raw in rows:
            v=raw
            while v:
                k=v.bit_length()-1
                if k in pivots: v^=pivots[k]
                else:
                    pivots[k]=v
                    break
        return len(pivots)

    def audit(self):
        ranks=[self.rank(rows) for rows in self.d]
        n=[len(c) for c in self.cells]
        b=[n[k]-(ranks[k-1] if k else 0)-(ranks[k] if k<self.dim else 0)
           for k in range(self.dim+1)]
        for k in range(self.dim-1):
            for upperrow in self.d[k+1]:
                composition=0
                while upperrow:
                    low=upperrow & -upperrow
                    composition ^= self.d[k][low.bit_length()-1]
                    upperrow ^= low
                assert composition==0, f'd² nonzero at k={k}'
        return {'cells':n,'rank_d':ranks,'betti_mod2':b,
                'Euler_cells':sum((-1)**i*v for i,v in enumerate(n)),
                'Euler_betti':sum((-1)**i*v for i,v in enumerate(b)),
                'd_squared_zero_exact':True}


def arrays(L, D=3):
    return np.zeros((D,)*0+(L,)*D,dtype=np.uint8)

DIRECTIONS=((0,1),(0,2),(1,2))

def curl(a):
    """Spatial d1, a has shape [3,L,L,L] and f shape [3,L,L,L]."""
    out=np.zeros((3,*a.shape[1:]),dtype=np.uint8)
    for p,(i,j) in enumerate(DIRECTIONS):
        out[p]=(a[j] ^ np.roll(a[j],-1,axis=i)
                ^ a[i] ^ np.roll(a[i],-1,axis=j))
    return out


def d2(B):
    """Spatial d2 (one cube value per vertex)."""
    return ((B[2]^np.roll(B[2],-1,axis=0))
            ^ (B[1]^np.roll(B[1],-1,axis=1))
            ^ (B[0]^np.roll(B[0],-1,axis=2)))


def flux(B):
    """Three Z2 charges on reference spatial 2-tori: x_other=0."""
    q=[]
    for p,(i,j) in enumerate(DIRECTIONS):
        other=({0,1,2}-{i,j}).pop()
        section=np.take(B[p],0,axis=other)
        q.append(int(np.sum(section,dtype=np.int64)%2))
    return tuple(q)


def flux_every_section(B):
    result={}
    for p,(i,j) in enumerate(DIRECTIONS):
        other=({0,1,2}-{i,j}).pop()
        result[str((i,j))]=[int(np.sum(np.take(B[p],n,axis=other))%2)
                                for n in range(B.shape[-1])]
    return result


def representative(L,p=0):
    B=np.zeros((3,L,L,L),dtype=np.uint8)
    i,j=DIRECTIONS[p]
    # 1 plaquette in each spatial 2-torus section; nonzero cohomology class.
    for x in np.ndindex(L,L,L):
        if x[i]==0 and x[j]==0:
            B[(p,*x)]=1
    assert not d2(B).any()
    assert flux(B)[p]==1
    return B


def phi(y,k=.30,Delta=3.,scale=.30):
    z=y/scale
    # stable logcosh using logaddexp
    return .5*(k+Delta)*y*y-Delta*scale**2*(np.logaddexp(z,-z)-np.log(2))


def phi_prime(y,k=.30,Delta=3.,scale=.30):
    return (k+Delta)*y-Delta*scale*np.tanh(y/scale)


def stiffness(y,k=.30,Delta=3.,scale=.30):
    return k+Delta*np.tanh(y/scale)**2


def energy(B,m,J=2.):
    return J*int(B.sum())+float(phi(B.astype(float)-m).sum())


def edge_supports(L):
    supp=[]
    for i in range(3):
        for x in np.ndindex(L,L,L):
            a=np.zeros((3,L,L,L),dtype=np.uint8)
            a[(i,*x)]=1
            face_idx=np.flatnonzero(curl(a).reshape(-1))
            assert len(face_idx)==4
            supp.append((i,x,face_idx))
    return supp


def run_relax(L, charged, rate, seed=20261122, max_sweeps=140):
    rng=np.random.default_rng(seed)
    B0=representative(L) if charged else np.zeros((3,L,L,L),dtype=np.uint8)
    B=B0.copy()
    m=None  # memory set after prior perturbation: equilibrated with its former configuration
    # Include multiple sparse defects, created by exact moves d a.
    edge_pulses=[(0,(0,0,0)),(1,(1,1,1)),(2,(2,2,2)),(0,(1,2,0)),(1,(2,0,1)),(2,(0,1,2))]
    a_init=np.zeros((3,L,L,L),dtype=np.uint8)
    for i,x in edge_pulses:
        a_init[(i,*x)]=1
    B ^= curl(a_init)
    m=B.astype(float).copy()  # history previously tracked this excited shape; release it now
    assert not d2(B).any()
    q0=flux(B)
    assert q0==((1,0,0) if charged else (0,0,0))
    # 'Initial perturbation' happened prior to the first physical time step.
    supports=edge_supports(L)
    audit=[];A_list=[];B_list=[B.copy()]
    H=energy(B,m)
    for step in range(max_sweeps):
        prior=B.copy()
        A=np.zeros((3,L,L,L),dtype=np.uint8)
        for ix in rng.permutation(len(supports)):
            i,x,indices=supports[ix]
            bf=B.reshape(-1)
            mb=m.reshape(-1)
            old=bf[indices].astype(float)
            new=1.-old
            DE=2.*float(np.sum(new-old)) + float(
                np.sum(phi(new-mb[indices])-phi(old-mb[indices])))
            if DE < -1e-11:
                bf[indices]^=1
                A[(i,*x)]^=1
        # Real-valued memory is relaxed with a local finite-memory gradient step.
        # H(m) decreases by choosing step smaller than 2/(k+Delta), here 0.15.
        y=B.astype(float)-m
        m = m + rate*phi_prime(y)
        H1=energy(B,m)
        assert H1 <= H + 1e-8, ('not dissipative',H,H1,step)
        assert np.array_equal(B,prior ^ curl(A)), '4D time-spatial cube Bianchi fails'
        assert not d2(B).any(), 'spatial cube Bianchi fails'
        assert flux(B)==q0, 'topological charge altered'
        H=H1
        A_list.append(A.copy());B_list.append(B.copy())
        audit.append([step+1,int(B.sum()),H,float(stiffness(B.astype(float)-m).max()),
                      float(np.sqrt(np.mean((B-m)**2))),int(A.sum()),*q0])
    return {'charged':charged,'rate':rate,'B_initial':B_list[0],
            'B_final':B,'m_final':m,'Q':q0,'history':np.asarray(audit),
            'B_history':np.asarray(B_list),'A_history':np.asarray(A_list),
            'B0':B0,'initial_energy':energy(B_list[0],B_list[0].astype(float)),
            'max_cube_residual':0, 'max_spacetime_cube_residual':0}


def test_formulae():
    # 1. two independent random 3D lattice cochains: d²=0
    L=3
    for rep in range(50):
        a=RNG.integers(0,2,size=(3,L,L,L),dtype=np.uint8)
        assert not d2(curl(a)).any()
        B=representative(L)
        assert flux(B ^ curl(a))==flux(B)
    # 2. Different parameter cases still bounded and convex.
    ys=np.linspace(-3,3,20001)
    assert np.min(phi(ys))>=-1e-13
    assert np.min(stiffness(ys))>=.3-1e-13
    assert np.max(stiffness(ys))<=3.3+1e-13
    # 3. Test local edge support orientation
    supp=edge_supports(3)
    assert len(supp)==81
    # 4. Test 2^3 charge sectors individually, and any combinations.
    reps=[representative(3,p) for p in range(3)]
    qset=[]
    for code in range(8):
        B=np.zeros_like(reps[0])
        for p in range(3):
            if (code>>p)&1:B ^= reps[p]
        assert not d2(B).any()
        qset.append(flux(B))
    assert len(set(qset))==8
    return {'random_d2d1_tests':50, 'distinct_charge_classes_explicit':len(set(qset)),
            'stiffness_range':[float(np.min(stiffness(ys))),float(np.max(stiffness(ys)))],
            'local_face_count_per_edge':4}


def exact_4d_spacetime_audit(L=2,T=2):
    """Build an entire 4D spacetime cochain and check EVERY cube (not only a split formula)."""
    C=CubicalComplex((T,L,L,L),(False,True,True,True))
    initial=representative(L)
    # Start with an arbitrary exact perturbation, and then arbitrary spacetime moves.
    a0=RNG.integers(0,2,size=(3,L,L,L),dtype=np.uint8)
    initial ^= curl(a0)
    Bhistory=[initial]
    A=[]
    for t in range(T):
        a=RNG.integers(0,2,size=(3,L,L,L),dtype=np.uint8)
        A.append(a)
        Bhistory.append(Bhistory[-1]^curl(a))
    bits=0
    for t,B in enumerate(Bhistory):
        for p,(i,j) in enumerate(DIRECTIONS):
            for x in np.ndindex(L,L,L):
                if B[(p,*x)]:
                    bits ^= 1<<C.idx[2][((i+1,j+1),(t,*x))]
    for t,a in enumerate(A):
        for i in range(3):
            for x in np.ndindex(L,L,L):
                if a[(i,*x)]:
                    bits ^= 1<<C.idx[2][((0,i+1),(t,*x))]
    failures=sum((bits & row).bit_count()%2 for row in C.d[2])
    assert failures==0
    assert all(flux(B)==flux(initial) for B in Bhistory)
    # Physically inconsistent time/spatial face edit without a compensating flow.
    flipped=bits^(1<<C.idx[2][((1,2),(1,0,0,0))])
    after_failures=sum((flipped & row).bit_count()%2 for row in C.d[2])
    assert after_failures>0
    return {'spacetime_cells':len(C.cells[4]), 'faces':len(C.cells[2]),
            'cubes_tested':len(C.cells[3]), 'exact_cube_failures':failures,
            'one_uncompensated_face_flip_cube_failures':after_failures,
            'charge_initial':flux(initial), 'charge_each_slice':[flux(B) for B in Bhistory]}


def report():
    spatial2=CubicalComplex((2,2,2),(True,True,True)).audit()
    spatial3=CubicalComplex((3,3,3),(True,True,True)).audit()
    cyl2=CubicalComplex((2,2,2,2),(False,True,True,True)).audit()
    assert spatial2['betti_mod2']==[1,3,3,1]
    assert spatial3['betti_mod2']==[1,3,3,1]
    assert cyl2['betti_mod2']==[1,3,3,1,0]
    assert cyl2['cells']==[24,88,120,72,16]
    base_test=test_formulae()
    spacetime_exact=exact_4d_spacetime_audit()
    torus4=CubicalComplex((2,2,2,2),(True,True,True,True)).audit()
    openbox3=CubicalComplex((2,2,2),(False,False,False)).audit()
    assert torus4['betti_mod2']==[1,4,6,4,1]
    assert openbox3['betti_mod2']==[1,0,0,0]
    simulations=[run_relax(3,charged,rate,seed=20261122+int(charged)*7+int(100*rate))
                 for charged in (False,True) for rate in (.06,.15)]
    audit_runs=[]
    for sim in simulations:
        hist=sim['history']; Bf=sim['B_final']
        h=np.vstack([[0,int(sim['B_initial'].sum()),sim['initial_energy'],
                      0.3, 0.0,0,*sim['Q']],hist])
        charged=int(sim['charged']); rate=sim['rate']
        filepath=HERE/f'dynamics_charge_{charged}_rate_{str(rate).replace(".","p")}.csv'
        np.savetxt(filepath,h,delimiter=',',comments='',
            header='sweep,excited_plaquettes,energy,max_tangent_stiffness,lag_rms,edge_flips,Q01,Q02,Q12',
            fmt=['%d','%d','%.12g','%.12g','%.12g','%d','%d','%d','%d'])
        audits={'charged':bool(charged),'rate':rate,'Q':sim['Q'],
                'initial_plaquettes':int(sim['B_initial'].sum()),
                'final_plaquettes':int(Bf.sum()),
                'initial_energy':float(h[0,2]),'final_energy':float(h[-1,2]),
                'peak_stiffness':float(np.max(h[:,3])),
                'final_stiffness':float(h[-1,3]),
                'num_positive_energy_steps':int(np.sum(np.diff(h[:,2])>1e-8)),
                'total_accepted_edges':int(hist[:,5].sum()),
                'min_required_plaquettes':3 if charged else 0,
                'max_3d_Bianchi_residual':0,
                'max_4d_Bianchi_residual':0}
        assert audits['final_plaquettes'] >= audits['min_required_plaquettes']
        audit_runs.append(audits)
    # Draw two views of relaxation and protected sector.
    fig,axs=plt.subplots(2,1,figsize=(8.8,6.4),sharex=True)
    for s in simulations:
        h=s['history']; lab=f"Q={int(s['charged'])}, memory={s['rate']}"
        axs[0].plot(np.r_[0,h[:,0]],np.r_[s['initial_energy'],h[:,2]],label=lab)
        axs[1].plot(np.r_[0,h[:,0]],np.r_[int(s['B_initial'].sum()),h[:,1]],label=lab)
    axs[0].set_ylabel('Total energy');axs[0].legend(fontsize=9,ncol=2)
    axs[1].set_ylabel('Excited plaquettes');axs[1].set_xlabel('Local-update sweep')
    axs[1].axhline(3,linestyle='--',linewidth=1,label='Q01=1 lower bound: 3')
    axs[1].axhline(0,linestyle=':',linewidth=1)
    fig.tight_layout();fig.savefig(HERE/'topological_memory_relaxation.png',dpi=170);plt.close(fig)
    # Draw stiffness and lag.
    fig,axs=plt.subplots(2,1,figsize=(8.8,6.0),sharex=True)
    for s in simulations:
        h=s['history'];lab=f"Q={int(s['charged'])}, memory={s['rate']}"
        axs[0].plot(h[:,0],h[:,3],label=lab)
        axs[1].plot(h[:,0],h[:,4],label=lab)
    axs[0].set_ylabel('Max tangent stiffness');axs[0].legend(fontsize=9,ncol=2)
    axs[1].set_ylabel('Memory mismatch RMS');axs[1].set_xlabel('Local-update sweep')
    fig.tight_layout();fig.savefig(HERE/'memory_stiffness.png',dpi=170);plt.close(fig)
    # Intuitive dual string display: excited (0,1) faces at transverse z coordinates, by x,y.
    s=next(r for r in simulations if r['charged'] and r['rate']==.15)
    Bfirst=s['B_initial'];Blast=s['B_final']
    fig,axs=plt.subplots(2,3,figsize=(9,5.6))
    for row,bs in enumerate((Bfirst,Blast)):
        for z in range(3):
            axs[row,z].imshow(bs[0,:,:,z],interpolation='nearest',cmap='Greys',vmin=0,vmax=1)
            axs[row,z].set_title(f"{'initial' if row==0 else 'final'}, z={z}")
            axs[row,z].set_xticks(range(3));axs[row,z].set_yticks(range(3))
    fig.suptitle('01-plaquette slices; parity is protected on each z slice')
    fig.tight_layout();fig.savefig(HERE/'flux_slices.png',dpi=170);plt.close(fig)
    # Exact lower bound for all orientations, multiple L: 2,3,4.
    lower=[]
    for L in [2,3,4,5]:
        for p in range(3):
            B=representative(L,p)
            assert int(B.sum())==L
            assert all(k==1 for k in flux_every_section(B)[str(DIRECTIONS[p])])
            lower.append({'L':L,'charge_pair':str(DIRECTIONS[p]),
                          'proven_lower_bound':L,'explicit_saturating_area':int(B.sum()),
                          'one_flux_in_each_transverse_slice':True})
    with (HERE/'sector_area_bounds.csv').open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=list(lower[0]));writer.writeheader();writer.writerows(lower)
    summary={'model':'v10 discrete Z2 cocycle with physical flux, bounded memory, and spacetime constraint',
             'date':'2026-11-22','spatial_2x2x2':spatial2,'spatial_3x3x3':spatial3,
             'spacetime_cylinder_2x2x2_times_2_intervals':cyl2,
             'spacetime_full_cochain_exact_audit':spacetime_exact,
             'periodic_time_4torus':torus4,
             'open_spatial_box':openbox3,
             'form_identities':base_test, 'runs':audit_runs,
             'spacetime_Bianchi':'B_ij(t+1) xor B_ij(t) = (d_3 a_t)_ij; B_0i(t)=a_i(t); d_4 B=0 exactly',
             'theorem':'Q_ij is conserved for B(t+1)=B(t)+d_3 a_t; every Q_ij=1 sector contains at least L face excitations',
             'interpretation':'Noncontractible dual strings on spatial T3, not localized point particles',
             'limitations':['No Lorentzian metric, diffeomorphism symmetry, Einstein constraints, TT wave or gravity source',
                            'Spatial topology is T3 with periodic boundary conditions; infinite space has different cohomology',
                            'Update sweep is dissipative external-time relaxation, not relativistic causal propagation',
                            'Physical B→B+d a is NOT a gauge redundancy; unlike the SO(3) frame rotation of v9',
                            'Time cylinder has three topological sectors labels; periodic-time T4 would give six']}
    # Audit cyclic spacetime closure including random A fields and spatial B.
    for s in simulations:
        Bhist=s['B_history'];Ahist=s['A_history']
        for t in range(len(Ahist)):
            assert np.array_equal(Bhist[t+1]^Bhist[t],curl(Ahist[t]))
            assert not d2(Bhist[t]).any()
        assert not d2(Bhist[-1]).any()
        assert all(flux(B)==s['Q'] for B in Bhist)
    with (HERE/'audit_v10.json').open('w') as f:json.dump(summary,f,indent=2,ensure_ascii=False)
    return summary

if __name__=='__main__':
    info=report()
    print(json.dumps({'spatial_betti':info['spatial_3x3x3']['betti_mod2'],
        'spacetime_betti':info['spacetime_cylinder_2x2x2_times_2_intervals']['betti_mod2'],
        'runs':info['runs']},indent=2))
