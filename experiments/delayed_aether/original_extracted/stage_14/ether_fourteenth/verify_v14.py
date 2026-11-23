#!/usr/bin/env python3
"""v14: exponential SPD metric, topological certificate, admissibility counterexample, ADM signature.
All tests are finite toy-model calculations, not derivations of GR.
"""
from __future__ import annotations
import csv, hashlib, json, math
from pathlib import Path
import numpy as np
from scipy.linalg import expm
from verify_v13 import ShearModel, sym, stable_logcosh
from verify_v11 import metric_geometry

HERE = Path(__file__).resolve().parent
I3 = np.eye(3)


def spd_exp_and_frechet_pullback(B, G=None):
    """Symmetric B -> exp(B), inv(exp B), sqrt(det(exp B)), optional adjoint derivative.
    Derivative pullback uses spectral Loewner matrix of matrix exponential.
    """
    lam, Q = np.linalg.eigh(sym(B))
    expv = np.exp(lam)
    g = np.einsum('...ik,...k,...jk->...ij',Q,expv,Q)
    P = np.einsum('...ik,...k,...jk->...ij',Q,1/expv,Q)
    w = np.exp(.5*np.sum(lam,axis=-1))
    if G is None: return g,P,w,None
    Gf = np.einsum('...ki,...kl,...lj->...ij',Q,G,Q)
    a=lam[..., :,None]; b=lam[...,None,:]
    diff=a-b
    # stable symmetric divided difference: (exp a - exp b)/(a-b)
    avg=(a+b)/2
    L=np.exp(avg)*np.sinh(diff/2)/(np.where(np.abs(diff)>1e-8,diff/2,1.))
    L=np.where(np.abs(diff)>1e-8,L,np.exp(avg)*(1+diff*diff/24))
    pull=np.einsum('...ik,...kl,...jl->...ij',Q,L*Gf,Q)
    return g,P,w,sym(pull)


class ExpShearModel(ShearModel):
    def potential(self,q,B,Z,grad=True):
        c=self.cell;h=self.h
        D=self.derivatives(q)
        S=np.einsum('...ca,...cb->...ab',D,D)
        g,P,w,_ = spd_exp_and_frechet_pullback(B[self.I]) if self.coupled else (
            np.broadcast_to(I3,B[self.I].shape), np.broadcast_to(I3,B[self.I].shape),
            np.ones(B[self.I].shape[:-2]), None)
        PS=P@S
        A=np.trace(PS,axis1=-2,axis2=-1)
        J=A*A-np.trace(PS@PS,axis1=-2,axis2=-1)
        E2=float(c*self.k2/2*np.sum(w*A))
        E4=float(c*self.k4/4*np.sum(w*J))
        if grad:
            dD=c*w[...,None,None]*(self.k2*np.einsum('...ca,...ab->...cb',D,P)
               +self.k4*np.einsum('...ca,...ab->...cb',D,A[...,None,None]*P-P@S@P))
            gq=np.zeros_like(q)
            force=dD[...,0]/(2*h)
            gq[2:,1:-1,1:-1]+=force;gq[:-2,1:-1,1:-1]-=force
            force=dD[...,1]/(2*h)
            gq[1:-1,2:,1:-1]+=force;gq[1:-1,:-2,1:-1]-=force
            force=dD[...,2]/(2*h)
            gq[1:-1,1:-1,2:]+=force;gq[1:-1,1:-1,:-2]-=force
            gB=np.zeros_like(B);gZ=np.zeros_like(Z)
            if self.coupled:
                PSP=P@S@P
                metric_grad = c*w[...,None,None]*(
                    self.k2/2*(.5*A[...,None,None]*P-PSP)
                    +self.k4/4*(.5*J[...,None,None]*P-2*A[...,None,None]*PSP+2*(P@S@P@S@P)))
                _,_,_,gB[self.I]=spd_exp_and_frechet_pullback(B[self.I],metric_grad)
        Egrad=0.
        for a in range(3):
            left=[slice(None)]*3;right=[slice(None)]*3
            left[a]=slice(None,-1);right[a]=slice(1,None)
            left=tuple(left);right=tuple(right)
            jump=B[right]-B[left]
            Egrad+=self.K*c/(2*h*h)*np.sum(jump*jump)
            if grad:
                force=self.K*c/(h*h)*jump
                gB[right]+=force;gB[left]-=force
        Emass=.5*self.m2*c*np.sum(B*B)
        y=B-Z
        r=np.sqrt(np.sum(y*y,axis=(-2,-1)))
        phi=.5*(self.k+self.delta)*r*r - self.delta*self.width**2*stable_logcosh(r/self.width)
        Ememory=float(c*np.sum(phi))
        if grad:
            gamma=(self.k+self.delta)-self.delta*self.width*np.tanh(r/self.width)/np.maximum(r,1e-16)
            gB+=self.m2*c*B+c*gamma[...,None,None]*y
            gZ-=c*gamma[...,None,None]*y
            gq[self.boundary]=0;gB[self.boundary]=0;gZ[self.boundary]=0
            gB=self.project_metric(gB);gZ=self.project_metric(gZ)
        return E2+E4+Egrad+Emass+Ememory, {'E2':E2,'E4':E4,'Egrad':float(Egrad),'Emass':float(Emass),'Ememory':Ememory},(gq,gB,gZ) if grad else None

    def gram_from_shared_edges(self,B):
        # Every edge is assigned ONE length, shared by neighboring tetrahedra.
        BV=B.reshape(-1,3,3)
        edges=self.edges
        d=self.coords[edges[:,1]]-self.coords[edges[:,0]]
        gmid,_,_,_=spd_exp_and_frechet_pullback(.5*(BV[edges[:,0]]+BV[edges[:,1]]))
        length2=np.einsum('ea,eab,eb->e',d,gmid,d)
        l2=length2[self.edgeinv]
        G=np.zeros((len(self.tets),3,3))
        G[:,0,0],G[:,1,1],G[:,2,2]=l2[:,0],l2[:,1],l2[:,2]
        G[:,0,1]=G[:,1,0]=(l2[:,0]+l2[:,1]-l2[:,3])/2
        G[:,0,2]=G[:,2,0]=(l2[:,0]+l2[:,2]-l2[:,4])/2
        G[:,1,2]=G[:,2,1]=(l2[:,1]+l2[:,2]-l2[:,5])/2
        G[:,0,0] = l2[:,0]
        return np.linalg.eigvalsh(sym(G)),np.sqrt(length2)

    def regge(self,B):
        eig,lens=self.gram_from_shared_edges(B)
        min_eig=float(np.min(eig))
        if min_eig<=0:
            return {'min_tet_gram_eig':min_eig,'max_regge_deficit':None,'regge_abs_curvature':None}
        geo=metric_geometry(self.coords,self.tets,self.edges,self.edgeinv,
            np.zeros(len(self.coords)),length_override=lens)
        return {'min_tet_gram_eig':min_eig,
                'max_regge_deficit':geo['max_flat_residual'],
                'regge_abs_curvature':geo['regge_abs_curvature']}

    def min_simplex_pair_dot(self,q):
        qv=q.reshape(-1,4)
        return float(np.min(np.einsum('ij,ij->i',qv[self.edges[:,0]],qv[self.edges[:,1]])))

    def guarded_step(self,state,dt,threshold=0.001,depth=0):
        q,B,Z,p,v,vz=state
        # For the v13 splitting integrator: drag half, then kick half, then geodesic drift.
        drag=np.exp(-self.gamma*dt/(2*self.mu_z))
        vzpre=vz*drag
        ppre,_,_=self.kick(q,B,Z,p.copy(),v.copy(),vzpre.copy(),dt/2)
        maxangle=float(dt*np.max(np.linalg.norm(ppre.reshape(-1,4),axis=1)))
        mindot=self.min_simplex_pair_dot(q)
        certificate=mindot-2*maxangle
        if certificate<=threshold:
            if depth>=14:raise RuntimeError('admissible timestep too small')
            state,dl1,cert1,n1=self.guarded_step(state,dt/2,threshold,depth+1)
            state,dl2,cert2,n2=self.guarded_step(state,dt/2,threshold,depth+1)
            return state,dl1+dl2,min(cert1,cert2),n1+n2
        state2,loss=self.step(state,dt)
        after=self.min_simplex_pair_dot(state2[0])
        assert after>=certificate-1e-10 and after>threshold
        return state2,loss,certificate,1


def finite_tetra_counterexample():
    # tetrahedron (0,0,0), (1,0,0), (0,1,0), (0,0,1).
    pts=np.array([[0.,0.,0.],[1.,0.,0.],[0.,1.,0.],[0.,0.,1.]])
    B=np.zeros((4,3,3))
    B[1,1,1]=np.log(100.);B[2,0,0]=np.log(100.)
    edge2=[]
    for i,j in ((0,1),(0,2),(1,2)):
        v=pts[j]-pts[i]
        g,_,_,_=spd_exp_and_frechet_pullback((B[i]+B[j])/2)
        edge2.append(float(v@g@v))
    a,b,c=np.sqrt(edge2)
    return {'edge_lengths':[float(a),float(b),float(c)],'triangle_inequality_gap':float(a+b-c),
            'all_vertex_metrics_SPD':True,'all_edges_positive':True,
            'counterexample':bool(a+b<c)}


def adm_metric(B,phi,beta):
    g,_,_,_=spd_exp_and_frechet_pullback(B)
    N=float(np.exp(phi))
    big=np.zeros((4,4))
    big[1:,1:]=g
    big[0,1:]=g@beta
    big[1:,0]=big[0,1:]
    big[0,0]=-N*N+beta@g@beta
    return big, -np.exp(2*phi+np.trace(B))


def writecsv(path,rows):
    with path.open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=rows[0].keys());writer.writeheader();writer.writerows(rows)


def gradient_tests(model):
    return model.check_gradient()


def simulate_guarded(model,T,dt,name):
    state=model.prepare(kick=.10)
    q,*_=state
    init=model.min_simplex_pair_dot(q)
    init_degree=int(model.degree(q))
    e0,_=model.energy(state)
    rows=[];loss=0.; mincert=1e100; substeps=0; global_max_logmetric=0.0
    for it in range(int(round(T/dt))+1):
        if it%5==0 or it==int(round(T/dt)):
            q,B,Z,p,v,vz=state
            E,parts=model.energy(state)
            s,off=model.shear_stats(B)
            ev,_=model.gram_from_shared_edges(B)
            eigs=np.linalg.eigvalsh(B.reshape(-1,3,3))
            maxB=float(np.max(np.abs(eigs)))
            lag=np.sqrt(np.sum((B-Z)**2,axis=(-2,-1)))
            rows.append({'t':it*dt,'topological_degree':int(model.degree(q)),
                'min_pair_dot':model.min_simplex_pair_dot(q),
                'min_admissible_certificate':mincert if it else init,
                'max_shear':s,'max_offdiag':off,
                'minimum_metric_eig':float(np.exp(np.min(eigs))),
                'max_logmetric_op':maxB,
                'max_memory_radial_modulus':float(model.k+model.delta*np.tanh(np.max(lag)/model.width)**2),
                'min_tetra_gram_eig':float(np.min(ev)),
                'energy':E,'accumulated_dissipation':loss,
                'relative_energy_budget':(E+loss-e0)/e0,**parts})
        if it==int(round(T/dt)): break
        state,dl,cert,ns=model.guarded_step(state,dt)
        global_max_logmetric=max(global_max_logmetric,float(np.max(np.abs(np.linalg.eigvalsh(state[1])))))
        substeps+=ns;loss+=dl;mincert=min(mincert,cert)
    writecsv(HERE/(name+'.csv'),rows)
    return state,rows, {'initial_pair_dot':init,'initial_degree':init_degree,
        'final_degree':rows[-1]['topological_degree'],
        'min_stepwise_certificate':mincert,'substeps':substeps,
        'max_abs_energy_budget':max(abs(r['relative_energy_budget']) for r in rows),
        'final_max_shear':rows[-1]['max_shear'],
        'final_regge':model.regge(state[1]),
        'minimum_metric_eig_over_saved_times':min(r['minimum_metric_eig'] for r in rows),
        'maximum_logmetric_op_over_saved_times':max(r['max_logmetric_op'] for r in rows),
        'maximum_logmetric_op_all_step_endpoints':global_max_logmetric,
        'minimum_gram_eig_over_saved_times':min(r['min_tetra_gram_eig'] for r in rows)}


def main():
    info={}
    info['tetrahedron_obstruction']=finite_tetra_counterexample()
    print('TETRA',info['tetrahedron_obstruction'],flush=True)
    rng=np.random.default_rng(20261122)
    A=sym(rng.normal(size=(120,3,3)))
    egs,P,w,_=spd_exp_and_frechet_pullback(A)
    info['spd_random']={
      'smallest_exp_metric_eigenvalue':float(np.min(np.linalg.eigvalsh(egs))),
      'max_inverse_error':float(np.max(np.abs(egs@P-I3))),
      'max_det_identity_relative_error':float(np.max(np.abs(np.linalg.det(egs)/w**2-1)))}
    adm=[]
    for _ in range(120):
        B=sym(rng.normal(size=(3,3)));phi=float(rng.uniform(-1.,1.))
        shift=rng.normal(size=3)
        mat,formula=adm_metric(B,phi,shift)
        vals=np.linalg.eigvalsh(mat)
        adm.append({'minus_count':int(np.sum(vals<0)), 'plus_count':int(np.sum(vals>0)),
                    'det_ratio':float(np.linalg.det(mat)/formula)})
    info['adm_signature']={
       'samples':len(adm),'all_lorentzian':bool(all(r['minus_count']==1 and r['plus_count']==3 for r in adm)),
       'max_det_identity_abs_error':float(max(abs(r['det_ratio']-1) for r in adm))}
    print('SPD',info['spd_random'],'ADM',info['adm_signature'],flush=True)
    shape_mu=float(np.linalg.eigvalsh(np.array([[1.,1.,1.],[1.,2.,2.],[1.,2.,3.]]))[0])
    info['uniform_simplex_sufficiency']={'reference_gram_min_eig_div_h2':shape_mu,
       'frobenius_distortion_bound_C':float(np.sqrt(58.)),
       'sufficient_max_logmetric_op':float(np.log1p(shape_mu/np.sqrt(58.)))}
    for n,dt,T in [(10,.002,.04),(12,.002,.08)]:
        model=ExpShearModel(n=n)
        grad=gradient_tests(model)
        print('GRAD',n,grad,flush=True)
        name=f'exp_n{n}_dt{str(dt).replace(".","p")}'
        _,rows,stats=simulate_guarded(model,T,dt,name)
        stats['uniform_sufficiency_verified_at_saved_times']=(
           stats['maximum_logmetric_op_all_step_endpoints'] < info['uniform_simplex_sufficiency']['sufficient_max_logmetric_op'])
        info[name]={'grad_checks':grad,**stats}
        print('DYNAMICS',name,stats,flush=True)
    (HERE/'audit_v14.json').write_text(json.dumps(info,indent=2,ensure_ascii=False))
    # Guard requirements, not overly optimistic conclusions.
    assert info['tetrahedron_obstruction']['counterexample']
    assert info['adm_signature']['all_lorentzian']
    for tag in ['exp_n10_dt0p002','exp_n12_dt0p002']:
        r=info[tag]
        assert r['initial_degree']==r['final_degree']==1
        assert r['min_stepwise_certificate']>0.
        assert r['minimum_metric_eig_over_saved_times']>0.
        assert r['minimum_gram_eig_over_saved_times']>0.
        assert all(x['abs_error']<1.e-7 for x in r['grad_checks'].values())
        assert r['max_abs_energy_budget']<1.e-3
    print('PASS: v14 numerical and topological audit',flush=True)

if __name__=='__main__':main()
