#!/usr/bin/env python3
"""v13: finite vertex-state topology obstruction + 3-D shear metric/memory action.

Reproducible toy model, not general relativity. Run in this directory.
"""
from __future__ import annotations
import argparse, csv, json, math
from pathlib import Path
import numpy as np
from scipy.optimize import brentq
from verify_v11 import make_mesh, hedgehog, degree_preimage, unique_edges, metric_geometry

HERE=Path(__file__).resolve().parent
EYE=np.eye(3)


def stable_logcosh(x):
    a=np.abs(x)
    return a + np.log1p(np.exp(-2*a)) - np.log(2.)


def sym(a):
    return .5*(a+np.swapaxes(a,-1,-2))


class ShearModel:
    def __init__(self,n=8,full=True,coupled=True,k2=1.,k4=.08249624119,K=.35,m2=1.2,k=.55,delta=3.,width=.035,mu=1.,mu_z=.75,gamma=.6):
        self.n=n; self.N=n+1; self.h=2./n; self.cell=self.h**3
        self.full=full; self.coupled=coupled
        self.k2=k2;self.k4=k4;self.K=K;self.m2=m2
        self.k=k;self.delta=delta;self.width=width;self.mu=mu;self.mu_z=mu_z;self.gamma=gamma
        self.coords,self.tets=make_mesh(n)
        self.edges,self.edgeinv=unique_edges(self.tets)
        X=self.coords.reshape((self.N,)*3+(3,))
        self.boundary=np.any(np.isclose(np.abs(X),1.),axis=-1)
        self.I=np.s_[1:-1,1:-1,1:-1]
        self.vac=np.array([1.,0.,0.,0.])

    def project_metric(self,B):
        if self.full:return sym(B)
        tr=np.trace(B,axis1=-2,axis2=-1)/3.
        return tr[...,None,None]*EYE

    def prepare(self,kick=.1):
        n=self.N
        q=hedgehog(self.coords,center=(-.135,.065,-.035),radius=.69).reshape((n,n,n,4))
        B=np.zeros((n,n,n,3,3));Z=B.copy()
        p=np.zeros_like(q)
        p[1:-1]=(-kick)*(q[2:]-q[:-2])/(2*self.h)
        p-=np.sum(p*q,axis=-1,keepdims=True)*q
        p[self.boundary]=0
        v=np.zeros_like(B);vz=v.copy()
        return (q,B,Z,p,v,vz)

    def derivatives(self,q):
        h=self.h
        Dx=(q[2:,1:-1,1:-1]-q[:-2,1:-1,1:-1])/(2*h)
        Dy=(q[1:-1,2:,1:-1]-q[1:-1,:-2,1:-1])/(2*h)
        Dz=(q[1:-1,1:-1,2:]-q[1:-1,1:-1,:-2])/(2*h)
        return np.stack([Dx,Dy,Dz],axis=-1)

    def potential(self,q,B,Z,grad=True):
        c=self.cell; h=self.h
        D=self.derivatives(q)           # (n-1)^3 x 4 x 3
        S=np.einsum('...ca,...cb->...ab',D,D)
        g=EYE+B[self.I]
        if self.coupled:
            det=np.linalg.det(g)
            if np.min(det)<=0 or np.min(np.linalg.eigvalsh(g))<=0:
                raise ValueError('non-positive vertex metric')
            P=np.linalg.inv(g)
            w=np.sqrt(det)
        else:
            P=np.broadcast_to(EYE,g.shape)
            w=np.ones(g.shape[:-2])
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
                    + self.k4/4*(.5*J[...,None,None]*P
                        -2*A[...,None,None]*PSP+2*(P@S@P@S@P))
                    )
                gB[self.I]+=metric_grad
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

    def kinetic(self,p,v,vz):
        return .5*self.cell*(np.sum(p*p)+self.mu*np.sum(v*v)+self.mu_z*np.sum(vz*vz))

    def energy(self,state):
        q,B,Z,p,v,vz=state
        E,parts,_=self.potential(q,B,Z,False)
        return E+self.kinetic(p,v,vz),parts

    def kick(self,q,B,Z,p,v,vz,dt):
        _,_,(gq,gB,gZ)=self.potential(q,B,Z)
        gq-=np.sum(q*gq,axis=-1,keepdims=True)*q
        p=p-dt*gq/self.cell
        v=v-dt*gB/(self.mu*self.cell)
        vz=vz-dt*gZ/(self.mu_z*self.cell)
        p[self.boundary]=0;v[self.boundary]=0;vz[self.boundary]=0
        return p,self.project_metric(v),self.project_metric(vz)

    def drift(self,q,B,Z,p,v,vz,dt):
        pn=np.linalg.norm(p,axis=-1,keepdims=True)
        an=dt*pn
        q1=q*np.cos(an)+p*(np.sinc(an/np.pi)*dt)
        p1=p*np.cos(an)-q*(pn*np.sin(an))
        B1=B+dt*v;Z1=Z+dt*vz
        q1[self.boundary]=self.vac;p1[self.boundary]=0
        B1[self.boundary]=0;Z1[self.boundary]=0
        return q1,self.project_metric(B1),self.project_metric(Z1),p1,v,vz

    def step(self,state,dt):
        q,B,Z,p,v,vz=state
        drag=np.exp(-self.gamma*dt/(2*self.mu_z))
        dissipated=.5*self.cell*self.mu_z*(1-drag*drag)*np.sum(vz*vz)
        vz=vz*drag
        p,v,vz=self.kick(q,B,Z,p,v,vz,dt/2)
        q,B,Z,p,v,vz=self.drift(q,B,Z,p,v,vz,dt)
        p,v,vz=self.kick(q,B,Z,p,v,vz,dt/2)
        dissipated+=.5*self.cell*self.mu_z*(1-drag*drag)*np.sum(vz*vz)
        return (q,B,Z,p,v,vz*drag),float(dissipated)

    def degree(self,q):
        return -degree_preimage(self.coords,self.tets,q.reshape(-1,4))

    def shear_stats(self,B):
        tr=np.trace(B,axis1=-2,axis2=-1)/3
        dev=B-tr[...,None,None]*EYE
        maxs=float(np.max(np.sqrt(np.sum(dev*dev,axis=(-2,-1)))))
        maxoff=float(max(np.max(np.abs(B[...,0,1])),np.max(np.abs(B[...,0,2])),np.max(np.abs(B[...,1,2]))))
        return maxs,maxoff

    def regge(self,B):
        coords=self.coords; edges=self.edges
        d=coords[edges[:,1]]-coords[edges[:,0]]
        g=EYE+(B.reshape(-1,3,3)[edges[:,0]]+B.reshape(-1,3,3)[edges[:,1]])/2
        l2=np.einsum('ea,eab,eb->e',d,g,d)
        if np.min(l2)<=0:raise ValueError('negative edge length squared')
        geometry=metric_geometry(coords,self.tets,edges,self.edgeinv,
                                 np.zeros(len(coords)),length_override=np.sqrt(l2))
        return {'min_vertex_metric_eig':float(np.min(np.linalg.eigvalsh(EYE+B.reshape(-1,3,3)))),
                'min_tet_gram_eig':geometry['min_gram_eigenvalue'],
                'max_regge_deficit':geometry['max_flat_residual'],
                'regge_abs_curvature':geometry['regge_abs_curvature']}

    def check_gradient(self):
        rng=np.random.default_rng(1326)
        state=self.prepare();q,B,Z,_,_,_=state
        B[self.I]=sym(rng.normal(0,.005,size=B[self.I].shape))
        B=self.project_metric(B)
        Z[self.I]=sym(rng.normal(0,.004,size=Z[self.I].shape))
        Z=self.project_metric(Z)
        E,_,(gq,gB,gZ)=self.potential(q,B,Z)
        tests={}
        for key in ('q','B','Z'):
            if key=='q':
                d=rng.normal(size=q.shape)
                d-=np.sum(d*q,axis=-1,keepdims=True)*q
                d[self.boundary]=0
                d/=np.linalg.norm(d)
                dot=np.sum(d*gq)
                def probe(t):return self.potential(q+t*d,B,Z,False)[0]
            else:
                d=self.project_metric(sym(rng.normal(size=B.shape)))
                d[self.boundary]=0
                d/=np.linalg.norm(d)
                dot=np.sum(d*(gB if key=='B' else gZ))
                if key=='B':
                    def probe(t):return self.potential(q,B+t*d,Z,False)[0]
                else:
                    def probe(t):return self.potential(q,B,Z+t*d,False)[0]
            eps=1e-5
            fd=(probe(eps)-probe(-eps))/(2*eps)
            tests[key]={'analytic':float(dot),'finite_difference':float(fd),'abs_error':float(abs(fd-dot))}
        return tests


def simulate(model:ShearModel,T=.12,dt=.001,frequency=10):
    state=model.prepare();e0,_=model.energy(state)
    rows=[];loss=0
    for t in range(round(T/dt)+1):
        if t%frequency==0 or t==round(T/dt):
            q,B,Z,p,v,vz=state
            E,parts=model.energy(state)
            s,off=model.shear_stats(B)
            r=np.sqrt(np.sum((B-Z)**2,axis=(-2,-1)))
            row={'time':float(t*dt),'charge':int(model.degree(q)),'energy':float(E),
                 'dissipated':float(loss),'energy_balance_rel':float((E+loss-e0)/e0),
                 'shear_norm_max':s,'offdiag_max':off,'btrace_abs_max':float(np.max(np.abs(np.trace(B,axis1=-2,axis2=-1)))),
                 'memory_lag_max':float(np.max(r)),'max_memory_radial_modulus':float(model.k+model.delta*np.tanh(np.max(r)/model.width)**2),
                 'unit_sphere_error':float(np.max(np.abs(np.sum(q*q,axis=-1)-1))), **parts}
            rows.append(row)
        if t<round(T/dt):
            state,dl=model.step(state,dt);loss+=dl
    return state,rows


def topology_contract(n=8,steps=201):
    coords,tets=make_mesh(n)
    qi=hedgehog(coords,center=(-.135,.065,-.035),radius=.69)
    theta=np.arccos(np.clip(qi[:,0],-1,1))
    norm=np.linalg.norm(qi[:,1:],axis=-1)
    dirs=qi[:,1:]/np.maximum(norm[:,None],1e-16)
    dirs[norm<1e-14]=[1,0,0]
    def path(t):
        ang=(1-t)*theta
        q=np.concatenate([np.cos(ang)[:,None],np.sin(ang)[:,None]*dirs],axis=-1)
        return q
    times=np.linspace(0,1,steps)
    rows=[]
    for t in times:
        q=path(t)
        deg=-degree_preimage(coords,tets,q)
        rows.append({'time':float(t),'degree':int(deg),'max_unit_error':float(np.max(np.abs(np.sum(q*q,axis=-1)-1)))})
    transitions=[(i-1,i) for i in range(1,len(rows)) if rows[i]['degree']!=rows[i-1]['degree']]
    if not transitions:raise AssertionError('not enough resolution to see transition')
    a,b=transitions[0]
    t0,t1=times[a],times[b]
    # With the path varying smoothly, det of four vertex vectors crosses zero at a singular tetrahedron.
    def dettet(q):return np.linalg.det(np.swapaxes(q[tets],1,2))
    d0,d1=dettet(path(t0)),dettet(path(t1))
    ids=np.flatnonzero((d0*d1<0) | ((np.abs(d0)<1e-14)^(np.abs(d1)<1e-14)))
    witness=None
    for idx in ids:
        fn=lambda tt:float(np.linalg.det(path(tt)[tets[idx]].T))
        try:t=brentq(fn,t0,t1,xtol=1e-14)
        except ValueError:continue
        M=path(t)[tets[idx]].T
        _,_,v=np.linalg.svd(M)
        coeff=v[-1]
        if np.max(coeff)<0:coeff=-coeff
        if np.min(coeff)>1e-8:
            coeff=coeff/np.sum(coeff)
            witness={'tetra_id':int(idx),'t':float(t),'barycentric':coeff.tolist(),
                     'zero_residual':float(np.linalg.norm(M@coeff)),
                     'domain_position':(coeff@coords[tets[idx]]).tolist(),
                     'root_det':float(np.linalg.det(M))}
            break
    if witness is None:
        # Degree change theorem still holds; stored root search is merely a numerical witness.
        witness={'not_found':'singular tetrahedron not isolated by first transition bracket'}
    return rows,{'grid_n':n,'degree_initial':rows[0]['degree'],'degree_final':rows[-1]['degree'],
                 'first_transition':[float(t0),float(t1)],'number_sign_change_tets':int(len(ids)),
                 'witness':witness}


def writecsv(path,rows):
    with open(path,'w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)


def main():
    out={}
    for n in [8,12]:
        rows,r=topology_contract(n)
        writecsv(HERE/f'contract_n{n}.csv',rows)
        out[f'topology_{n}']=r
    for n,dt,T in [(8,.002,.10),(8,.001,.10),(12,.002,.10)]:
        for full in ([True,False] if (n,dt)==(8,.002) else [True]):
            name=f'{"full" if full else "trace"}_n{n}_dt{str(dt).replace(".","p")}'
            model=ShearModel(n=n,full=full)
            checks=model.check_gradient()
            state,rows=simulate(model,T=T,dt=dt,frequency=5)
            writecsv(HERE/f'{name}.csv',rows)
            geom=model.regge(state[1])
            out[name]={'grad_checks':checks,'geometry':geom,'first':rows[0],'last':rows[-1],
                       'maximum_abs_energy_balance_error':max(abs(r['energy_balance_rel']) for r in rows),
                       'minimum_charge':min(r['charge'] for r in rows)}
            print(name,'charge',rows[-1]['charge'],'shear',rows[-1]['shear_norm_max'],
                  'E_balance',out[name]['maximum_abs_energy_balance_error'],
                  'deficit',geom['max_regge_deficit'],'minGram',geom['min_tet_gram_eig'],flush=True)
    (HERE/'audit_v13.json').write_text(json.dumps(out,indent=2,ensure_ascii=False))
    print('TOPO',json.dumps(out['topology_8']),flush=True)

if __name__=='__main__':main()