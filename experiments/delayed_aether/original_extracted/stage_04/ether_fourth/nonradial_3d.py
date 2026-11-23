#!/usr/bin/env python3
"""Full 3D (not radially restricted) finite-difference static energy test.

q: R^3 -> S^3, rho2 = 0.5 |dq|^2, rho4 = 0.5 sum_{i<j}|dq_i wedge dq_j|^2.
The h minimizer solves (-K Delta + g^2 rho2) h = g rho2 with Dirichlet
boundary fixed to the radial solution. This is a variational test only,
not an all-deformations stability theorem or a 3D time evolution.
"""
from __future__ import annotations
from pathlib import Path
import csv, math, argparse, time
import numpy as np
from scipy.fft import dstn,idstn
from scipy.sparse.linalg import LinearOperator,cg
from scipy.ndimage import gaussian_filter
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from radial_profile_positive import Radial

P=Path(__file__).resolve().parent
PI=np.pi; K=1.; g=.5

class Testbed:
    def __init__(self,n,dx,profile):
        assert n%2==1
        self.n=n;self.dx=dx;self.shape=(n,n,n)
        xyz=(np.arange(n)-(n-1)/2)*dx
        self.X,self.Y,self.Z=np.meshgrid(xyz,xyz,xyz,indexing='ij',sparse=True)
        self.X=self.X+np.zeros(self.shape)
        self.Y=self.Y+np.zeros(self.shape)
        self.Z=self.Z+np.zeros(self.shape)
        self.r=np.sqrt(self.X**2+self.Y**2+self.Z**2)
        self.Fnodes=np.r_[np.pi,profile[0],0.]
        self.rnodes=np.arange(len(self.Fnodes))*.16
        self.hnodes=profile[1]
        self.hrnodes=(np.arange(len(self.hnodes))+.5)*.16
        self.hbd=np.interp(self.r,self.hrnodes,self.hnodes)
        self.nn=n-2
        # -K Delta Dirichlet preconditioner, spectral DST-I exact.
        kk=np.arange(1,self.nn+1,dtype=float)
        cosv=np.cos(np.pi*kk/(self.nn+1))
        self.eigen=(2*K/dx**2)*(3-cosv[:,None,None]-cosv[None,:,None]-cosv[None,None,:])

    def hedgehog(self,A=None,shift=(0.,0.,0.)):
        if A is None:A=np.eye(3)
        X=self.X-shift[0];Y=self.Y-shift[1];Z=self.Z-shift[2]
        x=A[0,0]*X+A[0,1]*Y+A[0,2]*Z
        y=A[1,0]*X+A[1,1]*Y+A[1,2]*Z
        z=A[2,0]*X+A[2,1]*Y+A[2,2]*Z
        r=np.sqrt(x*x+y*y+z*z)
        F=np.interp(r,self.rnodes,self.Fnodes,left=PI,right=0)
        sine_over_r=np.divide(np.sin(F),r,out=np.zeros_like(F),where=r>1e-10)
        q=np.stack([np.cos(F),sine_over_r*x,sine_over_r*y,sine_over_r*z],axis=-1)
        return q

    @staticmethod
    def static_densities(q,degree=False):
        # center differences on interior, vacuum at outer edges.
        d0=(q[2:,1:-1,1:-1,:]-q[:-2,1:-1,1:-1,:])
        d1=(q[1:-1,2:,1:-1,:]-q[1:-1,:-2,1:-1,:])
        d2=(q[1:-1,1:-1,2:,:]-q[1:-1,1:-1,:-2,:])
        # unscaled values of derivatives, physical dx supplied by caller.
        s0=np.sum(d0*d0,axis=-1);s1=np.sum(d1*d1,axis=-1);s2=np.sum(d2*d2,axis=-1)
        c01=np.sum(d0*d1,axis=-1);c02=np.sum(d0*d2,axis=-1);c12=np.sum(d1*d2,axis=-1)
        return d0,d1,d2,s0,s1,s2,c01,c02,c12

    def density(self,q,with_degree=False):
        d0,d1,d2,s0,s1,s2,c01,c02,c12=self.static_densities(q)
        rho2=.5*(s0+s1+s2)/(2*self.dx)**2
        rho4=.5*(s0*s1-c01*c01+s0*s2-c02*c02+s1*s2-c12*c12)/(2*self.dx)**4
        rho4=np.maximum(rho4,0)
        if not with_degree:return rho2,rho4,None
        p=q[1:-1,1:-1,1:-1,:]
        mat=np.stack([p,d0/(2*self.dx),d1/(2*self.dx),d2/(2*self.dx)],axis=-2)
        degree=-np.linalg.det(mat).sum()*self.dx**3/(2*PI**2)
        return rho2,rho4,float(degree)

    def lap(self,h):
        return (h[2:,1:-1,1:-1]+h[:-2,1:-1,1:-1]+
                h[1:-1,2:,1:-1]+h[1:-1,:-2,1:-1]+
                h[1:-1,1:-1,2:]+h[1:-1,1:-1,:-2]-6*h[1:-1,1:-1,1:-1])/self.dx**2

    def solve_h(self,rho2,rtol=2e-10):
        hb=self.hbd
        r=(g*rho2 + K*self.lap(hb)-g*g*rho2*hb[1:-1,1:-1,1:-1]).ravel()
        def mv(v):
            delta=np.zeros(self.shape)
            delta[1:-1,1:-1,1:-1]=v.reshape((self.nn,)*3)
            return (g*g*rho2*delta[1:-1,1:-1,1:-1]-K*self.lap(delta)).ravel()
        def pre(v):
            v3=v.reshape((self.nn,)*3)
            return idstn(dstn(v3,type=1,norm='ortho')/self.eigen,type=1,norm='ortho').ravel()
        ncol=self.nn**3
        op=LinearOperator((ncol,ncol),matvec=mv,dtype=float)
        m=LinearOperator((ncol,ncol),matvec=pre,dtype=float)
        count=[0]
        def cb(_):count[0]+=1
        delta,info=cg(op,r,M=m,rtol=rtol,atol=0.0,maxiter=300,callback=cb)
        if info!=0:raise RuntimeError(f'CG info {info}, residual={np.linalg.norm(mv(delta)-r)}')
        h=hb.copy()
        h[1:-1,1:-1,1:-1]+=delta.reshape((self.nn,)*3)
        residual=np.linalg.norm(mv(delta)-r)/(max(np.linalg.norm(r),1e-13))
        return h,residual,count[0]

    def energy(self,q,degree=False,with_h=True):
        rho2,rho4,B=self.density(q,with_degree=degree)
        if with_h:
            h,res,calls=self.solve_h(rho2)
        else:
            h=self.hbd;res=float('nan');calls=0
        hi=h[1:-1,1:-1,1:-1];v=g*hi
        c=1-v+.5*v*v
        e2=float(np.sum(c*rho2)*self.dx**3)
        e4=float(np.sum(rho4)*self.dx**3)
        # Edge gradient Dirichlet energy: any change of boundary affects constant.
        eh=float(.5*K*self.dx*(np.sum(np.diff(h,axis=0)**2)+np.sum(np.diff(h,axis=1)**2)+np.sum(np.diff(h,axis=2)**2)))
        return dict(E=e2+e4+eh,E2=e2,E4=e4,Eh=eh,B=B,solver_rel_residual=res,cg_iters=calls)

    def perturb(self,q,kind,eps,seed=11):
        r=self.r;X=self.X;Y=self.Y;Z=self.Z
        env=np.exp(-.5*(r/2.5)**2)
        if kind=='quadrupole':
            amplit=(X*Y/(1.+r*r))*env
            v=np.zeros_like(q)
            v[...,1]=amplit
            v[...,2]=-.7*amplit
        elif kind=='dipole':
            amplit=(X/(1.+r))*env
            v=np.zeros_like(q)
            v[...,2]=amplit
            v[...,3]=.5*amplit
        elif kind=='random':
            # Deterministic physically fixed Fourier perturbation; not a voxel-scale random field.
            rng=np.random.default_rng(seed)
            v=np.zeros_like(q)
            for a in range(4):
                for _ in range(7):
                    kv=rng.normal(size=3)*.65
                    phase=rng.uniform(-PI,PI)
                    coeff=rng.normal()
                    v[...,a]+=coeff*np.cos(kv[0]*X+kv[1]*Y+kv[2]*Z+phase)
            v*=env[...,None]
        elif kind=='angular':
            v=np.zeros_like(q)
            v[...,1]=np.sin(.8*Y)*np.cos(.4*Z)*env
            v[...,2]=np.sin(.6*Z)*np.cos(.9*X)*env
        else:raise ValueError(kind)
        v-=np.sum(q*v,axis=-1,keepdims=True)*q
        active=(r<3)
        rms=np.sqrt(np.mean(np.sum(v[active]**2,axis=-1)))
        if rms<1e-9:raise ValueError('bad perturb')
        v=v/rms
        # Geodesic on S^3 pointwise, exact norm preservation up to roundoff.
        vn=np.sqrt(np.sum(v*v,axis=-1,keepdims=True))
        angle=eps*vn
        qt=np.cos(angle)*q+np.sinc(angle/np.pi)*eps*v
        return qt


def do_run(n,dx,profile,do_all=True):
    t0=time.time()
    bed=Testbed(n,dx,profile)
    q0=bed.hedgehog()
    E0=bed.energy(q0,degree=True)
    print('GRID',n,dx,'baseline',E0,'seconds',time.time()-t0,flush=True)
    rows=[dict(n=n,dx=dx,kind='baseline',epsilon=0,**E0,delta_E=0,curvature=np.nan)]
    directions=[('affine',.10),('affine',.20),('shear',.13),('quadrupole',.04),('dipole',.04),('angular',.04),('random',.04),('translation',.15)]
    if not do_all:directions=[('affine',.15),('quadrupole',.04),('random',.04),('translation',.15)]
    for kind,eps in directions:
        en=[]
        for sign in (+1,-1):
            if kind in ('affine','shear','translation'):
                if kind=='affine':A=np.diag([np.exp(sign*eps),np.exp(-sign*eps),1.])
                elif kind=='shear':A=np.array([[1.,sign*eps,0],[0,1.,0],[0,0,1.]])
                else:A=np.eye(3)
                q=bed.hedgehog(A,shift=(sign*eps if kind=='translation' else 0,0,0))
            else:q=bed.perturb(q0,kind,sign*eps,seed=11)
            E=bed.energy(q,degree=True)
            en.append(E['E'])
            row=dict(n=n,dx=dx,kind=kind,epsilon=sign*eps,**E,
                     delta_E=E['E']-E0['E'],curvature=np.nan)
            rows.append(row)
            print('  ',kind,'eps',round(sign*eps,3),'E delta',round(row['delta_E'],7),'B',round(E['B'],6),
                  'res',format(E['solver_rel_residual'],'.1e'),'CG',E['cg_iters'],flush=True)
        curvature=(en[0]+en[1]-2*E0['E'])/eps**2
        for row in rows[-2:]:row['curvature']=curvature
        print('  ',kind,'symmetric curvature',round(curvature,6),flush=True)
    print('GRID DONE seconds',time.time()-t0,flush=True)
    return rows,E0


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--fast',action='store_true');ap.add_argument('--fine',action='store_true');args=ap.parse_args()
    R=Radial(L=16,dr=.16,alpha=.25)
    sol=R.optimize(maxiter=2500)
    dat=R.evaluate(sol.x,details=True)
    print('radial static E',dat['energy'],'B',dat['degree'],flush=True)
    profile=(sol.x,dat['h'])
    if args.fast:conditions=[(41,.30,False)]
    elif args.fine:conditions=[(91,.145,False)]
    else:conditions=[(49,.27,True),(61,.22,False)]
    rows=[];base=[]
    for n,dx,all_flag in conditions:
        out,baseline=do_run(n,dx,profile,do_all=all_flag)
        rows+=out;base.append((n,dx,baseline))
    tag='fine' if args.fine else 'quick' if args.fast else 'coarse_medium'
    with (P/f'nonradial_tests_{tag}.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
    # Plot energy response, 49^3 only for angle pair and 61^3 refinement as symbols.
    fig,ax=plt.subplots(figsize=(9,5.2))
    types=['affine','shear','quadrupole','dipole','angular','random','translation']
    for kind in types:
        rr=[r for r in rows if r['kind']==kind and r['n']==conditions[0][0]]
        if not rr:continue
        rr.sort(key=lambda a:a['epsilon'])
        ax.plot([r['epsilon'] for r in rr],[r['delta_E'] for r in rr],'o-',label=kind)
    ax.axhline(0,color='black',lw=1)
    ax.set(xlabel='Signed perturbation amplitude',ylabel='Energy change relative to radial baseline',title='Non-spherical variations with the scalar field re-optimized')
    ax.grid(alpha=.25);ax.legend();fig.tight_layout();fig.savefig(P/f'nonradial_energy_{tag}.png',dpi=165);plt.close(fig)
    # Symmetrized second variation plot
    groups=[]
    for r in rows:
        if r['epsilon']>0:groups.append(r)
    fig,ax=plt.subplots(figsize=(9,5))
    labels=[f"{r['kind']} ({r['n']})" for r in groups]
    vals=[r['curvature'] for r in groups]
    ax.bar(np.arange(len(vals)),vals)
    ax.axhline(0,lw=1,color='black')
    ax.set_xticks(np.arange(len(vals)),labels,rotation=32,ha='right')
    ax.set(ylabel='Symmetric curvature (energy/amplitude²)',title='Positive numerical curvatures only test the selected perturbations')
    fig.tight_layout();fig.savefig(P/f'nonradial_curvature_{tag}.png',dpi=165);plt.close(fig)
    if any(r['curvature']<0 for r in groups):print('WARNING negative curvature direction, investigate.',flush=True)
    return rows

if __name__=='__main__':main()
