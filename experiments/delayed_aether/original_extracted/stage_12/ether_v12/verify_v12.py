#!/usr/bin/env python3
"""Self-consistent, finite-dimensional field/metric/memory model (not GR).

Fixed-boundary q in S^3, conformal intrinsic edge metric exp((b_i+b_j)/2),
relaxing internal z. Potential V2+V4+Vmetric+Vmem is derived from the ONE
semidiscrete action with Rayleigh dissipation on z only. No prescribed q motion.

Use exact sphere-geodesic kinetic drift and potential kick, symmetric splitting;
damping is applied to memory momentum. Inhomogeneous z and b and q all evolve.
No claim of Lorentz invariance, Einstein gravity, gauge preservation or genuine
stable particles. q topological charge is checked under a finite mesh preimage
algorithm from verify_v11.py.
"""
import argparse, csv, hashlib, json, sys
from pathlib import Path
import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))  # bundled v11 geometry/degree helper
from verify_v11 import hedgehog, make_mesh, degree_preimage, unique_edges, metric_geometry

AXES = tuple(range(3))
PAIRS = ((0,1),(0,2),(1,2))


def edge_slices(axis, n):
    l=[slice(None)]*4; r=l.copy()
    l[axis]=slice(0,n-1);r[axis]=slice(1,n)
    return tuple(l),tuple(r)


def face_slices(i,j,n):
    p=[slice(None)]*4;p[i]=slice(0,n-1);p[j]=slice(0,n-1)
    ai=p.copy();ai[i]=slice(1,n)
    aj=p.copy();aj[j]=slice(1,n)
    return tuple(p),tuple(ai),tuple(aj)


def scalar_slice(idx):
    return idx[:3]


def logcosh(x):
    # stable for all finite x
    a=np.abs(x)
    return a+np.log1p(np.exp(-2*a))-np.log(2.)


class Model:
    def __init__(self,n=12,c2=1.,c4=.08249624119,K=.5,m2=1.2,
                 mu_b=1.,mu_z=.75,k=.55,delta=3.,width=.035,
                 gamma=0.6,coupled=True,alpha=.15,barrier=0.,s_cut=.15):
        self.n=n;self.N=n+1;self.dx=2/n;self.cell=self.dx**3
        self.c2=c2;self.c4=c4;self.K=K;self.m2=m2;self.mu_b=mu_b;self.mu_z=mu_z
        self.k=k;self.delta=delta;self.width=width;self.gamma=gamma;self.coupled=coupled;self.alpha=alpha;self.barrier=barrier;self.s_cut=s_cut
        coords,tets=make_mesh(n)
        self.coords=coords;self.tets=tets
        X=coords.reshape(self.N,self.N,self.N,3)
        self.X=X
        mask=np.any(np.isclose(np.abs(X),1,atol=1e-13),axis=-1)
        self.boundary=mask
        self.interior=~mask
        self.vacuum=np.array([1.,0.,0.,0.])
        self.edges,self.edgeinv=unique_edges(tets)

    def prepare(self,kick=.18):
        n=self.N
        q=hedgehog(self.coords,center=(-.135,.065,-.035),radius=.69).reshape((n,n,n,4))
        b=np.zeros((n,n,n));z=b.copy()
        p=np.zeros_like(q)
        p[1:-1]=(-kick)*(q[2:]-q[:-2])/(2*self.dx)
        p-=np.sum(p*q,axis=-1,keepdims=True)*q
        p[self.boundary]=0
        vb=np.zeros_like(b);vz=np.zeros_like(z)
        return (q,b,z,p,vb,vz)

    def potential(self,q,b,z,gradient=True):
        n=self.N; dx=self.dx;c=self.cell
        E2=E4=Eg=Ebar=0.
        if gradient:
            gq=np.zeros_like(q);gb=np.zeros_like(b);gz=np.zeros_like(z)
        else:gq=gb=gz=None
        for axis in AXES:
            aidx,zidx=edge_slices(axis,n);als=scalar_slice(aidx);zls=scalar_slice(zidx)
            dq=(q[zidx]-q[aidx])/dx
            d2=np.einsum('...c,...c->...',dq,dq)
            if self.coupled:
                weight=np.exp(self.alpha*(b[als]+b[zls])/2)
            else:weight=1.
            E2 += (self.c2*c/2)*np.sum(weight*d2)
            if gradient:
                force=self.c2*c/dx*(weight[...,None]*dq if self.coupled else dq)
                gq[aidx]-=force;gq[zidx]+=force
                if self.coupled:
                    bg=self.alpha*self.c2*c/4*weight*d2
                    gb[als]+=bg;gb[zls]+=bg
        for i,j in PAIRS:
            base,ip,jp=face_slices(i,j,n)
            base3=scalar_slice(base)
            da=(q[ip]-q[base])/dx;db=(q[jp]-q[base])/dx
            aa=np.sum(da*da,axis=-1);bb=np.sum(db*db,axis=-1);ab=np.sum(da*db,axis=-1)
            wedge=np.maximum(0.,aa*bb-ab*ab) # theoretically nonnegative
            if self.coupled:
                weight=np.exp(-self.alpha*b[base3])
            else:weight=1.
            E4 += self.c4*c/2*np.sum(weight*wedge)
            if gradient:
                f_i=(self.c4*c/dx)*(weight[...,None] if self.coupled else 1.)*(bb[...,None]*da-ab[...,None]*db)
                f_j=(self.c4*c/dx)*(weight[...,None] if self.coupled else 1.)*(aa[...,None]*db-ab[...,None]*da)
                gq[base]-=f_i+f_j;gq[ip]+=f_i;gq[jp]+=f_j
                if self.coupled:gb[base3]-=self.alpha*self.c4*c/2*weight*wedge
        for axis in AXES:
            aidx,zidx=edge_slices(axis,n);als=scalar_slice(aidx);zls=scalar_slice(zidx)
            db=(b[zls]-b[als])/dx
            Eg+=(self.K*c/2)*np.sum(db*db)
            if gradient:
                force=self.K*c/dx*db
                gb[als]-=force;gb[zls]+=force
        Eg += .5*self.m2*c*np.sum(b*b)
        if gradient:gb+=self.m2*c*b
        if self.barrier>0:
            qflat=q.reshape(-1,4)
            prod=np.einsum('ic,ic->i',qflat[self.edges[:,0]],qflat[self.edges[:,1]])
            if np.any(prod<=0):
                raise ValueError(f"inadmissible edge dot product {np.min(prod)}")
            ids=np.nonzero(prod<self.s_cut)[0]
            if len(ids):
                aa=self.edges[ids,0]; bb=self.edges[ids,1]
                sv=prod[ids]
                diff=self.s_cut/sv-1.
                Ebar=self.barrier*np.sum(diff*diff)
                if gradient:
                    derivative=-2*self.barrier*diff*self.s_cut/(sv*sv)
                    np.add.at(gq.reshape(-1,4),aa,derivative[:,None]*qflat[bb])
                    np.add.at(gq.reshape(-1,4),bb,derivative[:,None]*qflat[aa])
        y=b-z
        a=np.abs(y/self.width)
        phi=.5*(self.k+self.delta)*y*y-self.delta*self.width**2*logcosh(y/self.width)
        Em=c*np.sum(phi)
        if gradient:
            dphi=(self.k+self.delta)*y-self.delta*self.width*np.tanh(y/self.width)
            gb+=c*dphi;gz-=c*dphi
            gq[self.boundary]=0
            gb[self.boundary]=0;gz[self.boundary]=0
        return E2+E4+Eg+Em+Ebar,(E2,E4,Eg,Em,Ebar),(gq,gb,gz)

    def kinetic(self,p,vb,vz):
        return .5*self.cell*(np.sum(p*p)+self.mu_b*np.sum(vb*vb)+self.mu_z*np.sum(vz*vz))

    def energy(self,state):
        q,b,z,p,vb,vz=state
        v,components,_=self.potential(q,b,z,gradient=False)
        t=self.kinetic(p,vb,vz)
        return t+v, dict(zip(['E2','E4','Emetric','Ememory','Eadmissibility'],map(float,components))) | {'T':float(t)}

    def kick(self,q,b,z,p,vb,vz,h):
        _,_,(gq,gb,gz)=self.potential(q,b,z,gradient=True)
        gq-=np.sum(gq*q,axis=-1,keepdims=True)*q
        p=p-h*gq/self.cell
        vb=vb-h*gb/(self.mu_b*self.cell)
        vz=vz-h*gz/(self.mu_z*self.cell)
        p[self.boundary]=0;vb[self.boundary]=0;vz[self.boundary]=0
        return p,vb,vz

    def drift(self,q,b,z,p,vb,vz,h):
        p_abs=np.linalg.norm(p,axis=-1,keepdims=True)
        angle=h*p_abs
        coefficient=np.sinc(angle/np.pi)*h # sin(angle)/|p|, safe at 0
        q_new=q*np.cos(angle)+p*coefficient
        p_new=p*np.cos(angle)-q*(p_abs*np.sin(angle))
        b_new=b+h*vb
        z_new=z+h*vz
        q_new[self.boundary]=self.vacuum;p_new[self.boundary]=0
        b_new[self.boundary]=0;z_new[self.boundary]=0
        return q_new,b_new,z_new,p_new,vb,vz

    def step(self,state,h,return_loss=False):
        q,b,z,p,vb,vz=state
        # Stagger friction to respect time reversal when gamma=0.
        factor=np.exp(-self.gamma*h/(2*self.mu_z))
        loss1=.5*self.cell*self.mu_z*(1-factor**2)*np.sum(vz*vz)
        vz=vz*factor
        p,vb,vz=self.kick(q,b,z,p,vb,vz,h/2)
        q,b,z,p,vb,vz=self.drift(q,b,z,p,vb,vz,h)
        p,vb,vz=self.kick(q,b,z,p,vb,vz,h/2)
        loss2=.5*self.cell*self.mu_z*(1-factor**2)*np.sum(vz*vz)
        vz=vz*factor
        ans=(q,b,z,p,vb,vz)
        return (ans,float(loss1+loss2)) if return_loss else ans

    def degree(self,q):
        return -degree_preimage(self.coords,self.tets,q.reshape(-1,4))

    def charge_core_centroid(self,q):
        w=np.maximum(0.,1-q[...,0])
        return np.sum(self.X*w[...,None],axis=(0,1,2))/np.sum(w)

    def curvature(self,b):
        geom=metric_geometry(self.coords,self.tets,self.edges,self.edgeinv,(self.alpha*b).reshape(-1))
        return dict(max_deficit=float(geom['max_flat_residual']),
                    regge_abs_curvature=float(geom['regge_abs_curvature']),
                    min_gram_eigenvalue=float(geom['min_gram_eigenvalue']))

    def check_gradient(self):
        rng=np.random.default_rng(1427)
        q,b,z,_,_,_=self.prepare()
        b[self.interior]=rng.normal(0,.018,np.count_nonzero(self.interior))
        z[self.interior]=rng.normal(0,.017,np.count_nonzero(self.interior))
        E,_,(gq,gb,gz)=self.potential(q,b,z)
        outputs={}
        for tag in ('q','b','z'):
            if tag=='q':
                direction=rng.normal(size=q.shape)
                direction -= np.sum(q*direction,axis=-1,keepdims=True)*q
                direction[self.boundary]=0
                direction/=np.linalg.norm(direction)
                def pert(e):return (q+e*direction,b,z)
                dot=np.sum(direction*gq)
            else:
                direction=rng.normal(size=b.shape);direction[self.boundary]=0
                direction/=np.linalg.norm(direction)
                def pert(e):return (q,b+e*direction,z) if tag=='b' else (q,b,z+e*direction)
                dot=np.sum(direction*(gb if tag=='b' else gz))
            eps=1e-5
            pp=self.potential(*pert(eps),gradient=False)[0]
            mm=self.potential(*pert(-eps),gradient=False)[0]
            fd=(pp-mm)/(2*eps)
            relative=abs(fd-dot)/max(1,abs(fd),abs(dot))
            outputs[tag]={'analytic':float(dot),'finite_diff':float(fd),'relative_error':float(relative)}
        return outputs


def simulate(m,dt,T,sample_every,coupled=True, check_degree=True):
    state=m.prepare()
    rows=[]
    E0,_=m.energy(state)
    dissipated=0.
    for s in range(round(T/dt)+1):
        if s%sample_every==0 or s==round(T/dt):
            q,b,z,p,vb,vz=state
            energy,part=m.energy(state)
            max_y=float(np.max(np.abs(b-z)))
            stiff_max=float(m.k+m.delta*np.tanh(max_y/m.width)**2)
            cr=m.charge_core_centroid(q)
            row={'step':s,'time':round(s*dt,10),'total_energy':float(energy),
                'relative_energy_change':float((energy-E0)/E0),
                'dissipated':float(dissipated),
                'balance_error':float((energy+dissipated-E0)/E0),
                'core_x':float(cr[0]),'core_y':float(cr[1]),'core_z':float(cr[2]),
                'max_abs_b':float(np.max(np.abs(b))),
                'max_abs_z':float(np.max(np.abs(z))),
                'min_pair_dot':float(np.min(np.einsum('ic,ic->i',q.reshape(-1,4)[m.edges[:,0]],q.reshape(-1,4)[m.edges[:,1]]))),
                'rms_lag':float(np.sqrt(np.mean((b-z)**2))),
                'max_memory_modulus':stiff_max,
                'max_unit_error':float(np.max(np.abs(np.sum(q*q,axis=-1)-1))),
                'max_tangent_error':float(np.max(np.abs(np.sum(q*p,axis=-1)))),
                **part}
            if check_degree: row['charge']=m.degree(q)
            rows.append(row)
        if s<round(T/dt):
            state,loss=m.step(state,dt,return_loss=True)
            dissipated+=loss
    return state,rows


def save_csv(path, rows):
    with path.open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)


def main():
    pa=argparse.ArgumentParser()
    pa.add_argument('--n',type=int,default=12)
    pa.add_argument('--dt',type=float,default=.003)
    pa.add_argument('--T',type=float,default=.6)
    pa.add_argument('--sample-every',type=int,default=10)
    pa.add_argument('--label',default='main')
    pa.add_argument('--control',action='store_true')
    pa.add_argument('--alpha',type=float,default=.15)
    pa.add_argument('--barrier',type=float,default=0.)
    pa.add_argument('--s-cut',type=float,default=.15)
    a=pa.parse_args()
    model=Model(n=a.n,coupled=not a.control,alpha=a.alpha,barrier=a.barrier,s_cut=a.s_cut)
    grad=model.check_gradient()
    print('gradient',json.dumps(grad))
    if max(v['relative_error'] for v in grad.values())>2e-6:raise AssertionError('gradient check failed')
    state,rows=simulate(model,a.dt,a.T,a.sample_every)
    path=HERE/f'{a.label}_timeseries.csv';save_csv(path,rows)
    q,b,z,p,vb,vz=state
    bgeom=model.curvature(b)
    audit={'grid_n':a.n,'dt':a.dt,'T':a.T,'control_no_q_geometry_coupling':a.control,'metric_coupling_alpha':a.alpha,
           'admissibility_barrier':a.barrier,'s_cut':a.s_cut,
           'degree_initial':rows[0]['charge'],'degree_final':rows[-1]['charge'],
           'charge_observations':sorted(set(r['charge'] for r in rows)),
           'max_norm_error':max(r['max_unit_error'] for r in rows),
           'max_tangent_error':max(r['max_tangent_error'] for r in rows),
           'initial_energy':rows[0]['total_energy'],'final_energy':rows[-1]['total_energy'],
           'rel_energy_change':rows[-1]['relative_energy_change'],
           'relative_energy_balance_error':rows[-1]['balance_error'],
           'max_abs_energy_balance_error':max(abs(r['balance_error']) for r in rows),
           'dissipated':rows[-1]['dissipated'],
           'core_shift_x':rows[-1]['core_x']-rows[0]['core_x'],
           'metric':bgeom,'max_memory_modulus':max(r['max_memory_modulus'] for r in rows),
           'max_b':max(r['max_abs_b'] for r in rows),
           'minimum_edge_dot':min(r['min_pair_dot'] for r in rows),
           'gradient_audit':grad,
           'datafile':str(path.name)}
    (HERE/f'{a.label}_audit.json').write_text(json.dumps(audit,indent=2,ensure_ascii=False))
    print('AUDIT',json.dumps(audit,ensure_ascii=False))

if __name__=='__main__':main()
