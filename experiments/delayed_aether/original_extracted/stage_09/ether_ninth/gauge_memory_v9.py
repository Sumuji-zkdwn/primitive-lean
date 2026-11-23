import numpy as np
from itertools import combinations

EDGES=list(combinations(range(5),2))
FACES=list(combinations(range(5),3))
BASIS=np.array([[[0,0,0],[0,0,-1],[0,1,0]], [[0,0,1],[0,0,0],[-1,0,0]], [[0,-1,0],[1,0,0],[0,0,0]]],float)

def hat(v): return np.einsum('a,aij->ij',v,BASIS)
def vee(X):return np.array([X[2,1],X[0,2],X[1,0]])
def rot(v):
    a=np.linalg.norm(v);X=hat(v)
    if a<1e-12:return np.eye(3)+X+0.5*X@X
    return np.eye(3)+np.sin(a)/a*X + (1-np.cos(a))/a**2*X@X

def edge_matrix(U,a,b):
    if a<b:return U[(a,b)]
    return U[(b,a)].T

def holonomy(U,face):
    a,b,c=face
    return edge_matrix(U,a,b)@edge_matrix(U,b,c)@edge_matrix(U,c,a)

def F_vector(U,face):
    H=holonomy(U,face)
    return vee(0.5*(H-H.T))

def energy(U,M,kappa=0.65):
    w=0.;mem=0.
    for f in FACES:
        H=holonomy(U,f)
        w+=3-np.trace(H)
        D=0.5*(H-H.T)-hat(M[f]);mem+=0.5*kappa*np.sum(D*D)
    return float(w+mem), float(w),float(mem)

def gradients(U,M,kappa=0.65):
    grad={e:np.zeros(3) for e in EDGES}
    for f in FACES:
        a,b,c=f
        paths=[(a,b),(b,c),(c,a)]
        mats=[edge_matrix(U,i,j) for i,j in paths]
        H=mats[0]@mats[1]@mats[2]
        D=0.5*(H-H.T)-hat(M[f])
        A=-np.eye(3)+kappa*D
        for k,(i,j) in enumerate(paths):
            e=tuple(sorted((i,j)));sgn=1 if i<j else -1
            P=np.eye(3)
            for t in range(k): P=P@mats[t]
            Q=np.eye(3)
            for t in range(k+1,3):Q=Q@mats[t]
            for axis in range(3):
                X=BASIS[axis]
                dT=X@mats[k] if sgn>0 else -mats[k]@X
                dH=P@dT@Q
                grad[e][axis]+=np.sum(A*dH)
    return grad

def transformed(U,M,G):
    Ut={e:G[e[0]]@matrix@G[e[1]].T for e,matrix in U.items()}
    Mt={f:G[f[0]]@vec for f,vec in M.items()}
    return Ut,Mt

def run(rng,steps=65, rate=.12, eta=.022, kick=.9):
    U={e:rot(rng.normal(size=3)*.12) for e in EDGES}
    M={f:F_vector(U,f) for f in FACES}
    e=(0,4); U[e]=rot(np.array([kick,0,0]))@U[e]
    out=[]
    for t in range(steps+1):
        E,W,EM=energy(U,M)
        max_gap=max(np.linalg.norm(F_vector(U,f)-M[f]) for f in FACES)
        stiff=max(1+3*np.tanh(np.linalg.norm(F_vector(U,f)-M[f])/.24)**2 for f in FACES)
        out.append([t,E,W,EM,max_gap,stiff])
        if t==steps:break
        gr=gradients(U,M)
        U={e:rot(-eta*gr[e])@U[e] for e in EDGES}
        M={f:(1-rate)*M[f]+rate*F_vector(U,f) for f in FACES}
    return np.asarray(out),U,M

def audit():
    rng=np.random.default_rng(20261122)
    Ut={e:rot(rng.normal(size=3)*.3) for e in EDGES}
    Mt={f:rng.normal(size=3)*.2 for f in FACES}
    G={i:rot(rng.normal(size=3)*.8) for i in range(5)}
    Ut2,Mt2=transformed(Ut,Mt,G)
    print('gauge E',energy(Ut,Mt),energy(Ut2,Mt2))
    gg=gradients(Ut,Mt);gg2=gradients(Ut2,Mt2)
    print('gauge gradient err',max(np.linalg.norm(gg2[e]-G[e[0]]@gg[e]) for e in EDGES))
    for e in EDGES[:2]:
        axis=0;h=1e-6
        Uplus=dict(Ut);Uminus=dict(Ut)
        Uplus[e]=rot(h*np.eye(3)[axis])@Ut[e];Uminus[e]=rot(-h*np.eye(3)[axis])@Ut[e]
        num=(energy(Uplus,Mt)[0]-energy(Uminus,Mt)[0])/(2*h)
        print('gradient numerical',e,axis,num,gg[e][axis])
    out,Uend,Mend=run(rng)
    print('dynamics energies',out[0],out[-1],'monotone',bool((np.diff(out[:,1])<=1e-11).all()), 'max rises',max(np.diff(out[:,1])))
    # test equivariance of one simultaneous nonlinear update (gradient and memory)
    g1=gradients(Ut,Mt); link_step={e:rot(-.02*g1[e])@Ut[e] for e in EDGES}
    mem_step={f:.87*Mt[f]+.13*F_vector(link_step,f) for f in FACES}
    g2=gradients(Ut2,Mt2);link_step2={e:rot(-.02*g2[e])@Ut2[e] for e in EDGES}
    mem_step2={f:.87*Mt2[f]+.13*F_vector(link_step2,f) for f in FACES}
    linkerr=max(np.linalg.norm(link_step2[e]-G[e[0]]@link_step[e]@G[e[1]].T) for e in EDGES)
    memerr=max(np.linalg.norm(mem_step2[f]-G[f[0]]@mem_step[f]) for f in FACES)
    print('step covariance',linkerr,memerr)
    return out

if __name__=='__main__': audit()
