import numpy as np
from itertools import combinations

OUT=np.array([[1.,1.,1.],[-1.,-1.,1.],[-1.,1.,-1.],[1.,-1.,-1.]])
BASE=np.linalg.norm(OUT,axis=1)
TETS=[tuple(sorted((4,)+t)) for t in combinations(range(4),3)]
OUTEDGES={(i,j):float(np.linalg.norm(OUT[i]-OUT[j])) for i,j in combinations(range(4),2)}

def length(a,b,r):
    if a==4:return float(r[b]);
    if b==4:return float(r[a]);
    return OUTEDGES[tuple(sorted((a,b)))]

def dihedral(tet,edge,r):
    a,b=edge
    c,d=[x for x in tet if x not in edge]
    x=length(a,b,r); y=length(a,c,r); z=length(a,d,r)
    bc=length(b,c,r);bd=length(b,d,r);cd=length(c,d,r)
    ec=(x*x+y*y-bc*bc)/2;ed=(x*x+z*z-bd*bd)/2
    cdot=(y*y+z*z-cd*cd)/2
    proj_c=y*y-(ec/x)**2;proj_d=z*z-(ed/x)**2
    val=(cdot-ec*ed/x**2)/np.sqrt(proj_c*proj_d)
    if not (-1.-1e-10<val<1+1e-10):raise ValueError((tet,edge,r,val))
    return float(np.arccos(np.clip(val,-1,1)))

def deficit(r):
    return np.array([2*np.pi-sum(dihedral(tet,(4,i),r) for tet in TETS if i in tet) for i in range(4)])

def boundary_exterior_angles(r):
    return np.array([np.pi-sum(dihedral(tet,(i,j),r) for tet in TETS if i in tet and j in tet) for i,j in OUTEDGES])

def action(r):
    return float(np.dot(r,deficit(r))+np.dot(list(OUTEDGES.values()),boundary_exterior_angles(r)))

def J(r,eps=1e-5):
    return np.column_stack([(deficit(r+np.eye(4)[i]*eps)-deficit(r-np.eye(4)[i]*eps))/(2*eps) for i in range(4)])

if __name__=='__main__':
    print('tets',TETS,'base',BASE, 'flat deficit',deficit(BASE), 'action',action(BASE))
    print('J0',J(BASE), 'eig',np.linalg.eigvalsh((J(BASE)+J(BASE).T)/2))
    rng=np.random.default_rng(22)
    for pct in [0.02,0.05,0.08,0.12,0.18]:
        r=BASE.copy();r[0]*=1+pct
        print('p',pct, 'def',deficit(r),'eig',np.linalg.eigvalsh(J(r)), 'asym',np.linalg.norm(J(r)-J(r).T))
    r=BASE.copy();r[0]*=1.08
    v=np.array([0.07,-0.025,0.03]); rflat=np.linalg.norm(OUT-v,axis=1); rcurv=r+(rflat-BASE)
    print('moved flat',deficit(rflat),'moved curved',deficit(rcurv),'change',deficit(rcurv)-deficit(r))
    print('grad action',np.array([(action(r+np.eye(4)[i]*1e-5)-action(r-np.eye(4)[i]*1e-5))/2e-5 for i in range(4)]),'vs def',deficit(r))
