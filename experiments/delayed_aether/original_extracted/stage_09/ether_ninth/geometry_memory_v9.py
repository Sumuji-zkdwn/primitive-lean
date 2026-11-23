import numpy as np
import regge_v9

def memory_phi(y,k=.8,delta=3.0,a=.16):
    u=y/a
    return .5*(k+delta)*y*y -delta*a*a*np.logaddexp(u,-u)+delta*a*a*np.log(2)

def memory_force(y,k=.8,delta=3.0,a=.16):
    return (k+delta)*y-delta*a*np.tanh(y/a)

def stiff(y,k=.8,delta=3.,a=.16):
    return k+delta*np.tanh(y/a)**2

def H(r,m,mu=.5):
    d=regge_v9.deficit(r)
    return .5*mu*np.dot(d,d)+np.sum(memory_phi(d-m))

def derivatives(r,m,mu=.5):
    d=regge_v9.deficit(r)
    f=memory_force(d-m)
    return regge_v9.J(r).T@(mu*d+f),-f

def simulate(n=240,eta=.007,gamma=.06):
    r=regge_v9.BASE.copy();r[0]*=1.08
    m=np.zeros(4)
    out=[]
    for t in range(n+1):
        d=regge_v9.deficit(r)
        out.append([t,H(r,m),np.linalg.norm(d),max(abs(d)),np.linalg.norm(d-m),max(stiff(d-m)),*r])
        if t==n:break
        dr,dm=derivatives(r,m)
        # coordinate descent, memory adjustment and geometry adjustment
        # backtrack when needed, guaranteeing test-step decrease, not an analytic proof
        step=eta
        for _ in range(18):
            rnext=r-step*dr
            mn=m-gamma*dm
            try:
                if H(rnext,mn)<=H(r,m)+1e-12:break
            except (ValueError,RuntimeWarning):pass
            step*=.5
        else:raise RuntimeError(('line search failed',t))
        r,m=rnext,mn
    return np.array(out)

if __name__=='__main__':
    d=simulate()
    print('start',d[0]);print('end',d[-1]);print('max change',max(np.diff(d[:,1])))
    from pathlib import Path
    np.savetxt(Path(__file__).with_name('geometry_memory_timeseries.csv'),d,delimiter=',',header='step,energy,curvature_l2,max_curvature,memory_gap_l2,max_stiffness,r0,r1,r2,r3',comments='')
