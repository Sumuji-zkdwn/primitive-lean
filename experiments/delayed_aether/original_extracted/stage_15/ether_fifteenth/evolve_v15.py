"""Genuine IVP time-integration of homogeneous nonlinear vacuum ADM (Kasner).

R_ij=0, N=1, beta=0.  Numerical evolution is independent of the exact
Kasner expression used for the initial data and comparison at final time.
"""
from pathlib import Path
import csv, json
import numpy as np
P=np.array([-2/7,3/7,6/7],float)
M=np.array([[1.,2.,-1.],[1.,-1.,2.],[2.,-1.,-1.]])
Q,_=np.linalg.qr(M)

def exact(t):
    g=Q@np.diag(t**(2*P))@Q.T
    k=-Q@np.diag(P*t**(2*P-1))@Q.T
    return g,k

def rhs(g,k):
    inv=np.linalg.inv(g)
    kmix=inv@k
    return -2*k, np.trace(kmix)*k-2*k@inv@k

def rk4(g,k,dt):
    dg1,dk1=rhs(g,k)
    dg2,dk2=rhs(g+dt*dg1/2,k+dt*dk1/2)
    dg3,dk3=rhs(g+dt*dg2/2,k+dt*dk2/2)
    dg4,dk4=rhs(g+dt*dg3,k+dt*dk3)
    gn=g+dt/6*(dg1+2*dg2+2*dg3+dg4)
    kn=k+dt/6*(dk1+2*dk2+2*dk3+dk4)
    return (gn+gn.T)/2,(kn+kn.T)/2

def ham(g,k):
    kmix=np.linalg.solve(g,k)
    return float(np.trace(kmix)**2 - np.trace(kmix@kmix))

def run(out):
    out=Path(out);t0=0.4;duration=1.2
    summ=[]; trace=[]
    for steps in (12,24,48,96,192):
        dt=duration/steps
        g,k=exact(t0)
        H0=ham(g,k);maxH=abs(H0);mindet=np.linalg.det(g)
        for i in range(steps):
            g,k=rk4(g,k,dt)
            t=t0+dt*(i+1)
            hh=ham(g,k)
            maxH=max(maxH,abs(hh))
            mindet=min(mindet,float(np.linalg.det(g)))
            if steps==96 and i%4==0:
                trace.append(dict(t=t,H=hh,offdiag_g=float(g[0,1]),offdiag_K=float(k[0,1])))
        ga,ka=exact(t0+duration)
        summ.append(dict(dt=dt,steps=steps,maxH=maxH,final_H=abs(ham(g,k)),metric_max_error=float(np.max(np.abs(g-ga))),K_max_error=float(np.max(np.abs(k-ka))),min_g_eig=float(np.linalg.eigvalsh(g)[0]),min_g_det=mindet))
        print('IVP',steps,'hmax',f'{maxH:.3e}','gerr',f'{np.max(np.abs(g-ga)):.3e}','Kerr',f'{np.max(np.abs(k-ka)):.3e}')
    with (out/'kasner_IVP_convergence.csv').open('w',newline='') as fh:
        w=csv.DictWriter(fh,fieldnames=list(summ[0]));w.writeheader();w.writerows(summ)
    with (out/'kasner_IVP_trace.csv').open('w',newline='') as fh:
        w=csv.DictWriter(fh,fieldnames=list(trace[0]));w.writeheader();w.writerows(trace)
    return summ
if __name__=='__main__':run(Path(__file__).parent)
