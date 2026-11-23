#!/usr/bin/env python3
"""Independent test: time-reparam invariance allows e^(alpha S)Q/N for ANY alpha."""
import csv,json
from pathlib import Path
import numpy as np
from scipy.integrate import solve_ivp
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
P=Path(__file__).resolve().parent
D,w,mu=3.,.45,1.2
q0,z0,u0,r0=.55,-.16,.18,-.075
initial_y=z0-q0
A0=1+D*np.tanh(initial_y/w)**2
Km0=.5*(A0*u0*u0+r0*r0)
V0=.5*mu**2*initial_y**2
anis=np.array([.048,-.032,-.016]); H0=np.sqrt((anis@anis+Km0+V0)/6)
init=np.r_[np.zeros(3),q0,z0,H0+anis,u0,r0]
t=np.linspace(0,7,701)

def odes(t,x,alpha):
    b=x[:3];q,z=x[3:5];v=x[5:8];vq,vz=x[8:]
    S=sum(b);H=sum(v);Q=v@v-H**2;y=z-q
    tanh=np.tanh(y/w)
    A=1+D*tanh**2;Ap=2*D/w*tanh*(1-tanh*tanh)
    K=.5*(A*vq*vq+vz*vz);V=.5*mu**2*y*y
    target=.5*(alpha*Q+np.exp((1-alpha)*S)*(K-V))-alpha*H*(v-H)
    acc=target-.5*sum(target)
    dvq=(-H*A*vq-Ap*(vz-vq)*vq-.5*Ap*vq*vq+mu**2*y)/A
    dvz=-H*vz+.5*Ap*vq*vq-mu**2*y
    return np.r_[v,vq,vz,acc,dvq,dvz]

results=[];traces=[]
for alpha in (0.,1.,2.):
    sol=solve_ivp(lambda t,x: odes(t,x,alpha),(0,7),init,rtol=2e-12,atol=2e-12,method='DOP853',t_eval=t)
    assert sol.success
    err=[]; scales=[]
    for x in sol.y.T:
        S=sum(x[:3]); v=x[5:8];q,z=x[3:5];vq,vz=x[8:]
        Q=v@v-sum(v)**2; A=1+D*np.tanh((z-q)/w)**2
        K=.5*(A*vq*vq+vz*vz); V=.5*mu**2*(z-q)**2
        constraint=np.exp(alpha*S)*Q+np.exp(S)*(K+V)
        err.append(constraint);scales.append(np.exp(S/3))
    err=np.array(err);scales=np.array(scales)
    assert max(abs(err))<2e-9,(alpha,max(abs(err)))
    results.append({'alpha':alpha,'final_scale':float(scales[-1]),'final_q':float(sol.y[3,-1]),
                    'final_z':float(sol.y[4,-1]),'max_lapse_constraint':float(max(abs(err)))})
    traces.append((alpha,scales,err))
with (P/'volume_ambiguity_v22.csv').open('w',newline='') as f:
    wr=csv.writer(f);wr.writerow(['time']+[f'scale_alpha_{int(x[0])}' for x in traces]+[f'lapse_constraint_alpha_{int(x[0])}' for x in traces])
    for i,ti in enumerate(t): wr.writerow([ti]+[tr[1][i] for tr in traces]+[tr[2][i] for tr in traces])
fig,ax=plt.subplots(figsize=(7.8,4.5))
for alpha,scale,err in traces: ax.plot(t,scale,label=f'alpha={alpha:g} (same time-gauge symmetry)')
ax.legend();ax.set_xlabel('model time');ax.set_ylabel('geometric scale exp(S/3)')
fig.tight_layout();fig.savefig(P/'volume_ambiguity_v22.png',dpi=170);plt.close(fig)
(P/'volume_ambiguity_audit_v22.json').write_text(json.dumps({'cases':results,'interpretation':'Reparametrization alone does not imply unique nonlinear gravitation action. Full spatial diffeomorphism not tested.'},indent=2)+'\n')
print(json.dumps(results,indent=2))
