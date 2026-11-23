#!/usr/bin/env python3
"""Analytic compact-support 3D radial scalar wave test with finite propagation speed.

For free massless h_tt=c²(h_rr+2h_r/r), let u=r h.
Then u_tt=c² u_rr and h(r,t)=(u0(r-ct)+u0(r+ct))/(2r) when hdot0=0,
where u0 is extended oddly to negative r.
"""
import numpy as np, math,csv
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
P=Path(__file__).resolve().parent
c=1/math.sqrt(2) # K/m_h=1/2 in dynamical model
center=1.4;halfwidth=.3

def bump(s):
    v=(np.abs(s)-center)/halfwidth
    ans=np.zeros_like(v,dtype=float)
    z=np.abs(v)<1
    ans[z]=(1-v[z]**2)**3
    return np.sign(s)*ans

def h(r,t):
    r=np.asarray(r)
    return (bump(r-c*t)+bump(r+c*t))/(2*r)

if __name__=='__main__':
    t=np.linspace(0,11,5501)
    rs=[3.5,5.5,7.5]
    rows=[]
    fig,ax=plt.subplots(figsize=(8.8,5.2))
    for r in rs:
        signal=h(np.full_like(t,r),t)
        predicted=(r-(center+halfwidth))/c
        sel=np.where(np.abs(signal)>1e-9)[0]
        observed=t[sel[0]] if len(sel) else float('nan')
        rows.append(dict(r=r,c=c,predicted_front=predicted,
                         observed_threshold_first=observed,error=observed-predicted,
                         maximum_signal=float(np.max(np.abs(signal)))))
        ax.plot(t,signal,label=f'r={r:g}; predicted front={predicted:.2f}')
        ax.axvline(predicted,ls=':',lw=1,alpha=.4)
    ax.set(xlabel='Time (model units)',ylabel='Scalar disturbance h(r,t)',
           title='Finite-speed propagation in the vacuum radial scalar sector')
    ax.legend(fontsize=9);ax.grid(alpha=.2);fig.tight_layout();fig.savefig(P/'causal_wavefront.png',dpi=160);plt.close(fig)
    with (P/'causal_wavefront_audit.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
    for x in rows:
        print(x)
        assert 0<=x['error']<.03
    print('ANALYTIC CAUSAL WAVEFRONT CHECK PASSED')
