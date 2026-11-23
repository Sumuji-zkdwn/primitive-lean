#!/usr/bin/env python3
"""Independent amplitude-scaling test of nonlinear cross -> plus coupling.
Only a fixed-background two-polarization Hamiltonian; does not solve GR constraints.
"""
import json,csv
from pathlib import Path
import numpy as np
from scipy.integrate import solve_ivp
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
P=Path(__file__).resolve().parent

def solve(amp, n=256, tend=1.4,inhomogeneous=True):
    dx=2*np.pi/n; x=np.arange(n)*dx
    F=2+.35*np.tanh(.4*np.cos(x-.6)+.18*np.sin(2*x)) if inhomogeneous else np.full(n,2.)
    D=lambda v:(np.roll(v,-1)-np.roll(v,1))/(2*dx)
    w0=amp*np.exp(-(np.angle(np.exp(1j*(x-2.3)))/.46)**2)
    z=np.zeros(n)
    Y0=np.concatenate((z,z*0+w0,z,-.5*F*D(w0)))
    def h(Y):
        b,w,pb,pw=np.split(Y,4)
        return dx*np.sum(pb*pb/(4*F)+np.exp(-4*b)*pw*pw/F+F*D(b)**2+.25*F*np.exp(4*b)*D(w)**2)
    def rhs(t,Y):
        b,w,pb,pw=np.split(Y,4)
        ex=np.exp(4*b)
        db=pb/(2*F)
        dw=2*pw/(F*ex)
        dpb=2*D(F*D(b))+4*pw*pw/(F*ex)-F*ex*D(w)**2
        dpw=.5*D(F*ex*D(w))
        return np.concatenate((db,dw,dpb,dpw))
    sol=solve_ivp(rhs,(0,tend),Y0,method='DOP853',rtol=2e-10,atol=2e-11,max_step=.4*dx,t_eval=[tend])
    assert sol.success
    b,w,pb,pw=np.split(sol.y[:,-1],4)
    return {'amplitude':amp,'grid':n,'fixed_memory_profile':inhomogeneous,'max_generated_plus':float(np.max(np.abs(b))), 'energy_relative_error':float((h(sol.y[:,-1])-h(Y0))/h(Y0)), 'max_cross':float(np.max(np.abs(w)))}

if __name__=='__main__':
    rows=[]
    for amp in [0.10,0.15,0.20,0.25,0.30]:
        for n in [128,256]:rows.append(solve(amp,n))
    extra=solve(0.25,256,inhomogeneous=False)
    data=[r for r in rows if r['grid']==256]
    power=float(np.polyfit(np.log([r['amplitude'] for r in data]),np.log([r['max_generated_plus'] for r in data]),1)[0])
    assert 1.85<power<2.15,power
    assert max(abs(r['energy_relative_error']) for r in rows)<1e-8
    for r1,r2 in zip(rows[::2],rows[1::2]):
        assert abs(r1['max_generated_plus']-r2['max_generated_plus'])/r2['max_generated_plus'] < .025
    with open(P/'polarization_scaling_v28.csv','w',newline='') as out:
        wr=csv.DictWriter(out,list(rows[0]));wr.writeheader();wr.writerows(rows)
    fig,ax=plt.subplots(figsize=(7.7,4.8))
    for n in (128,256):
        r=[x for x in rows if x['grid']==n]
        ax.loglog([v['amplitude'] for v in r],[v['max_generated_plus'] for v in r],'o-',label=f'{n} grid cells')
    x=np.array([.1,.3]);c=data[-1]['max_generated_plus']/.3**2
    ax.loglog(x,c*x*x,'--',c='gray',label='Quadratic reference')
    ax.set(xlabel='Initial cross-polarization amplitude',ylabel='Induced plus-polarization amplitude',title='Nonlinear polarization transfer in the fixed-background sector')
    ax.grid(alpha=.2,which='both');ax.legend();fig.tight_layout();fig.savefig(P/'nonlinear_polarization_scaling_v28.png',dpi=170);plt.close(fig)
    result={'quadratic_scaling_exponent':power,'all_rows':rows,'homogeneous_memory_control':extra,'relative_spatial_grid_difference_at_amp_0p25':abs(rows[6]['max_generated_plus']-rows[7]['max_generated_plus'])/rows[7]['max_generated_plus']}
    (P/'polarization_amplitude_audit_v28.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    print('quadratic exponent:',power)
    print('0.25 amp fine:',rows[7])
    print('homogeneous memory control',extra)
    print('cross-grid relative difference',result['relative_spatial_grid_difference_at_amp_0p25'])
    print('AUDIT OK')
