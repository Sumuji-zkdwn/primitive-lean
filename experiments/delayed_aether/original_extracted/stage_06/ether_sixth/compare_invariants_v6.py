#!/usr/bin/env python3
"""Invariantly matched comparisons: impact parameter and areal turning radii."""
import csv,json
from pathlib import Path
import numpy as np
from scipy.optimize import brentq
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from verify_v6 import metric,optical_bending,timelike_precession
OUT=Path(__file__).resolve().parent

def areal_r(r,model):
    _A,B=metric(r,model)
    return r*np.sqrt(B)

def invert_areal(R,model):
    minr=1 if model=='exp' else .5
    return brentq(lambda r:areal_r(r,model)-R,minr*(1+1e-9),R,xtol=1e-13)

def photon_sphere_r(model):
    return 2. if model=='exp' else (2+np.sqrt(3))/2

def impact_b(r,model):
    A,B=metric(r,model)
    return r*np.sqrt(B/A)

def invert_impact(b,model):
    photon_r=photon_sphere_r(model)
    return brentq(lambda r:impact_b(r,model)-b,photon_r*(1+1e-9),b,xtol=1e-13)

def write(rows,name):
    with (OUT/name).open('w',newline='') as fh:
        w=csv.DictWriter(fh,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)

def main():
    bends=[]
    for b in [5.5,5.75,6,7,8,10,12,15,20,30,50,100,200,500,1000]:
        ep=invert_impact(b,'exp'); sp=invert_impact(b,'schwarzschild')
        alpha_e,_,_ =optical_bending(ep,'exp');alpha_s,_,_=optical_bending(sp,'schwarzschild')
        bends.append({'impact_b_over_m':b,'r0_exp':ep,'r0_sch':sp,'deflection_exp':alpha_e,
                      'deflection_sch':alpha_s,'deflection_ratio':alpha_e/alpha_s,'weak_4_over_b':4/b})
    write(bends,'lensing_same_impact.csv')
    orbits=[]
    for Rp,Ra in [(7,9),(10,14),(15,22),(20,30),(50,70),(100,150)]:
        ep,ea=[invert_areal(R,'exp') for R in (Rp,Ra)]
        sp,sa=[invert_areal(R,'schwarzschild') for R in (Rp,Ra)]
        pe,*_=timelike_precession(ep,ea,'exp');ps,*_=timelike_precession(sp,sa,'schwarzschild')
        orbits.append({'areal_Rp_over_m':Rp,'areal_Ra_over_m':Ra,
                       'isotropic_rp_exp':ep,'isotropic_ra_exp':ea,
                       'isotropic_rp_sch':sp,'isotropic_ra_sch':sa,
                       'advance_exp':pe,'advance_sch':ps,'ratio_exp_over_sch':pe/ps})
    write(orbits,'precession_same_areal_radii.csv')
    clocks=[]
    for R in [3,4,5,10,20,50,100,1000]:
        ep=invert_areal(R,'exp');sp=invert_areal(R,'schwarzschild')
        Ae,_=metric(ep,'exp');As,_=metric(sp,'schwarzschild')
        clocks.append({'areal_R_over_m':R,'isotropic_r_exp':ep,'isotropic_r_sch':sp,
                       'redshift_exp':1/np.sqrt(Ae)-1,'redshift_sch':1/np.sqrt(As)-1})
    write(clocks,'redshift_same_areal_radius.csv')
    fig,ax=plt.subplots(figsize=(8.4,4.6))
    x=np.array([r['impact_b_over_m'] for r in bends])
    ax.loglog(x,[r['deflection_exp'] for r in bends],'o-',label='Exponential toy')
    ax.loglog(x,[r['deflection_sch'] for r in bends],'s--',label='Schwarzschild GR')
    ax.loglog(x,4/x,':',label='Weak field 4m/b')
    ax.grid(alpha=.25);ax.legend();ax.set(xlabel='Asymptotic impact parameter b/m',ylabel='Deflection (rad)',title='Invariant comparison at the same impact parameter')
    fig.tight_layout();fig.savefig(OUT/'lensing_same_impact.png',dpi=155);plt.close(fig)
    fig,ax=plt.subplots(figsize=(8.4,4.6))
    x=np.array([r['areal_Rp_over_m'] for r in orbits]);
    ax.plot(x,[r['advance_exp'] for r in orbits],'o-',label='Exponential toy')
    ax.plot(x,[r['advance_sch'] for r in orbits],'s--',label='Schwarzschild GR')
    ax.grid(alpha=.25);ax.legend();ax.set(xlabel='Pericenter circumferential radius Rp/m',ylabel='Precession per radial period (rad)',title='Same invariant peri- and apo-center circumferences')
    fig.tight_layout();fig.savefig(OUT/'precession_same_areal.png',dpi=155);plt.close(fig)
    selected={'b10':next(q for q in bends if q['impact_b_over_m']==10),
              'b100':next(q for q in bends if q['impact_b_over_m']==100),
              'areal_pericenter10_14':next(q for q in orbits if q['areal_Rp_over_m']==10),
              'redshift_areal10':next(q for q in clocks if q['areal_R_over_m']==10),
              'photon_b_critical_exp':impact_b(2,'exp'),
              'photon_b_critical_sch':impact_b((2+np.sqrt(3))/2,'schwarzschild')}
    assert selected['photon_b_critical_exp']>selected['photon_b_critical_sch']
    (OUT/'invariant_comparison.json').write_text(json.dumps(selected,indent=2)+'\n')
    print(json.dumps(selected,indent=2))
if __name__=='__main__': main()
