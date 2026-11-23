#!/usr/bin/env python3
"""Independent scaled Skyrme-energy test in a fixed finite box."""
import csv, json
from pathlib import Path
import numpy as np
from scipy.integrate import quad
from verify_v11 import hedgehog

ROOT=Path(__file__).resolve().parent


def energy_in_cube(n, radius):
    h=2./n
    g=np.linspace(-1.,1.,n+1)
    coords=np.stack(np.meshgrid(g,g,g,indexing='ij'),-1).reshape(-1,3)
    q=hedgehog(coords,center=(0.,0.,0.),radius=radius).reshape(n+1,n+1,n+1,4)
    dq=np.stack(np.gradient(q,h,axis=(0,1,2),edge_order=2),axis=0)
    d2=np.sum(dq*dq,axis=-1)
    E2=.5*np.sum(d2,axis=0)
    E4=np.zeros_like(E2)
    for i,j in ((0,1),(0,2),(1,2)):
        E4+=.5*(d2[i]*d2[j]-np.sum(dq[i]*dq[j],axis=-1)**2)
    return float(E2.sum()*h**3),float(E4.sum()*h**3)


def main():
    # Exact continuum scaling constants for f(r)=pi*(1-r), 0<=r<=1,
    # using E2=1/2|grad q|^2 and E4=1/2 sum_{i<j}|di q wedge dj q|^2.
    A=2*np.pi*(np.pi**2/3+1)
    B=2*np.pi*quad(lambda r: 2*np.pi**2*np.sin(np.pi*r)**2 +
                   (np.sin(np.pi*r)**4/r**2 if r else 0),0,1,epsabs=1e-12)[0]
    # The 2*pi prefactor includes the 1/2 wedge convention.
    target=.48
    k4=A*target**2/B
    radii=np.arange(.24,.761,.04)
    rows=[]
    for n in (20,40,60,80,100,120):
        for radius in radii:
            E2,E4=energy_in_cube(n,float(radius))
            rows.append(dict(n=n,radius=round(float(radius),3),E2=E2,E4=E4,
                             E=E2+k4*E4,exact_scaling=A*radius+k4*B/radius))
    with (ROOT/'energy_scaling.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
    min_by_n={str(n):min((r for r in rows if r['n']==n),key=lambda r:r['E']) for n in (20,40,60,80,100,120)}
    audit={'A':A,'B':B,'k4':k4,'target_minimum_radius':target,'predicted_minimum_radius':(k4*B/A)**.5,
           'grid_minima':min_by_n,'radius_domain':[float(radii.min()),float(radii.max())],
           'interpretation':'stable only in radial radius family and only with added Skyrme quartic term'}
    (ROOT/'energy_audit.json').write_text(json.dumps(audit,indent=2),encoding='utf-8')
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    fig,ax=plt.subplots(figsize=(7.5,4.7))
    x=np.linspace(.24,.76,250)
    ax.plot(x,A*x+k4*B/x,label='continuum scaling (analytic)')
    for n in (20,40,60,80,100,120):
        rr=[r for r in rows if r['n']==n]
        ax.plot([r['radius'] for r in rr],[r['E'] for r in rr],'.-',label=f'{n} cells / axis')
    ax.axvline(target,color='gray',ls=':',label='continuum minimum')
    ax.set(xlabel='lump radius (model units)',ylabel='E2 + c4 E4',title='Finite-size stationary radius requires quartic rigidity')
    ax.legend(fontsize=8);ax.grid(alpha=.25);fig.tight_layout()
    fig.savefig(ROOT/'energy_vs_radius.png',dpi=160);plt.close(fig)
    print(json.dumps(audit,indent=2))

if __name__=='__main__':main()
