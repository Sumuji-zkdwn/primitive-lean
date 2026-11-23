#!/usr/bin/env python3
"""Linear relaxation spectrum and universal-front-speed obstruction, independent audit."""
from pathlib import Path
import csv
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
P=Path(__file__).resolve().parent
# Old v3 masses vs tuned masses. Vacuum parameters only.
G0=1.0; k_mem=.9; tau=1.2; K=1.0
old_Mq=1.0; old_Mh=2.0
new_Mq=G0+k_mem; new_Mh=K

def modes(wavenumber,M):
    # M*tau*s^3 + M*s^2 + tau*(G0+k)*p^2*s + G0*p^2=0
    return np.roots([M*tau,M,tau*(G0+k_mem)*wavenumber**2,G0*wavenumber**2])

cases=[]
for name,Mq,Mh in [('original',old_Mq,old_Mh),('front_matched',new_Mq,new_Mh)]:
    for p in np.logspace(-2,3,260):
        roots=modes(p,Mq)
        propagating=max(roots,key=lambda s:s.imag)
        relaxing=min(roots,key=lambda s:abs(s.imag))
        cases.append(dict(case=name,p=p,phase_speed=propagating.imag/p,attenuation=-propagating.real,
                          relax_re=relaxing.real,relax_im=relaxing.imag,
                          c_front_q=np.sqrt((G0+k_mem)/Mq),c_front_h=np.sqrt(K/Mh),
                          c_relaxed=np.sqrt(G0/Mq)))
        # All three real parts must be non-positive (q>0 and k_mem>0).
        assert max(s.real for s in roots)<1e-9,(name,p,roots)
with (P/'dispersion.csv').open('w',newline='') as f:
    w=csv.DictWriter(f,fieldnames=list(cases[0]));w.writeheader();w.writerows(cases)

fig,ax=plt.subplots(figsize=(8.8,5.1))
for name,label in [('original','v3: untuned inertia'),('front_matched','v4: front speeds matched')]:
    C=[v for v in cases if v['case']==name]
    ax.semilogx([v['p'] for v in C],[v['phase_speed'] for v in C],label=f'{label}, q phase')
    ax.axhline(C[0]['c_front_h'],ls=':',lw=1,label=f'{label}, h front')
ax.axhline(1,color='black',ls='--',lw=1,alpha=.7,label='target front speed 1')
ax.set(xlabel='Wave number (model units)',ylabel='Phase/front speed',title='Matching the front cone does not remove relaxation dispersion')
ax.grid(alpha=.22);ax.legend(fontsize=8)
fig.tight_layout();fig.savefig(P/'speed_tuning.png',dpi=165);plt.close(fig)

with (P/'speed_summary.txt').open('w') as f:
    for name,Mq,Mh in [('v3',old_Mq,old_Mh),('v4_tuned',new_Mq,new_Mh)]:
        f.write(f'{name}: Mq={Mq:.9g}, Mh={Mh:.9g}, c_q_slow={np.sqrt(G0/Mq):.9g}, c_q_front={np.sqrt((G0+k_mem)/Mq):.9g}, c_h_front={np.sqrt(K/Mh):.9g}\n')
    f.write('For tau,k>0 the relaxation polynomial is Hurwitz for every wavenumber>0.\n')
    f.write('For finite fixed Mq and quartic strain-memory, tangent stiffness = G0+k+3*eta*y^2 is unbounded as |y| increases.\n')
    f.write('Thus no global fixed bound on all background-dependent front speeds is available.\n')
    f.write('The wave-front comparison concerns vacuum principal symbols, not exact Lorentz invariance or equality of all dispersion branches.\n')
print((P/'speed_summary.txt').read_text())
for wavenumber in (.1,1,3,10,100):
    roots=modes(wavenumber,new_Mq)
    print('p',wavenumber,'roots',roots)
