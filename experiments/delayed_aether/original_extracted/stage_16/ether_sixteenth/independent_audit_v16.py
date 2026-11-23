#!/usr/bin/env python3
"""Independent numerical checks for v16. Reads saved data, recomputes residuals,
uses finite differences of the full Hamiltonian, and checks topology via 1D quadrature."""
from pathlib import Path
import json
import numpy as np
from scipy.integrate import simpson
from verify_v16 import RadialModel, evolve
HERE=Path(__file__).resolve().parent

J=json.loads((HERE/'audit_v16.json').read_text())
A=np.genfromtxt(HERE/'radial_dynamics.csv',delimiter=',',names=True)
assert np.all(np.isfinite(A.view(np.float64)))
assert np.max(np.abs(A['H']-A['H'][0]))/A['H'][0] < 2e-10
assert np.max(np.abs(A['H']-A['T_q']-A['T_chi']-A['V'])) < 1e-9
assert A['max_A'].max() > 1.10 and np.min(A['max_A'])>=1.0-1e-12
assert np.max(np.abs(A['control_max_A']-1))<1e-14
# Independent recomputation of gravity constraint using ordinary radial central differences.
B=np.genfromtxt(HERE/'einstein_constraint_profile.csv',delimiter=',',names=True)
r=B['r']; dr=r[1]-r[0]
res={}
for mode in ['lagged','aligned']:
    psi=B['psi_'+mode]; S=B['poisson_source_2piG_psi5rho_'+mode]; rho=B['rho_'+mode]
    lap=(psi[2:]-2*psi[1:-1]+psi[:-2])/dr**2 + 2/r[1:-1]*(psi[2:]-psi[:-2])/(2*dr)
    core=(r[1:-1]>.45)&(r[1:-1]<r[-1]-1)
    rms=float(np.sqrt(np.mean((lap+S[1:-1])[core]**2)))
    rel=rms/float(np.sqrt(np.mean(S[1:-1][core]**2)))
    assert rel<9e-5,(mode,rel)
    # 2nd-order one-sided derivative at R compared with Robin exterior matching condition.
    Douter=(3*psi[-1]-4*psi[-2]+psi[-3])/(2*dr)
    robin=float(abs(Douter+(psi[-1]-1)/r[-1]))
    assert robin<1e-6,(mode,robin)
    res[mode]={'independent_radial_laplacian_relative_rms':rel, 'independent_Robin_residual':robin,
               'psi_center':float(psi[0]),'rho_peak':float(max(rho))}
# Hamiltonian canonical ODE rederived by a finite-difference directional derivative test.
m=RadialModel(n=48)
y=m.initial();rhs=m.rhs(0,y)
k=m.k; grad_analytic=np.r_[-rhs[2*k:3*k],-rhs[3*k:4*k],rhs[:k],rhs[k:2*k]]
rng=np.random.default_rng(721)
fd_rel=[]
for _ in range(12):
    d=rng.normal(size=y.size);d/=np.linalg.norm(d)
    eps=4e-6
    estimated=(m.hamiltonian(y+eps*d)[0]-m.hamiltonian(y-eps*d)[0])/(2*eps)
    expected=np.dot(grad_analytic,d)
    fd_rel.append(abs(estimated-expected)/max(1,abs(estimated),abs(expected)))
assert max(fd_rel)<3e-8,max(fd_rel)
# Finite radial quadrature for degree B=-2/pi integral sin^2 f df on a hedgehog.
_,sol,_,_=evolve(n=96,T=.25)
Hdeg=[]
for z in [sol.y[:,0],sol.y[:,-1]]:
    f,_,_,_=RadialModel(n=96).split(z)
    ff=np.r_[np.pi,f,0]
    dx=12/96
    fp=np.gradient(ff,dx,edge_order=2)
    Bnum=-2/np.pi*simpson(np.sin(ff)**2*fp,dx=dx)
    Hdeg.append(float(Bnum))
    assert abs(Bnum-1)<0.004,Bnum
assert J['symbolic']['1+1_energy_identity'] and J['symbolic']['1+1_momentum_identity']
ratio=J['grav_initial_constraint_lagged_memory'][-1]['mass_from_source']/J['grav_initial_constraint_aligned_memory'][-1]['mass_from_source']
res['misc']={'max_full_hamiltonian_directional_gradient_error':max(fd_rel),
             'degree_hedgehog_radial_quadrature_initial_final':Hdeg,
             'mass_ratio_lagged_over_aligned':ratio,
             'mass_increase_percent_due_to_prescribed_memory_lag':100*(ratio-1)}
(HERE/'independent_audit_v16.json').write_text(json.dumps(res,ensure_ascii=False,indent=2))
print(json.dumps(res,ensure_ascii=False,indent=2))
