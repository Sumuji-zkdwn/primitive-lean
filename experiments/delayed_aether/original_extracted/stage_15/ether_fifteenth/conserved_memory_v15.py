"""Local covariant *reversible* memory pair, a constructive contrast to off-shell K shifts.

This is a 1+1 flat-spacetime matter-only check: NOT Einstein-matter coupled.
"""
from pathlib import Path
import json
import numpy as np
import sympy as sp

T,X,k,w,A,B=sp.symbols('t x k w A B',real=True,positive=True)
kappa=w**2/2
q=A*sp.cos(k*(X-T))+B*sp.cos(w*T)
z=A*sp.cos(k*(X-T))-B*sp.cos(w*T)
V=kappa*(q-z)**2/2
L=(sp.diff(q,T)**2+sp.diff(z,T)**2-sp.diff(q,X)**2-sp.diff(z,X)**2)/2 - V
Eqs=[sp.diff(q,T,2)-sp.diff(q,X,2)+kappa*(q-z),sp.diff(z,T,2)-sp.diff(z,X,2)-kappa*(q-z)]
assert all(sp.trigsimp(sp.expand_trig(e))==0 for e in Eqs)
# mixed stress T^mu{}_nu = (d^mu q)(d_nu q)+(d^mu z)(d_nu z)+delta^mu_nu L
u=[q,z]
derivs=[[sp.diff(u,T),sp.diff(u,X)] for u in u]
Tensor=[[sum((-1 if mu==0 else 1)*ds[mu]*ds[nu] for ds in derivs)+(L if mu==nu else 0) for nu in (0,1)] for mu in (0,1)]
div=[sp.diff(Tensor[0][nu],T)+sp.diff(Tensor[1][nu],X) for nu in (0,1)]
residuals=[sp.simplify(sp.trigsimp(sp.expand_trig(d))) for d in div]
assert residuals==[0,0],residuals
energy=sp.simplify(sp.expand_trig(-Tensor[0][0]))  # energy T^{00}=-T^0{}_0
# choose spatial period 2pi and integer k=2, wave amplitude and internal lag amplitude
chosen={k:sp.Integer(2),w:sp.Rational(13,10),A:sp.Rational(8,100),B:sp.Rational(15,100)}
fn=sp.lambdify((T,X),energy.subs(chosen),modules='numpy')
xs=2*np.pi*np.arange(512)/512
energies=[]
for t in np.linspace(0,9,37):
    y=fn(t,xs)
    energies.append(float(2*np.pi*np.mean(y)))
variation=max(energies)-min(energies)
out=Path(__file__).parent
result={'model':'Two covariant scalar fields with potential V=kappa/2(q-z)^2','energy_momentum_divergence_symbolic':['0','0'],
    'field_equations_symbolic':['0','0'],
    'spatial_total_energy':float(np.mean(energies)),
    'max_variation_total_energy_over_time':variation,
    'mechanism':'coherent relative-mode oscillation; no irreversible relaxation, no topological soliton',
    'limits':'1+1 flat space, matter stress conservation only; no coupled Einstein evolution'}
(out/'conserved_memory_v15.json').write_text(json.dumps(result,ensure_ascii=False,indent=2),encoding='utf-8')
print(json.dumps(result,ensure_ascii=False,indent=2))
