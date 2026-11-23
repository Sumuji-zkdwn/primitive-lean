#!/usr/bin/env python3
"""Independent symbolic audit of stage31 with SymPy (not a Lean proof)."""
import json
from pathlib import Path
import sympy as S

s = S.symbols('s', real=True)
x = S.symbols('x', positive=True)
G = S.Matrix([[s, s/2, s/2], [s/2,1,S.Rational(1,2)], [s/2,S.Rational(1,2),1]])
assert S.simplify(G.det() - s*(3-s)/4) == 0
assert S.simplify(G[:2,:2].det() - s*(4-s)/4) == 0
proj_dot = S.Rational(1,2) - s/4
proj_norm = 1-s/4
costheta = S.factor(proj_dot/proj_norm)
assert S.simplify(costheta-(2-s)/(4-s)) == 0

c=(2-x**2)/(4-x**2)
delta=2*S.pi-3*S.acos(c)
delta_prime=S.diff(delta,x)
flat=S.sqrt(S.Rational(8,3))
assert S.simplify(delta_prime.subs(x,flat) +9*S.sqrt(2)) == 0
assert S.simplify(c.subs(x,flat)+ S.Rational(1,2)) == 0
assert S.simplify(c.subs(x,1)- S.Rational(1,3)) == 0
assert S.simplify(c.subs(x,S.sqrt(S.Rational(11,4)))+S.Rational(3,5)) == 0

k,mu,M,gamma,z,v=S.symbols('k mu M gamma z v', positive=True)
del_fn=S.Function('d')(x)
V=k*(del_fn-z)**2/2+mu*z**2/2
E=M*v**2/2+V
E_prime=S.diff(E,x)*v + S.diff(E,v)*(-S.diff(V,x)/M) + S.diff(E,z)*(-gamma*S.diff(V,z))
assert S.simplify(E_prime + gamma*S.diff(V,z)**2) == 0
slope=-9*S.sqrt(2)
H=S.Matrix([[k*slope**2,-k*slope],[-k*slope,k+mu]])
assert S.simplify(H.det()-162*k*mu)==0
assert S.simplify(H[0,0]-162*k)==0
assert S.simplify(H[1,1]-(k+mu))==0

res={'status':'PASS','gram_determinant':str(S.factor(G.det())),
     'leading_minor':str(S.factor(G[:2,:2].det())),
     'dihedral_cos':str(costheta), 'd_deficit_dx_flat':str(S.simplify(delta_prime.subs(x,flat))),
     'linearized_memory_hessian_det':str(S.factor(H.det())),
     'energy_balance_identity':'dE/dt + gamma*(dV/dz)^2 = 0',
     'scope':'2->3 spatial Pachner geometry and chosen curvature-memory dynamics'}
Path(__file__).with_name('symbolic_audit_v31.json').write_text(json.dumps(res,indent=2)+'\n')
print(json.dumps(res))
