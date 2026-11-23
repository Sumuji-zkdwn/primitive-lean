#!/usr/bin/env python3
"""Einstein vacuum conditions at second and third orders in m/r.
This *imposes GR field equations*: it does not derive them from substrate rules.
"""
from pathlib import Path
import sympy as s
import json
OUT=Path(__file__).resolve().parent
u_sym,r,m,a2,a3,b2,b3=s.symbols('u r m a2 a3 b2 b3',real=True)
u=m/r
w=-u+a2*u**2+a3*u**3
v=u+b2*u**2+b3*u**3
w1=s.diff(w,r);w2=s.diff(w1,r);v1=s.diff(v,r);v2=s.diff(v1,r)
# Direct 3+1 spherical static Ricci formulas; checked against full 4D Ricci in audit_v6.
Rtt=s.exp(2*w-2*v)*(w2+w1**2+(2/r+v1)*w1)
Rrr=-2*(v2+v1/r)-(w2+w1**2-v1*w1)
Rth=-r*r*v2-3*r*v1-r*r*v1*v1-r*(1+r*v1)*w1
coeff2={n:s.simplify(s.expand(s.series(expr,m,0,3).removeO()).coeff(m,2)) for n,expr in [('Rtt',Rtt),('Rrr',Rrr),('Rtheta',Rth)]}
solve2=s.solve([s.together(ex).as_numer_denom()[0] for ex in coeff2.values()],[a2,b2],dict=True)
assert solve2==[{a2:0,b2:-s.Rational(1,4)}],solve2
coeff3={n:s.simplify(s.expand(s.series(expr.subs(solve2[0]),m,0,4).removeO()).coeff(m,3)) for n,expr in [('Rtt',Rtt),('Rrr',Rrr),('Rtheta',Rth)]}
solve3=s.solve([s.together(ex).as_numer_denom()[0] for ex in coeff3.values()],[a3,b3],dict=True)
assert solve3==[{a3:-s.Rational(1,12),b3:s.Rational(1,12)}],solve3
soul=s.log((1-u_sym/2)/(1+u_sym/2))
solv=2*s.log(1+u_sym/2)
assert s.simplify(s.diff(soul,u_sym,3).subs(u_sym,0)/6+s.Rational(1,12))==0
assert s.simplify(s.diff(solv,u_sym,2).subs(u_sym,0)/2+s.Rational(1,4))==0
assert s.simplify(s.diff(solv,u_sym,3).subs(u_sym,0)/6-s.Rational(1,12))==0
results={'second_order_Ricci_coefficients':{k:str(v) for k,v in coeff2.items()},
         'second_order_solution':{'a2':'0','b2':'-1/4'},
         'third_order_Ricci_coefficients':{k:str(v) for k,v in coeff3.items()},
         'third_order_solution':{'a3':'-1/12','b3':'1/12'},
         'w_correct_through_u3':'-u - u^3/12',
         'v_correct_through_u3':'u - u^2/4 + u^3/12',
         'exact_schwarz_w':'log((1-u/2)/(1+u/2))',
         'exact_schwarz_v':'2 log(1+u/2)',
         'interpretation':'Impose Einstein vacuum Ricci=0 order by order; this does NOT derive Einstein equations.',
         'pass':True}
(OUT/'vacuum_series.json').write_text(json.dumps(results,indent=2)+'\n')
print(json.dumps(results,indent=2))
