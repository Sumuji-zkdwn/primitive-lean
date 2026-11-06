"""Finite numerical probe of a reinterpretation loop based on initial primitive-lean statements.

NOT Lean verification. The derivative identities in the associated report follow algebraically
from Gradient.inc, RegularBand.inc and ExponentialWeight.lean. This script checks examples.
"""
import json
import math
import numpy as np
from scipy.integrate import solve_ivp

LAMBDA, R, U = 1., 1., 0.
GAMMA, TARGET, BETA = 1., 0.5, 2.

def E(x,y):
    return LAMBDA*x**4/4 + R*x*x/2 - U*x + (y-math.sqrt(2)*x)**2/2

def g(x,y):
    return np.array([LAMBDA*x**3+(R+2)*x-math.sqrt(2)*y-U,y-math.sqrt(2)*x])

def ode(b):
    def f(t,z):
        x,y = z; gg=g(x,y); e=E(x,y)-TARGET
        return -GAMMA*e*gg + b*np.array([-gg[1],gg[0]])
    return f

def observables(z):
    es=np.array([E(x,y)-TARGET for x,y in z]);
    p=1/(1+np.exp(BETA*es))
    H= -(p*np.log(p)+(1-p)*np.log1p(-p))
    gs=np.array([np.sum(g(x,y)**2) for x,y in z])
    Hp=BETA*BETA*GAMMA*es*es*gs*p*(1-p)
    return es,p,H,Hp

results={}
for label,initial,b in [
        ('below_target',(0.,0.5),0.),
        ('above_target',(0.,1.5),0.),
        ('shell_stationary',(0.,1.),0.),
        ('shell_circulating',(0.,1.),1.),
    ]:
    T=20.; grid=np.linspace(0,T,1001)
    sol=solve_ivp(ode(b),(0,T),initial,t_eval=grid,method='DOP853',rtol=1e-12,atol=1e-13)
    if not sol.success: raise RuntimeError(sol.message)
    z=sol.y.T; es,p,H,Hp=observables(z)
    s={
        'initial':initial,'b':b,'e_initial':float(es[0]),'e_final':float(es[-1]),
        'E_initial':float(es[0]+TARGET),'E_final':float(es[-1]+TARGET),
        'p_initial':float(p[0]),'p_final':float(p[-1]),
        'H_initial':float(H[0]),'H_final':float(H[-1]),
        'H_monotonic_min_increment':float(np.diff(H).min()),
        'max_e_deviation_from_initial':float(np.max(np.abs(es-es[0]))),
        'distance_final_from_initial':float(np.linalg.norm(z[-1]-z[0])),
        'total_travel_distance':float(np.linalg.norm(np.diff(z,axis=0),axis=1).sum()),
        'max_abs_energy_derivative_along_shell': float(np.max(np.abs(-GAMMA*es*np.array([sum(g(*v)**2) for v in z])))),
        'H_derivative_formula_min':float(Hp.min()),
        'trajectory_t_end': z[-1].tolist()
    }
    results[label]=s

# A deliberately false inference one can get from treating exp(-beta(E1+E2)) as independent probabilities.
def normalized(e): return 1/(1+math.exp(BETA*e))
false_inference={'e1':1.,'e2':1.,'p_sum':normalized(2.),'p1_times_p2':normalized(1.)**2,'discrepancy':normalized(2.)-normalized(1.)**2}

report={'source':'primitive-lean initial 465 theorem family; numerical derived observable probe',
       'parameters':{'lambda':LAMBDA,'r':R,'u':U,'gamma':GAMMA,'target':TARGET,'beta':BETA},
       'identities':{'energy_gap_derivative':'e_prime=-gamma*e*|grad(E)|^2',
                     'normalized_observer':'p=1/(1+exp(beta*e))',
                     'p_derivative':'p_prime=beta*gamma*e*|grad(E)|^2*p*(1-p)',
                     'binary_entropy_derivative':'H_prime=beta^2*gamma*e^2*|grad(E)|^2*p*(1-p)>=0',
                     'tangential_motion':'(x_prime,y_prime)=-gamma*e*grad(E)+b*J*grad(E) with J(gx,gy)=(-gy,gx)'},
       'trajectories':results,'invalid_independence_example':false_inference,
       'scope':'Algebraic derivation plus independent numerical integration only; Lean proof of newly derived H_prime not run.'}
with open('/mnt/data/primitive_465_roundtrip_results.json','w',encoding='utf8') as f: json.dump(report,f,indent=2,ensure_ascii=False)
print(json.dumps(report,indent=2,ensure_ascii=False))
