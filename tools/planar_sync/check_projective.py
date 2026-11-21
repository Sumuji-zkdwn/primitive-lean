#!/usr/bin/env python3
"""Compare the SAME first-order locking dynamics in phase and projective coordinates.

The physical assumptions of the first-order Adler model are not inferred here.
The exact change of coordinates and the chart at infinity are checked.
Requires NumPy and SciPy; exact identities use standard-library Fraction.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
from datetime import datetime, timezone
import argparse
import json
import numpy as np
from scipy.integrate import solve_ivp
from scipy.linalg import expm


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, default=Path(__file__).resolve().parents[2] / "verification" / "planar-sync")
    args = parser.parse_args()
    cases = 0
    for delta, k, q in product(map(F,[-2,-1,0,1,2]),map(F,[1,2]),
                                [F(-3),F(-1),F(0),F(1,2),F(1),F(3)]):
        c = (1-q*q)/(1+q*q)
        s = 2*q/(1+q*q)
        dq = delta*(1+q*q)/2-k*q
        dc = -4*q*dq/(1+q*q)**2
        ds = 2*(1-q*q)*dq/(1+q*q)**2
        assert c*c+s*s == 1
        assert dc == -delta*s+k*s*s
        assert ds == delta*c-k*c*s
        if q:
            p = 1/q
            assert -dq/(q*q) == k*p-delta*(1+p*p)/2
        cases += 1
    k = F(1)
    delta = F(3,5)
    stable, unstable = F(1,3), F(3)
    f = lambda q: delta*(1+q*q)/2-k*q
    assert f(stable) == f(unstable) == 0
    assert delta*stable-k == -F(4,5)
    assert delta*unstable-k == F(4,5)
    assert F(1)*(1+F(1)**2)/2-F(1) == 0

    # Homogeneous coordinate q=v/u. It avoids division at the antipodal point.
    # [u,v]' = [[K/2, -Delta/2],[Delta/2, -K/2]] [u,v].
    times = np.linspace(0,8,161)
    runs = []
    for delta, initial in product([0.0,.6,1.0,1.4,-.6,-1.0,-1.4],
                                  [-2.8,-.5,.4,2.8,np.pi]):
        k = 1.0
        phase = solve_ivp(lambda t,x: [delta-k*np.sin(x[0])],
                          (0,8),[initial],t_eval=times,method='DOP853',
                          rtol=2e-12,atol=2e-13)
        assert phase.success
        M = np.array([[k/2,-delta/2],[delta/2,-k/2]])
        uv0 = np.array([np.cos(initial/2),np.sin(initial/2)])
        if initial == np.pi:
            uv0 = np.array([0.0,1.0])
        uv = np.array([expm(t*M)@uv0 for t in times])
        denom = np.sum(uv*uv,axis=1)
        c = (uv[:,0]**2-uv[:,1]**2)/denom
        s = 2*uv[:,0]*uv[:,1]/denom
        error = max(float(np.max(np.abs(c-np.cos(phase.y[0])))),
                    float(np.max(np.abs(s-np.sin(phase.y[0])))))
        assert error < 1e-8, (delta,initial,error)
        runs.append({'Delta':delta,'K':k,'initial_phase':initial,
                     'maximum_observable_absolute_error':error,
                     'near_chart_boundary_initially': bool(initial==np.pi)})
    max_error = max(r['maximum_observable_absolute_error'] for r in runs)
    q0 = 3.0
    q = q0*np.exp(-times)
    delta0_phase = 2*np.arctan(q)
    assert np.all(np.isfinite(delta0_phase))
    report = {
        'title':'Exact projective rewrite of first-order phase locking',
        'generated_at_utc':datetime.now(timezone.utc).isoformat(),
        'overall_status':'passed',
        'exact_rational_identity_cases':cases,
        'phase_vs_homogeneous_runs':len(runs),
        'time_samples_per_run':len(times),
        'max_observable_absolute_error':max_error,
        'equations':{
            'phase':'phi_dot = Delta - K*sin(phi)',
            'projective':'q_dot = Delta/2*(1+q*q)-K*q',
            'reciprocal_chart':'p_dot = K*p-Delta/2*(1+p*p)',
            'zero_detuning':'q(t)=q(0)*exp(-K*t)',
            'homogeneous_matrix':[['K/2','-Delta/2'],['Delta/2','-K/2']],
            'observables':['c=(u*u-v*v)/(u*u+v*v)','s=2*u*v/(u*u+v*v)'],
        },
        'exact_lock_example':{'K':'1','Delta':'3/5','stable_q':'1/3',
                              'unstable_q':'3','stable_derivative':'-4/5',
                              'unstable_derivative':'4/5'},
        'runs':runs,
        'limitations':[
            'The first-order phase model is assumed, not derived from actual tidal or magnetic torques.',
            'q is a signed projective state coordinate, not automatically a directly measured width.',
            'q=infinity is a chart point, not an infinite physical displacement.',
            'At Delta=0, the antipodal point q=infinity remains an unstable equilibrium.',
            'For abs(Delta)=K, the double equilibrium is semistable and decay need not be exponential.',
            'This uses a standard half-angle/projective substitution, not a novel law of nature.',
            'The ordinary phase model already has one degree of freedom; the gain is simpler equations.',
            'Agreement of two numerical representations supplements the exact algebraic identity.'
        ]
    }
    args.output_dir.mkdir(exist_ok=True,parents=True)
    out=args.output_dir/'projective-lock-results.json'
    out.write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ['runs','equations','limitations']},
                     ensure_ascii=False,indent=2))
    print(out)


if __name__ == '__main__':
    main()
