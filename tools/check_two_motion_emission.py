#!/usr/bin/env python3
"""Independent exact rational regressions; NOT proofs of the continuum theorems.

Every coordinate of the chosen energy has degree at most two when the others
are fixed, so its coordinate central difference with step 1 is exactly its
partial derivative. This checks backreaction without reusing a gradient formula.
Only Python's standard library is required.
"""
from collections import Counter
from fractions import Fraction as Q
from itertools import product
import json


def energy(state, kappa, g, w1, w2):
    x1, v1, x2, v2, y = state
    return (v1*v1 + w1*w1*x1*x1 + v2*v2 + w2*w2*x2*x2)/2 + kappa*(y-g*x1*x2)**2/2


def partial(state, i, kappa, g, w1, w2):
    plus, minus = list(state), list(state)
    plus[i] += 1
    minus[i] -= 1
    return (energy(plus, kappa, g, w1, w2)-energy(minus, kappa, g, w1, w2))/2


def flux(c, qt, qs):
    return -c*c*qt*qs


def q(t):
    return t*t-2*t**3+t**4


def v(t):
    return 2*t-6*t*t+4*t**3


def a(t):
    return 2-12*t+12*t*t


def main():
    checks = Counter()
    states = list(product((Q(-1),Q(0),Q(1)), repeat=5))
    params = [tuple(map(Q,p)) for p in [
        (1,1,1,1,1),(2,-1,1,2,3),(3,0,2,1,2),
        (Q(1,3),Q(2,5),Q(7,10),1,Q(3,2)),(0,2,1,1,1)]]
    for kappa,g,w1,w2,c in params:
        for state in states:
            x1,v1,x2,v2,y=state
            F=kappa*(g*x1*x2-y)
            grad=[partial(state,i,kappa,g,w1,w2) for i in range(5)]
            assert grad == [w1*w1*x1+g*x2*F,v1,w2*w2*x2+g*x1*F,v2,-F]
            checks['coordinate_gradients']+=5
            field=[v1,-w1*w1*x1-g*x2*F,v2,-w2*w2*x2-g*x1*F,F/(2*c)]
            rate=sum((du*dx for du,dx in zip(grad,field)),Q(0))
            P=F*F/(2*c)
            assert rate+P==0 and P>=0 and energy(state,kappa,g,w1,w2)>=0
            checks['energy_rate_and_nonnegativity']+=1
            qt=F/(2*c)
            assert flux(c,qt,-qt/c)-flux(c,qt,qt/c)==P
            assert -c*c*(-qt/c-qt/c)==F
            checks['outgoing_flux_and_jump']+=1
    for k,lam,x0,h in product(map(Q,range(-2,3)),repeat=4):
        def U(x): return k*x*x/2+lam*x**4/4-(k*x0+lam*x0**3)*x
        assert U(x0+h)-U(x0)==(k+3*lam*x0*x0)*h*h/2+lam*x0*h**3+lam*h**4/4
        checks['shifted_quartic']+=1
    qcoef=[Q(0),Q(0),Q(1),Q(-2),Q(1)]
    vcoef=[(i+1)*qcoef[i+1] for i in range(len(qcoef)-1)]
    acoef=[(i+1)*vcoef[i+1] for i in range(len(vcoef)-1)]
    for t in [Q(i,10) for i in range(11)]:
        assert sum((z*t**i for i,z in enumerate(vcoef)),Q(0))==v(t)
        assert sum((z*t**i for i,z in enumerate(acoef)),Q(0))==a(t)
        checks['closed_mode_derivatives']+=2
    assert q(0)==v(0)==q(1)==v(1)==0
    assert q(Q(1,2))==Q(1,16) and a(0)+q(0)==2
    checks['closed_mode_endpoints_and_excursion']+=1
    print(json.dumps({'status':'all checks passed','arithmetic':'fractions.Fraction',
        'states':len(states),'parameter_sets':len(params),'checks':dict(checks),
        'scope':'Finite algebraic regressions, not ODE existence, interval integral or PDE proofs.'},indent=2))


if __name__=='__main__':
    main()
