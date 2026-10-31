#!/usr/bin/env python3
"""Exact Fraction tests for the E -> dual -> WFS bridge.

Not a proof of general facts: the Lean proofs live in EnergyWfsFenchel.inc.
"""
from fractions import Fraction as F
from itertools import product


def energy(k, lam, a, c, x, y, u):
    return lam*x**4/F(4) + k*x*x/F(2) + a*y*y/F(2) - c*x*y-u*x


def force(k, lam, c, y, x):
    return k*x+lam*x**3-c*y


def H(k, lam, c, y, x, u):
    return force(k, lam, c, y, x)-u, x


def invH(k, lam, c, y, p, q):
    return q, force(k, lam, c, y, q)-p


def wfs2(x):
    return (x*x-F(1))/2


def test():
    params=[F(-3),F(-1),F(0),F(1),F(2)]
    num=0
    for k,lam,c,y,x,u in product(params,repeat=6):
        a=F(2)
        p,q=H(k,lam,c,y,x,u)
        assert invH(k,lam,c,y,p,q)==(x,u)
        v=energy(k,lam,a,c,x,y,F(0))
        assert energy(k,lam,a,c,x,y,u)==v-u*x
        assert (force(k,lam,c,y,q)-p)*q-energy(k,lam,a,c,q,y,F(0))==u*x-v
        num+=1
    for x in [F(1,4),F(1,2),F(1),F(2),F(3)]:
        assert wfs2(x)-x*x/2 == -F(1,2)
    assert (F(1)-F(1,2)) != (wfs2(F(1))-F(1,2))
    assert energy(F(-1),F(1),F(1,2),F(0),F(0),F(1),F(0)) == F(1,4)
    assert energy(F(-1),F(1),F(1,2),F(0),F(1),F(1),F(0)) == 0
    print(f"PASS: {num:,} exact polynomial E/inverse/work tests; gauge and barrier witnesses verified")


if __name__=="__main__":
    test()
