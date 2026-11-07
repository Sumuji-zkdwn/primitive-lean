#!/usr/bin/env python3
"""Independent exact Fraction audit for the fourth-probe mean-constraint sidecar.
Checking each bounded-degree polynomial identity at 20 distinct rational
points is conclusive for the identities of degree <=17 used here.
"""
from fractions import Fraction as F

P = tuple(map(F,(
    '155406813431861/3135446314560000',
    '307250787839/10451487715200',
    '5341857272874251/15677231572800000',
    '379061002125331/653217982200000'
)))
Q = tuple(map(F,(
    '9757217468803/196456536000000',
    '21675828291197/196456536000000',
    '4/5', '1/25'
)))
def response(s,p):
    return sum((c*s**j for j,c in enumerate(p)), F(0))
def mean(p):
    return sum(j*c for j,c in enumerate(p))
assert sum(P)==sum(Q)==1 and min(P+Q)>0
assert P!=Q and mean(P)!=mean(Q)
for t in (F(1,4),F(1,3),F(1,2),F(4,5)):
    assert response(t**3,P) == response(t**4,Q)
print("PASS exact mass-only positive four-probe witness")
print("mean_P",mean(P),float(mean(P)), "mean_Q",mean(Q),float(mean(Q)))

def A(t): return 5*t**5-4*t**4-4*t**3+16*t**2-2*t-2
def B(t): return -t**2*(t**7+t**6+t**5-7*t**4-7*t**3+11*t**2-9*t-9)
def C(t): return 9*t**5*(t*t+t+1)*(t**6-3*t**3+3)
def E(t):
    return 40*t**11+79*t**10+76*t**9+110*t**8+260*t**7+605*t**6+672*t**5+474*t**4+24*t**3-138*t*t-120*t-30
def PB(t):
    return 20*t**10+35*t**9+20*t**8+50*t**7+200*t**6+455*t**5+380*t**4+80*t**3+200*t*t+144*t+36
def dA(t):return 25*t**4-16*t**3-12*t*t+32*t-2
def dB(t):return -9*t**8-8*t**7-7*t**6+42*t**5+35*t**4-44*t**3+27*t*t+18*t
def dC(t):return 117*t**12+108*t**11+99*t**10-270*t**9-243*t**8-216*t**7+189*t**6+162*t**5+135*t**4

Ahi=(13,117,222,174,63,9)
Bc=(9,72,232,402,420,276,108,18)
Elo=(61440,798720,4678656,16296960,37454592,59485440,
      66358112,51682976,27279440,9139648,1691794,120250)
# Each difference has polynomial degree <=17. 20 exact rational points
# determine a polynomial of degree at most 19 uniquely.
for i in range(20):
    t=F(i,20)
    assert A(t)==sum(c*(2*t-1)**k*(1-t)**(5-k) for k,c in enumerate(Ahi))
    assert B(t)==sum(c*t**(k+2)*(1-t)**(7-k) for k,c in enumerate(Bc))
    assert -2048*E(t)==sum(c*(2*t)**k*(1-2*t)**(11-k) for k,c in enumerate(Elo))
    assert A(t)*dB(t)-dA(t)*B(t)==-t*(t-1)**2*PB(t)
    assert A(t)*dC(t)-dA(t)*C(t)==9*t**4*(t-1)**2*E(t)
print("PASS exact polynomial identities (20 distinct points, degree <=17)")

# These are not numerical evidence for *all* real t. The Lean coefficients
# certify the polynomial identities and the positivity bases analytically.
assert all(c>0 for c in Ahi+Bc+Elo)
for i in range(1,100):
    t=F(i,100)
    assert B(t)>0 and C(t)>0
    if t>=F(1,2): assert A(t)>0
    if t<F(1,2): assert E(t)<0
print("PASS rational-grid sign checks; global signs follow from positive bases")
