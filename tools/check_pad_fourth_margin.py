#!/usr/bin/env python3
"""Exact stdlib Fraction audit: uniform two-probe PAD discrimination margin.
Assumes mass=1, mean=3/2 and calibrated exponents 1 vs 4/3.
This is NOT experimental PAD noise characterization.
"""
from fractions import Fraction as F
from random import Random
m=F(3,2)
lam=F(1812744140625,2126873677106)
mu=F(314129536481,2126873677106)
margin=F(2823749272953,68059957667392)
cp1=F(859005471493,34029978833696)
cp3=F(1702471931945,272239830669568)
cq2=F(987235535475,34029978833696)
assert lam>0 and mu>0 and lam+mu==1
assert min(margin,cp1,cp3,cq2)>0

def param(a,b):
    return (1-m+a+2*b,m-2*a-3*b,a,b)
def gap(t,a,b,c,d):
    p=param(a,b);q=param(c,d)
    return sum((p[j]*t**(3*j)-q[j]*t**(4*j) for j in range(4)),F(0))

# The identity is linear in a,b,c,d: verification at the origin and four
# coordinate unit vectors certifies the full identity exactly.
def difference(a,b,c,d):
    return (lam*gap(F(9,10),a,b,c,d)-mu*gap(F(1,2),a,b,c,d)
            -(margin+cp1*(m-2*a-3*b)+cp3*b+cq2*c))
basis=((F(0),)*4, (F(1),F(0),F(0),F(0)),
       (F(0),F(1),F(0),F(0)),(F(0),F(0),F(1),F(0)),
       (F(0),F(0),F(0),F(1)))
assert all(difference(*x)==0 for x in basis)
print("PASS exact affine LP dual identity for all rational parameters")
print("exact margin",margin,"approx",float(margin))

# Optimal nonnegative boundary profiles: p=(1/4,0,3/4,0),
# q=(q0,q1,0,q3), with q3 exact and q0,q1 positive.
d=F(416199750000,1063436838553)
p=param(F(3,4),F(0));q=param(F(0),d)
assert all(v>=0 for v in p+q)
assert sum(p)==sum(q)==1
assert sum(j*p[j] for j in range(4))==sum(j*q[j] for j in range(4))==m
assert gap(F(1,2),F(3,4),F(0),F(0),d)==-margin
assert gap(F(9,10),F(3,4),F(0),F(0),d)==margin
print("PASS exact sharpness on nonnegative simplex",p,q)
print("Comparison: original u=64/125 exact worst-case minimax gap",
      F(6098984073,392987202572),float(F(6098984073,392987202572)))
print("All bounds conditional on fixed alpha ratio, mass, and mean.")
