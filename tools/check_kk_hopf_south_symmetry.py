#!/usr/bin/env python3
"""Exact polynomial check of Hopf north/south pair-swap symmetry.

Independent symbolic checks; not a replacement for Lean topology.
"""
import sympy as s
X=s.symbols("x0:4",real=True)
rad=lambda t: sum(a*a for a in t)
hopf=lambda t:(2*(t[0]*t[2]+t[1]*t[3]),
               2*(t[0]*t[3]-t[1]*t[2]),
               t[0]**2+t[1]**2-t[2]**2-t[3]**2)
swap=lambda t:(t[2],t[3],t[0],t[1])
assert swap(swap(X))==X
assert s.expand(rad(swap(X))-rad(X))==0
hx,hy,hz=hopf(X)
a,b,c=hopf(swap(X))
for d in (a-hx,b+hy,c+hz):
    assert s.expand(d)==0
print("PASS: pair-swap involution, radius preservation, Hopf base reflection")
C,S=s.symbols("C S",real=True)
def rotate(t):
    return (C*t[0]-S*t[1],S*t[0]+C*t[1],
            C*t[2]-S*t[3],S*t[2]+C*t[3])
assert all(s.expand(a-b)==0 for a,b in zip(swap(rotate(X)),rotate(swap(X))))
print("PASS: pair-swap commutes with diagonal circle action")
w=s.symbols("w",real=True)
assert s.expand((1-(-w))-(1+w))==0
assert s.expand((1+(-w))-(1-w))==0
print("PASS: north/south domains exchange under reflection")
print("SCOPE: Homeomorph must be checked in Lean; smooth atlas and Chern class unproved")
