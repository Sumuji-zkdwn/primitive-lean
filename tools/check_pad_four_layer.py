#!/usr/bin/env python3
"""Exact four-layer PAD observation witness; conditional finite forward model.

No fit of an energy-dependent differential scattering cross section, no
experimental depth profile, and no real microjet Monte Carlo simulation.
"""
from fractions import Fraction as Q
from itertools import product
from math import exp, factorial, pi, sin, cos
import json
from pathlib import Path

P_PLUS=(Q(11,60),Q(7,15),Q(1,60),Q(1,3))
P_MINUS=(Q(19,60),Q(1,30),Q(29,60),Q(1,6))

def mean(p):
    return sum(i*w for i,w in enumerate(p))

def response(s,p):
    return sum(w*s**i for i,w in enumerate(p))

def matrix(t,s):
    return [[Q(1)]*4,[Q(0),Q(1),Q(2),Q(3)],
            [Q(1),t,t*t,t*t*t],
            [Q(1),s,s*s,s*s*s]]

def det(A):
    A=[row[:] for row in A]
    value=Q(1)
    for j in range(4):
        k=next((k for k in range(j,4) if A[k][j]),None)
        if k is None: return Q(0)
        if k != j:
            A[j],A[k]=A[k],A[j]
            value=-value
        pivot=A[j][j]
        value*=pivot
        for k in range(j+1,4):
            factor=A[k][j]/pivot
            for l in range(j+1,4):
                A[k][l]-=factor*A[j][l]
            A[k][j]=Q(0)
    return value

def solve(A,b):
    M=[row[:]+[y] for row,y in zip(A,b)]
    for j in range(4):
        k=next((k for k in range(j,4) if M[k][j]),None)
        if k is None: raise ValueError('non-identifiable')
        M[j],M[k]=M[k],M[j]
        pivot=M[j][j]
        M[j]=[v/pivot for v in M[j]]
        for k in range(4):
            if k != j:
                f=M[k][j]
                M[k]=[M[k][l]-f*M[j][l] for l in range(5)]
    return tuple(row[4] for row in M)

def spherical_example_c2():
    # Illustrative spherical Gaussian kernel, 17 degrees is NOT a
    # measurement of the energy-dependent condensed-phase DCS.
    phi=17*pi/180
    w=lambda t: exp(-t*t/(2*phi*phi))*sin(t)
    p2=lambda u: (3*u*u-1)/2
    def simpson(f,n=12000):
        step=pi/n
        return step/3*(f(0)+f(pi)+sum((4 if i%2 else 2)*f(i*step) for i in range(1,n)))
    return simpson(lambda t:w(t)*p2(cos(t)))/simpson(w)

def main():
    assert P_PLUS != P_MINUS
    assert all(v>0 for v in P_PLUS+P_MINUS)
    assert sum(P_PLUS)==sum(P_MINUS)==1
    assert mean(P_PLUS)==mean(P_MINUS)==Q(3,2)
    t=Q(4,5); s=Q(1,2)
    assert response(t,P_PLUS)==response(t,P_MINUS)==Q(369,500)
    assert response(s,P_PLUS)==Q(37,80)
    assert response(s,P_MINUS)==Q(19,40)
    assert response(s,P_MINUS)-response(s,P_PLUS)==Q(1,80)
    for k,j in product(range(-3,16),[2,3,5,7,11]):
        x=Q(k,j)
        assert response(x,P_PLUS)-response(x,P_MINUS)==Q(1,6)*(x-1)**2*(x-t)
    for a,b in product([Q(1,10),Q(1,4),Q(1,2),Q(4,5),Q(9,10)],repeat=2):
        assert det(matrix(a,b))==(b-a)*(1-a)**2*(1-b)**2
        if a!=b:
            for p in (P_PLUS,P_MINUS):
                y=[Q(1),Q(3,2),response(a,p),response(b,p)]
                assert solve(matrix(a,b),y)==p
    c2=Q(4,5); lam=Q(3,2)
    approx=sum(exp(-float(lam))*float(lam)**n/factorial(n)*float(c2)**n for n in range(35))
    assert abs(approx-exp(-float(lam*(1-c2))))<1e-14
    result={
      'result':'PASS', 'physical_scope':'idealized four-layer observation model',
      'p_plus':list(map(str,P_PLUS)), 'p_minus':list(map(str,P_MINUS)),
      'mass':'1','mean':'3/2','t':'4/5','s':'1/2',
      'response_t':'369/500', 'response_s_plus':'37/80',
      'response_s_minus':'19/40','gap_s':'1/80',
      'determinant_t_s':str(det(matrix(t,s))),
      'illustrative_spherical_17deg_c2':spherical_example_c2(),
      'poisson_identity':'checked by truncated sum'
    }
    dest=Path('docs/pad_four_layer_results.json')
    dest.parent.mkdir(exist_ok=True,parents=True)
    dest.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    main()
