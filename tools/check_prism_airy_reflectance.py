#!/usr/bin/env python3
"""Independent exact-rational and complex-amplitude Airy optical checks.

The refractive index n0=1.67667 is a SCHOTT table value at 1529.6nm;
n1=1.4 is explicitly illustrative, NOT measured for an actual fluid.
"""
from fractions import Fraction as Q
import math, cmath

N_GLASS=Q(167667,100000)
N_FLUID=Q(7,5)
N_AIR=Q(1)
LAMBDA_NM=Q(15296,10)


def fresnel(n,m):
    return (n-m)/(n+m)


def airy(a,b,x):
    return (a*a+b*b+2*a*b*x)/(1+a*a*b*b+2*a*b*x)


def amplitude(a,b,phi):
    z=cmath.exp(1j*phi)
    return (float(a)+float(b)*z)/(1+float(a*b)*z)


def film_phase(d):
    return 4*math.pi*float(N_FLUID*d/LAMBDA_NM)


def read(d):
    return airy(float(A), float(B), math.cos(film_phase(d)))


A=fresnel(N_GLASS,N_FLUID)
B=fresnel(N_FLUID,N_AIR)


def main():
    assert A==Q(27667,307667)
    assert B==Q(1,6)
    high=airy(A,B,Q(1))
    low=airy(A,B,Q(-1))
    assert high==(Q(473669,1873669))**2
    assert low==(Q(141665,1818335))**2
    assert high>low
    exact_gap=4*A*B*(1-A*A)*(1-B*B)/((1+A*B)**2*(1-A*B)**2)
    assert high-low==exact_gap

    dh=LAMBDA_NM/(2*N_FLUID)
    dl=3*LAMBDA_NM/(4*N_FLUID)
    assert dl-dh==LAMBDA_NM/(4*N_FLUID)
    assert math.isclose(read(dh),float(high),abs_tol=1e-14)
    assert math.isclose(read(dl),float(low),abs_tol=1e-14)

    for j in range(-100,101):
        d=Q(80+j*17,10)
        phi=film_phase(d)
        r_complex=amplitude(A,B,phi)
        exact=airy(float(A),float(B),math.cos(phi))
        assert math.isclose(abs(r_complex)**2,exact,abs_tol=3e-15)
        assert math.isclose(read(d+LAMBDA_NM/(2*N_FLUID)),read(d),abs_tol=4e-15)

    for x in [Q(-1),Q(-1,3),Q(0),Q(1,7),Q(1)]:
        assert airy(Q(0),B,x)==B*B
        assert airy(A,Q(0),x)==A*A

    margin=float(high-low)/2
    threshold=float(high+low)/2
    for e in [-0.999*margin,0,0.999*margin]:
        assert float(low)+e<threshold<float(high)+e

    # Fold of the previous effective double well E=(h*h-1)^2/4-u*h.
    r=1/math.sqrt(3)
    uc=2/(3*math.sqrt(3))
    assert math.isclose((-r)**3-(-r)-uc,0,abs_tol=1e-14)
    assert math.isclose(3*r*r-1,0,abs_tol=1e-14)
    # Existing ±1 write pulses are above the energy-model fold,
    # but their numerical values are NOT themselves the fold threshold.
    assert uc < 1

    print('PASS 201 complex-amplitude samples vs independent Airy intensity')
    print('PASS 201 film period checks and index-matched no-contrast examples')
    print('PASS exact rational SCHOTT illustrative contrast identity')
    print('PASS scalar-noise classification, effective-energy fold witness')
    print(f'd_high={float(dh):.6f} nm; d_low={float(dl):.6f} nm')
    print(f'R_high={100*float(high):.6f}%, R_low={100*float(low):.6f}%')
    print(f'gap={100*float(high-low):.6f} percentage points; noise margin={100*margin:.6f} points')
    print(f'quartic fold |u|={uc:.9f}, prior ±1 write pulses overdrive it')


if __name__=='__main__':
    main()
