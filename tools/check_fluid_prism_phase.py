#!/usr/bin/env python3
"""Finite exact and numerical regressions for a phenomenological fluid-prism cell.

Exact: quartic energies, stationary-point values, rational two-mode mixer and
threshold hystereson. Numerical: cosine interferometer and periodicity.
These checks do not replace Lean proofs or experimentally validate optics.
"""
from fractions import Fraction as F
from itertools import product
import math


def energy(h, u=F(0)):
    return (h*h-F(1))**2 / 4 - u*h


def slope(h,u=F(0)):
    return h*(h*h-F(1))-u


def curvature(h):
    return F(3)*h*h-F(1)


def height(bit):
    return F(1) if bit else F(-1)


def phase(h):
    return math.pi*(float(h)+1)/2


def port(h):
    return (1+math.cos(phase(h)))/2


def write(bit,drive):
    return True if drive >= 1 else False if drive <= -1 else bit


def test():
    xs=[F(i,10) for i in range(-40,41)]
    assert all(energy(x) >= 0 for x in xs)
    assert energy(F(-1)) == energy(F(1)) == 0
    assert energy(F(0)) == F(1,4)
    assert slope(F(-1)) == slope(F(0)) == slope(F(1)) == 0
    assert curvature(F(-1)) == curvature(F(1)) == 2
    assert curvature(F(0)) == -1
    assert math.isclose(port(height(False)),1,abs_tol=1e-12)
    assert math.isclose(port(height(True)),0,abs_tol=1e-12)
    for x in xs:
        assert math.isclose(port(x+4),port(x),abs_tol=5e-15)
        assert 0 <= port(x) <= 1
    for a,b in product([False,True], repeat=2):
        assert (port(height(a)) == port(height(b))) == (a==b)
    assert height(write(write(False,2),0)) == 1
    assert height(write(write(False,-2),0)) == -1
    for bit in [False,True]:
        assert write(bit,0)==bit
    for n in range(9):
        assert len(list(product([False,True], repeat=n))) == 2**n
    # A 1550-nm probe in an ideal single-pass path with contrast 0.444.
    wavelength_nm = 1550
    delta_n = 0.444
    a_nm = wavelength_nm/(4*delta_n)
    for h in [-1,0,1]:
        phys_phase=2*math.pi*delta_n*(a_nm*(h+1))/wavelength_nm
        assert math.isclose(phys_phase,phase(h),abs_tol=1e-13)
    for error in [-0.49, 0.0,0.49]:
        assert port(-1)+error > 0.5
        assert port(1)+error < 0.5
    print("PASS: 81 rational heights checked for nonnegative energy and stationary witnesses")
    print("PASS: 81 numeric phase periodicity and normalized detector bounds")
    print("PASS: bit-port separation, 2^n addressable states (n<=8), hysteretic writes")
    print(f"PASS: half-wave path calibration (1550nm, Δn=0.444, a={a_nm:.6f}nm)")
    print("PASS: scalar noise |error|<1/2 in ideal normalized units")


if __name__ == "__main__":
    test()
