"""Independent exact-rational regression for the Okanohara curvature bridge.

These finite checks complement, but do not replace, Lean proofs that quantify
over all real inputs. They require only Python's standard Fraction type.
"""
from fractions import Fraction as F


def potential(x):
    return (x*x - 1)**2 * ((x+1)**2 + 2) / F(16)


def response_left(t):
    return (t-2)**2 * (t*t + 2) / F(8)


def response_right(t):
    return (t+2)**2 * ((t+2)**2 + 2) / F(8)


def step_energy(old, new, drive):
    well = F(1) if new else F(-1)
    return potential(well) - drive*well + (F(2) if old != new else F(0))


def switch(old, drive):
    if F(1) <= drive:
        return True
    if drive <= F(-1):
        return False
    return old


def test_exact_well_quadratic_coefficients():
    assert potential(F(-1)) == potential(F(1)) == 0
    assert response_left(F(0)) == 1
    assert response_right(F(0)) == 3
    for i in range(-40, 41):
        t = F(i, 12)
        assert 2*potential(-1+t) == t*t*response_left(t)
        assert 2*potential(1+t) == t*t*response_right(t)


def test_hysteretic_energy_minimization():
    for old in (False, True):
        for i in range(-30, 31):
            drive = F(i, 10)
            new = switch(old, drive)
            assert step_energy(old, new, drive) <= step_energy(old, not new, drive)


def test_pressure_work_and_constant_vs_exponential_cascade():
    for q in (False, True):
        k = F(3 if q else 1)
        for di in range(-10, 11):
            d = F(di, 4)
            pressure = k*d
            at_d = k*d*d / 2 - pressure*d
            for zi in range(-10, 11):
                z = F(zi, 4)
                at_z = k*z*z / 2 - pressure*z
                assert at_z - at_d == k*(z-d)**2 / 2
                assert at_d <= at_z
    for n in range(1, 11):
        d = F(5, 7)
        assert (F(3*n)*d)**2 == 9*(F(n)*d)**2
        assert (F(3)**n*d)**2 == F(9)**n*d*d


def test_two_step_history_conditioned_gramian():
    for k in (F(1), F(3)):
        gramian = F(2) / (k*k)
        assert gramian > 0
        for i in range(-8, 9):
            d = F(i, 5)
            u_star = k*d/F(2)
            assert (u_star + u_star)/k == d
            assert 2*u_star*u_star == d*d/gramian
        for i in range(-6, 7):
            for j in range(-6, 7):
                u, v = F(i, 4), F(j, 4)
                d = (u+v)/k
                assert u*u+v*v >= d*d/gramian
    assert F(2)/(F(1)*F(1)) == 2
    assert F(2)/(F(3)*F(3)) == F(2, 9)
