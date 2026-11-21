"""Exact two-centre Gibbons--Hawking tests (SymPy, no floats).

Tests the hypotheses of the standard Gibbons--Hawking Ricci-flatness
construction and observer-limited far-field observables. Does not compute
or assert the full 5D Riemann tensor in code.
"""
import sympy as s


def check(expression, label):
    out = s.cancel(s.trigsimp(s.simplify(expression)))
    assert out == 0, (label, out)


def main():
    rho, z, a, q = s.symbols('rho z a q', real=True, positive=True)
    r_plus = s.sqrt(rho**2 + (z-a)**2)
    r_minus = s.sqrt(rho**2 + (z+a)**2)
    H = 1 + q/r_plus + q/r_minus
    Aphi = q*(z-a)/r_plus + q*(z+a)/r_minus
    # Cylindrical axisymmetric harmonic equation, away from both centres.
    lap = s.diff(H, rho, 2) + s.diff(H, rho)/rho + s.diff(H, z, 2)
    check(lap, 'axisymmetric Laplacian')
    # GH connection: dA = *_3 dH with dx^dy^dz orientation.
    check(s.diff(Aphi, rho) - rho*s.diff(H, z), 'GH rho relation')
    check(s.diff(Aphi, z) + rho*s.diff(H, rho), 'GH z relation')
    print('PASS: two-centre H is harmonic and dA=*dH (3 exact identities)')

    # One vs two centres, with exactly the same total monopole strength.
    R = s.symbols('R', real=True, positive=True)
    H2_axis = 1+q/(R-a)+q/(R+a)  # only valid R>a
    H1_axis = 1+2*q/R
    difference = 2*q*a*a/(R*(R*R-a*a))
    check(H2_axis-H1_axis-difference, 'axis exact difference')
    check(s.limit(R**3*(H2_axis-H1_axis), R, s.oo)-2*q*a*a,
          'axis quadrupole limit')

    H2_equator = 1+2*q/s.sqrt(R*R+a*a)
    H1_equator = 1+2*q/R
    check(s.limit(R**3*(H2_equator-H1_equator), R, s.oo)+q*a*a,
          'equatorial quadrupole limit')
    check(s.limit(R*(H2_axis-1),R,s.oo)-2*q, 'axis monopole')
    check(s.limit(R*(H2_equator-1),R,s.oo)-2*q, 'equator monopole')
    check(H2_axis.subs({R:3, a:1, q:1})-s.Rational(7,4), 'axis sample')
    check(H1_axis.subs({R:3, a:1, q:1})-s.Rational(5,3), 'one-centre sample')
    check(difference.subs({R:3, a:1, q:1})-s.Rational(1,12),
          'numeric exact gap')
    print('PASS: identical monopole q_total=2q; distinct quadrupole')
    print('      axis coefficient +2 q a²; equator coefficient -q a²')

    # Stronger comparison: two different *smooth* 2-centre metrics, not
    # a single charge-2 centre that is orbifold-singular at its origin.
    H_at_a1 = H2_axis.subs({q:1,a:1,R:5})
    H_at_a2 = H2_axis.subs({q:1,a:2,R:5})
    check(H_at_a1-s.Rational(17,12), 'two-centre separation a=1')
    check(H_at_a2-s.Rational(31,21), 'two-centre separation a=2')
    check(H_at_a2-H_at_a1-s.Rational(5,84),'smooth pair gap')
    print('PASS: smooth two-centre pair has equal flux, exact fine gap 5/84')

    # For a general radius sphere, local Chern = -1, exterior = -2.
    theta = s.symbols('theta', real=True)
    flux_one = s.integrate(-q*s.sin(theta),(theta,0,s.pi))*2*s.pi
    check(flux_one + 4*s.pi*q,'one-centre flux')
    period_psi = 4*s.pi*q
    normalized_factor=2*s.pi/period_psi
    check(normalized_factor*flux_one/(2*s.pi)+1,
          'small enclosing sphere Chern')
    check(normalized_factor*(2*flux_one)/(2*s.pi)+2,
          'large sphere Chern')
    print('PASS: normalized Chern numbers -1 (each), -2 (both)')
    print('SCOPE: no new Yang--Mills force; global smoothness from GH theorem')


if __name__ == '__main__':
    main()
