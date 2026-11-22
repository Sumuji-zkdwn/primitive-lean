"""Exact Kaluza--Klein magnetic flux from 5D locally flat geometry.

Global construction: helical S¹ identification. Checks the metric pullback,
the reduced geometric gauge field, nonzero F, and a field equation.
Dependency: sympy==1.14.0; no floating-point approximations.
"""
import sympy as s


def check(expr):
    assert s.simplify(s.trigsimp(expr)) == 0, s.simplify(expr)


def main():
    t,z,r,theta,y,B = s.symbols('t z r theta y B', real=True)
    coords = s.Matrix([t,z,r,theta,y])
    # The twist is simply a coordinate change of flat 5D Minkowski locally.
    X = r*s.cos(theta+B*y)
    Y = r*s.sin(theta+B*y)
    flat_coords = s.Matrix([t,z,X,Y,y])
    J = flat_coords.jacobian(coords)
    pulled = (J.T*s.diag(-1,1,1,1,1)*J).applyfunc(
        s.trigsimp).applyfunc(s.simplify)
    target = s.Matrix([
        [-1,0,0,0,0], [0,1,0,0,0], [0,0,1,0,0],
        [0,0,0,r*r,B*r*r],
        [0,0,0,B*r*r,1+B*B*r*r]])
    assert (pulled-target).applyfunc(s.simplify) == s.zeros(5)

    lam = 1+B*B*r*r
    conn = B*r*r/lam  # geometric connection; EM A_theta often conn/2
    base_phi_phi = r*r/lam
    check(base_phi_phi+lam*conn**2-r*r)
    check(lam*conn-B*r*r)
    Frtheta = s.diff(conn,r)
    check(Frtheta - 2*B*r/lam**2)
    assert s.simplify(Frtheta.subs({B:2,r:1})) != 0

    # Jordan-frame 4D metric h=diag(-1,1,1,r²/lam), circle radius phi=√lam.
    # Check reduced Maxwell equation ∂r(√|h| phi³ F^{rθ})=0.
    phi = s.sqrt(lam)
    sqrt_h = r/phi  # r>0
    raisedF = Frtheta*lam/r**2
    weighted_flux = s.simplify(sqrt_h*phi**3*raisedF)
    check(weighted_flux-2*B)
    check(s.diff(weighted_flux,r))

    # Reduced Ricci-scalar relation: zero since parent metric is flat.
    # h is 2D Minkowski times a radial surface with f=r/sqrt(lam).
    f = r/s.sqrt(lam)
    Ric_h = 6*B*B/lam**2
    check(Ric_h + 2*s.diff(f,r,2)/f)
    F2 = 2*Frtheta*raisedF
    check(F2-8*B*B/lam**3)
    box_phi = s.simplify(s.diff(sqrt_h*s.diff(phi,r),r)/sqrt_h)
    check(box_phi-2*B*B/lam**s.Rational(3,2))
    check(Ric_h - phi**2*F2/4 - 2*box_phi/phi)

    print("PASS: 5D vacuum flat pullback, KK square completion,")
    print("      nonzero reduced flux, Maxwell-dilaton equation,")
    print("      scalar-curvature identity.")
    print("A_theta =",conn)
    print("F_rtheta =",s.factor(Frtheta))
    print("weighted flux =",weighted_flux)


if __name__ == '__main__':
    main()
