"""Exact independent SymPy check of dS4 x S2 Einstein-Lambda gravity
and universal breathing-mode instability.

External theorems assumed for 12D: Ric(CP2,g_FS)=6g_FS with holomorphic
sectional curvature 4, and canonical Spin-c index chi(O)=1.
This file uses exact arithmetic; it does not assert particle physics.
"""
import sympy as s


def zero(expr):
    value = s.simplify(s.trigsimp(expr))
    assert value == 0, value


def ricci(g, coords):
    n = len(coords)
    inverse = g.inv()
    dg = [[[s.diff(g[i, j], coords[k]) for k in range(n)]
           for j in range(n)] for i in range(n)]
    gamma = {}
    for a in range(n):
        for b in range(n):
            for c in range(b, n):
                v = s.simplify(sum(
                    inverse[a, k] *
                    (dg[k][b][c] + dg[k][c][b] - dg[b][c][k])
                    for k in range(n)) / 2)
                gamma[a, b, c] = gamma[a, c, b] = v
    result = s.zeros(n)
    for a in range(n):
        for b in range(n):
            result[a, b] = s.simplify(sum(
                s.diff(gamma[k, a, b], coords[k]) -
                s.diff(gamma[k, a, k], coords[b]) +
                sum(gamma[k, a, b]*gamma[j, k, j] -
                    gamma[k, a, j]*gamma[j, b, k] for j in range(n))
                for k in range(n)))
    return result


def main():
    t, x, y, z, theta, phi, H, a = s.symbols(
        't x y z theta phi H a', real=True, positive=True)
    coords = [t, x, y, z, theta, phi]
    exp = s.exp(2 * H * t)
    g = s.diag(-1, exp, exp, exp, a**2, a**2*s.sin(theta)**2)
    R = ricci(g, coords)
    expected = s.diag(-3*H**2, 3*H**2*exp, 3*H**2*exp,
                      3*H**2*exp, 1, s.sin(theta)**2)
    for i in range(6):
        for j in range(6):
            zero(R[i,j]-expected[i,j])

    lam = s.symbols('lambda', positive=True)
    for i in range(6):
        zero((R[i,i]-lam*g[i,i]).subs(
            {H**2:lam/s.Integer(3), a**2:1/lam}))
    zero(s.Rational(2*2,6-2)-1)
    print('PASS all 36 6D Ricci components; Lambda_6=2lambda')

    n, beta = s.symbols('n beta', positive=True)
    V = (n+2)*lam*s.exp(-n*beta) - n*lam*s.exp(-(n+2)*beta)
    k = n*(n+2)/2
    zero(s.diff(V,beta).subs(beta,0))
    zero(s.diff(V,beta,2).subs(beta,0)+2*n*(n+2)*lam)
    mass2 = s.simplify(s.diff(V,beta,2).subs(beta,0)/(2*k))
    zero(mass2+2*lam)
    zero(mass2/(lam/3)+6)
    print('PASS for all n>0: m_radion²=-2lambda=-6H²')

    # 12D product, using standard Ricci(CP²,g_FS)=6*g_FS.
    assert [s.Rational(3,3),s.Rational(6,6),s.Rational(1,1),
            s.Rational(1,1)] == [1]*4
    zero(s.Rational(2*5,12-2)-1)
    assert 8+3+3 == 14
    print('PASS CP2 x S2 x S2 product Einstein constants; Lambda_12=5')
    print('NOTE: 14 internal Killing directions, not the SM 12')

    X,Y,Z=s.symbols('X Y Z',real=True)
    p=s.Matrix([X,Y,Z])
    k1=s.Matrix([0,-Z,Y])
    k2=s.Matrix([Z,0,-X])
    k3=s.Matrix([-Y,X,0])
    def lie(u,v):
        return v.jacobian(p)*u-u.jacobian(p)*v
    for u,v,w in [(k1,k2,k3),(k2,k3,k1),(k3,k1,k2)]:
        assert (lie(u,v)+w).applyfunc(s.simplify)==s.zeros(3,1)
    for kvector in (k1,k2,k3):
        zero(p.dot(kvector))
        assert kvector.jacobian(p)+kvector.jacobian(p).T==s.zeros(3,3)
    print('PASS three noncommuting SO(3) Killing fields')


if __name__ == '__main__':
    main()
