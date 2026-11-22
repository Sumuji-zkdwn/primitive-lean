"""Exact symbolic verification of the Kaluza--Klein kinematic witness.

This is an *independent* verification of the full geodesic calculation,
not a derivation of higher-dimensional vacuum Einstein dynamics.
Dependency: sympy==1.14.0.
"""
import sympy as s


def zero(x):
    assert s.simplify(x) == 0, x


def run():
    t, x, y, E = s.symbols('t x y E', real=True)
    ut, ux, uy, q = s.symbols('ut ux uy q', real=True)
    coords = (t, x, y)
    G = s.Matrix([[E**2*x**2-1, 0, E*x],
                  [0, 1, 0],
                  [E*x, 0, 1]])
    Gi = G.inv()
    assert s.factor(G.det()) == -1
    assert (G*Gi-s.eye(3)).applyfunc(s.simplify) == s.zeros(3)

    vel = s.Matrix([ut, ux, uy])
    L = (vel.T*G*vel)[0]/2
    p_y = s.diff(L, uy)
    zero(p_y - (uy+E*x*ut))

    # Routhian reduction: freeze the conserved p_y=q.
    R = s.expand((L-q*uy).subs(uy, q-E*x*ut))
    wanted = (ux**2-ut**2-q**2)/2 + q*E*x*ut
    zero(R-wanted)
    zero(s.diff(R,x)-q*E*ut)
    zero(s.diff(R,ut)-(-ut+q*E*x))
    zero(s.diff(R,ux)-ux)
    zero(s.diff(R,t))

    # Christoffel symbols from the full metric, rather than assumed force laws.
    gamma = {}
    for a in range(3):
        for b in range(3):
            for c in range(3):
                gamma[a,b,c] = s.simplify(sum(
                    Gi[a,d] * (s.diff(G[d,b],coords[c]) +
                               s.diff(G[d,c],coords[b]) -
                               s.diff(G[b,c],coords[d])) / 2
                    for d in range(3)))
    projected_acc = (q*E*ux, q*E*ut)
    full_acc = (*projected_acc, -E*(ux*ut+x*projected_acc[0]))
    fixed_vel = (ut, ux, q-E*x*ut)
    for a in range(3):
        zero(full_acc[a] + sum(
            gamma[a,b,c]*fixed_vel[b]*fixed_vel[c]
            for b in range(3) for c in range(3)))

    # Gauge changes and orientation reversal of the fibre.
    at, ax, alpha, beta = s.symbols('at ax alpha beta')
    def kinetic(a,b,u,v,w):
        return (v*v-u*u+(w+a*u+b*v)**2)/2
    zero(kinetic(at+alpha,ax+beta,ut,ux,uy-alpha*ut-beta*ux)
         -kinetic(at,ax,ut,ux,uy))
    zero(kinetic(-at,-ax,ut,ux,-uy)-kinetic(at,ax,ut,ux,uy))

    # Loop holonomy is independent of changing a local fibre origin.
    e01,e12,e20,l0,l1,l2 = s.symbols('e01 e12 e20 l0 l1 l2')
    zero((e01+l1-l0)+(e12+l2-l1)+(e20+l0-l2)
         -(e01+e12+e20))

    # Important limit: curved model is not vacuum Einstein.
    ricci = s.Matrix(3,3, lambda a,b: s.simplify(sum(
        s.diff(gamma[c,a,b],coords[c]) -
        s.diff(gamma[c,a,c],coords[b]) +
        sum(gamma[c,c,d]*gamma[d,a,b]-gamma[c,b,d]*gamma[d,a,c]
            for d in range(3))
        for c in range(3))))
    curvature = s.factor(s.trace(Gi*ricci))
    zero(curvature-E**2/2)

    # 4D gravity cannot distinguish the charge sign of RN.
    Q,M,r = s.symbols('Q M r', nonzero=True)
    f = 1-2*M/r+Q**2/r**2
    zero(f-f.subs(Q,-Q))

    print('PASS: det/inverse, conserved fibre momentum, Routhian,')
    print('      three full geodesic equations, gauge changes, holonomy,')
    print('      nonvacuum Ricci scalar, 4D sign degeneracy')
    print('R_3 =',curvature)


if __name__ == '__main__':
    run()
