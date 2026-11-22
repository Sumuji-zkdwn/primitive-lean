"""Exact symbolic curvature certificate from the 5D Ricci-flat KK monopole.

The spatial 4D metric is Taub-NUT in coordinates (r,theta,phi,psi):
  H(dr²+r²dtheta²+r²sin²(theta)dphi²)+H^-1(dpsi+cos(theta)dphi)²
with H=1+1/r, evaluated at (r,theta)=(1,pi/2).

The matrix R_(c,d) has entries (R^a_{bcd}), computed directly using
the full Levi-Civita formula and derivatives of the metric to order two.
The 5D metric adds a trivial -dt²; it is Ricci-flat but not flat.
This produces non-Abelian tangent-bundle holonomy; it does not give a
separate propagating 4D SU(2) Yang-Mills gauge boson.
SymPy 1.14.0; no float operations.
"""
import sympy as s


def curvature_at_point():
    r, th = s.symbols('r theta', real=True, positive=True)
    H, A = 1+1/r, s.cos(th)
    g = s.diag(H, H*r*r, H*r*r*s.sin(th)**2+A*A/H, 1/H)
    g[2,3] = g[3,2] = A/H
    p = {r:s.Integer(1), th:s.pi/2}
    n = 4
    g0 = g.subs(p)
    gi = g0.inv()
    assert g0 == s.diag(2,2,2,s.Rational(1,2))
    assert g0*gi == s.eye(n)
    first = [g.diff(u).subs(p) for u in (r,th)] + [s.zeros(n)]*2
    second = {(i,j):(g.diff((r,th)[i]).diff((r,th)[j]).subs(p)
                     if i<2 and j<2 else s.zeros(n))
              for i in range(n) for j in range(n)}
    D = lambda d,i,j: first[d][i,j]
    D2 = lambda c,d,i,j: second[c,d][i,j]
    gamma = s.MutableDenseNDimArray.zeros(4,4,4)
    deriv = s.MutableDenseNDimArray.zeros(4,4,4,4)
    for a in range(n):
        for b in range(n):
            for c in range(n):
                gamma[a,b,c] = s.expand(sum(
                    gi[a,j]*(D(c,j,b)+D(b,j,c)-D(j,b,c))
                    for j in range(n))/2)
    for z in range(n):
        dgi=-gi*first[z]*gi
        for a in range(n):
            for b in range(n):
                for c in range(n):
                    deriv[z,a,b,c] = s.expand(sum(
                        dgi[a,j]*(D(c,j,b)+D(b,j,c)-D(j,b,c))
                        +gi[a,j]*(D2(z,c,j,b)+D2(z,b,j,c)-D2(z,j,b,c))
                        for j in range(n))/2)
    R={}
    for c in range(n):
        for d in range(c+1,n):
            M=s.Matrix(n,n,lambda a,b:s.expand(
                deriv[c,a,d,b]-deriv[d,a,c,b]
                +sum(gamma[a,c,e]*gamma[e,d,b] -
                     gamma[a,d,e]*gamma[e,c,b] for e in range(n))))
            assert M.T*g0+g0*M==s.zeros(n)
            R[c,d]=M
    return g0,R


def main():
    g,R=curvature_at_point()
    X,Y,Z=R[0,1],R[0,2],R[0,3]
    expected=[
        s.Matrix([[0,-s.Rational(1,8),0,0],
                  [s.Rational(1,8),0,0,0],
                  [0,0,0,s.Rational(1,16)],
                  [0,0,-s.Rational(1,4),0]]),
        s.Matrix([[0,0,-s.Rational(1,8),0],
                  [0,0,0,-s.Rational(1,16)],
                  [s.Rational(1,8),0,0,0],
                  [0,s.Rational(1,4),0,0]]),
        s.Matrix([[0,0,0,s.Rational(1,16)],
                  [0,0,-s.Rational(1,8),0],
                  [0,s.Rational(1,8),0,0],
                  [-s.Rational(1,4),0,0,0]])]
    assert [X,Y,Z]==expected
    assert R[1,2]==-2*Z and R[1,3]==Y/2 and R[2,3]==-X/2
    comm=lambda P,Q:P*Q-Q*P
    assert comm(X,Y)==Z/4 and comm(Y,Z)==X/4 and comm(Z,X)==Y/4
    assert comm(X,Y)[0,3]==s.Rational(1,64)
    assert s.Matrix.hstack(*[M.reshape(16,1) for M in R.values()]).rank()==3
    full=lambda c,d:R[c,d] if c<d else (-R[d,c] if c>d else s.zeros(4))
    ricci=s.Matrix(4,4,lambda b,d:sum(full(a,d)[a,b] for a in range(4)))
    assert ricci==s.zeros(4)
    # Fully contracted coordinate-invariant Kretschmann scalar R_abcd R^abcd.
    # G is diagonal at this one point, so this rational contraction is exact.
    K = s.simplify(sum(
        g[a,a]/(g[b,b]*g[c,c]*g[d,d]) * full(c,d)[a,b]**2
        for a in range(4) for b in range(4)
        for c in range(4) for d in range(4)))
    assert K == s.Rational(3,8), K
    assert X!=s.zeros(4)
    print('PASS: Riemann curvature from metric (6 exact operators)')
    print('PASS: Ricci-flat and metric-skew curvature, rank=3; Kretschmann=3/8')
    print('PASS: [X,Y]=Z/4, [Y,Z]=X/4, [Z,X]=Y/4; (0,3) bracket=1/64')
    print('BOUNDARY: SU(2)-type tangent holonomy is not independent 4D YM')


if __name__=='__main__':
    main()
