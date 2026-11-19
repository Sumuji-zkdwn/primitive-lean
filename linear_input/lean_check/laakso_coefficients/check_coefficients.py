"""Exact checks for the six labelled edges; run with Python 3 and SymPy."""

from collections import Counter
from fractions import Fraction as F
from itertools import product
import json

import sympy as s


EDGES = [(0, 4), (1, 4), (4, 5), (4, 5), (5, 2), (5, 3)]
SIGNS = list(product((1, -1), repeat=6))
EXAMPLES = [(1, s.Integer(1)), (4, s.Integer(1)), (1, s.Rational(19, 20)),
            (1, s.Rational(1, 8))]


def laplacian(signs):
    incidence = s.zeros(6)
    for row, ((i, j), sign) in enumerate(zip(EDGES, signs)):
        incidence[row, i] = 1
        incidence[row, j] = -sign
    return incidence.T * incidence


def edge_signs(spin):
    return tuple(spin[i] * spin[j] for i, j in EDGES)


def hessian(lapl, kappa):
    # y=sqrt(2) z. The remaining quartic term is lambda*sum(x_i**4)/4.
    a = s.eye(6) + kappa * lapl
    return a.row_join(-2*s.eye(6)).col_join((-2*s.eye(6)).row_join(2*a))


def pivots(matrix):
    matrix = [[F(entry) for entry in row] for row in matrix.tolist()]
    result = []
    while matrix:
        d = matrix[0][0]
        assert d != 0
        result.append(d)
        matrix = [[matrix[i][j] - matrix[i][0]*matrix[j][0]/d
                   for j in range(1, len(matrix))] for i in range(1, len(matrix))]
    return tuple(result)


def direct_energy(lam, k, signs, x, z):
    local = sum(lam * (v*v - 1/lam)**2 / 4 + (w-v)**2 for v, w in zip(x, z))
    edge = sum((x[i]-a*x[j])**2 + 2*(z[i]-a*z[j])**2
               for a, (i,j) in zip(signs, EDGES))
    return local + k*edge/2


def polynomial_identity():
    lam, k = s.symbols("l k", nonzero=True)
    x = s.Matrix(s.symbols("x:6"))
    z = s.Matrix(s.symbols("z:6"))
    q = x.col_join(z)
    for sign in [(1,)*6, (1,1,1,-1,1,1)]:
        h = hessian(laplacian(sign), k)
        expanded = 3/(2*lam) + lam*sum(a**4 for a in x)/4 + (q.T*h*q)[0]/2
        assert s.expand(direct_energy(lam, k, sign, x, z)-expanded) == 0
    # Check the change from the PR's block in the same rational coordinates.
    v,w,a,b = s.symbols("v w a b")  # (x,z)=(v,w) at leaf, (a,b) at center
    quartic = v**4/4 + a**4/8
    edge = ((v-a)**2 + 2*(w-b)**2 + a*a + 2*b*b)/2
    old = quartic + (v-w-a/2)**2 + (w-a/2-b)**2 + 3*(a-4*b/3)**2/4 + b*b/6
    excess = lambda xx,zz: lam*xx**4/4 - xx**2/2 + (zz-xx)**2
    new = excess(v,w) + excess(a,b)/2 + k*edge
    assert s.expand(new-old-(lam-1)*quartic-(k-1)*edge) == 0


def frac_interval(fun, low, high, steps):
    assert fun(low) < 0 < fun(high)
    for _ in range(steps):
        mid = (low+high)/2
        if fun(mid) < 0:
            low = mid
        else:
            high = mid
    assert fun(low) < 0 < fun(high)
    return low, high


def decimal_enclosure(lo, hi, places=13):
    scale = 10**places
    bot = int(lo*scale // 1)
    top = -int((-hi*scale) // 1)
    def fmt(integer):
        whole, frac = divmod(integer, scale)
        return f"{whole}.{frac:0{places}d}"
    return [fmt(bot), fmt(top)]


def weak_certificate():
    k = s.Rational(1, 8)
    star = laplacian((1,1,1,-1,1,1)).extract([0,1,4], [0,1,4])
    a = s.eye(3) + k*star
    reduced = a - 2*a.inv()
    assert all(d > 0 for d in pivots(a))
    assert all(reduced[i,j] < 0 for i in range(3) for j in range(i))
    t = s.Symbol("t")
    w = s.Matrix([1, 1, t])
    grad = reduced*w
    ampl2 = -grad[0]
    poly = 39*t**4+97*t**3+20*t-78
    assert s.expand(ampl2-(291+117*t)/424) == 0
    assert s.expand(grad[2]+ampl2*t**3-3*poly/424) == 0
    assert all(c > 0 for c in s.Poly(poly.diff(),t).coeffs())
    assert poly.subs(t,0) < 0 < poly.subs(t,1)

    # Weighted graph-square certificate for an arbitrary real state. Match all
    # coefficients modulo the root polynomial, including the three diagonals.
    squares = s.zeros(3)
    for i in range(3):
        for j in range(i):
            direction = s.zeros(3,1)
            direction[i], direction[j] = 1/w[i], -1/w[j]
            squares += -reduced[i,j]*w[i]*w[j]*direction*direction.T
    diag = s.diag(*(ampl2*value**2 for value in w))
    for entry in reduced+diag-squares:
        numerator, denominator = s.fraction(s.cancel(entry))
        assert s.rem(numerator, poly, t) == 0
        assert s.Poly(denominator,t).is_monomial  # denominator nonzero for t>0
    # Verify the constant and the quartic completion for one three-vertex group.
    xx = s.Matrix(s.symbols("u:3"))
    zz = s.Matrix(s.symbols("v:3"))
    quartic_gap = sum((xx[i]**2-ampl2*w[i]**2)**2 for i in range(3))/4
    candidate = s.Rational(3,4) - ampl2**2*(2+t**4)/4
    eliminated = s.Rational(3,4) + sum(v**4 for v in xx)/4 + (xx.T*reduced*xx)[0]/2
    assert s.expand(eliminated-candidate-quartic_gap-(xx.T*(reduced+diag)*xx)[0]/2) == 0
    shifted = zz-a.inv()*xx
    unreduced = s.Rational(3,4) + sum(v**4 for v in xx)/4 + (xx.T*a*xx)[0]/2 - 2*xx.dot(zz) + (zz.T*a*zz)[0]
    assert s.expand(unreduced-eliminated-(shifted.T*a*shifted)[0]) == 0
    f = lambda u: 39*u**4+97*u**3+20*u-78
    low, high = frac_interval(f, F(0), F(1), 120)
    moment = lambda u: F(3,2) - ((291+117*u)/424)**2*(2+u**4)/2
    return {"positive_root_polynomial": str(poly),
            "root_enclosure": decimal_enclosure(low,high),
            "minimum_enclosure": decimal_enclosure(moment(high), moment(low)),
            "squared_amplitude": str(ampl2),
            "energy": "3/2 - ((291+117*t)/424)^2*(2+t^4)/2",
            "minimizers_per_odd_signature": 4}


def main():
    polynomial_identity()
    weak = weak_certificate()
    orbit_size = Counter()
    common = {k: set() for _,k in EXAMPLES}
    t = s.Symbol("t")
    references = [laplacian((1,)*6),laplacian((1,1,1,-1,1,1))]
    for signs in SIGNS:
        odd = int(signs[2]!=signs[3])
        orbit_size[odd] += 1
        lapl = laplacian(signs)
        gauges = [g for g in SIGNS if s.diag(*g)*lapl*s.diag(*g)==references[odd]]
        assert gauges
        spins = [g for g in SIGNS if edge_signs(g)==signs]
        assert len(spins) == (0 if odd else 2)
        if odd:
            charpoly = lapl.charpoly(t).as_expr()
            assert s.expand(charpoly-(t-1)**2*(t**2-5*t+2)**2) == 0
        for l,k in EXAMPLES:
            lam = s.Integer(l)
            zeros = [0]*6
            assert direct_energy(lam,k,signs,zeros,zeros) == 3/(2*lam)
            if odd:
                d = pivots(hessian(lapl,k))
                common[k].add(d)
                if k == s.Rational(1,8):
                    assert any(v < 0 for v in d)
                    witness = list(gauges[0])
                    assert direct_energy(lam,k,signs,witness,witness) == s.Rational(3,4)
                else:
                    assert all(v > 0 for v in d)
            else:
                for g in spins:
                    x = [v/s.sqrt(lam) for v in g]
                    assert direct_energy(lam,k,signs,x,x) == 0
    assert orbit_size == {0:32,1:32}
    assert all(len(rows)==1 for rows in common.values())
    print(json.dumps({
        "signatures": {"even":orbit_size[0],"odd":orbit_size[1]},
        "examples": [{"lambda":str(l),"kappa":str(k),"even_minimum":"0",
                      "even_minimizers":2,
                      "odd_minimum":weak["energy"] if k==s.Rational(1,8) else str(F(3,2*l)),
                      "odd_minimizers":4 if k==s.Rational(1,8) else 1} for l,k in EXAMPLES],
        "odd_hessian_pivots": {str(k):[str(v) for v in next(iter(rows))] for k,rows in common.items()},
        "weak_coupling": weak,
    }, indent=2))


if __name__ == "__main__":
    main()
