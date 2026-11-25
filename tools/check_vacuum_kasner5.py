"""Exact 5D vacuum Kasner -> 4D Einstein-frame cosmology audit.

One metric only: ds5^2 = -dt^2 + t^(2p) d(x,y,z)^2 + t^(2q) dchi^2.
chi is periodic, t>0. No independent matter, gauge fields or flux.
SymPy 1.14.0; all curvature tensors recomputed from the metric itself.
The reduced scalar is a name for the circle radius in the 5D metric,
not an additional fundamental field.
"""
import sympy as s

T = s.symbols("t", positive=True)
p, q = s.symbols("p q", real=True)


def geometry(metric, riemann=False):
    n = metric.rows
    gprime = [s.diff(metric[i, i], T) for i in range(n)]
    coeff = {}
    for i in range(n):
        if i > 0:
            coeff[(0, i, i)] = -gprime[i] / (2 * metric[0, 0])
            coeff[(i, 0, i)] = gprime[i] / (2 * metric[i, i])
            coeff[(i, i, 0)] = coeff[(i, 0, i)]
        else:
            coeff[(0, 0, 0)] = gprime[0] / (2 * metric[0, 0])

    def gamma(a, b, c):
        return coeff.get((a, b, c), 0)

    def derivative(expr, i):
        return s.diff(expr, T) if i == 0 else s.S.Zero

    def curvature(a, b, c, d):  # R^a_{bcd}, directly from Christoffels
        return s.simplify(
            derivative(gamma(a, d, b), c)
            - derivative(gamma(a, c, b), d)
            + sum(
                gamma(a, c, e) * gamma(e, d, b)
                - gamma(a, d, e) * gamma(e, c, b)
                for e in range(n)
            )
        )

    ricci = s.Matrix(
        n, n,
        lambda b, d: s.simplify(sum(curvature(a, b, a, d) for a in range(n)))
    )
    if not riemann:
        return ricci
    nonzero = {
        (a, b, c, d): v
        for a in range(n)
        for b in range(n)
        for c in range(n)
        for d in range(n)
        if (v := curvature(a, b, c, d)) != 0
    }
    # Diagonal metric: R_abcd = g_aa R^a_bcd;
    # R_abcd R^abcd = sum R_abcd^2/(g_aa*g_bb*g_cc*g_dd).
    kretschmann = s.factor(sum(
        (metric[a, a] * v)**2
        / (metric[a, a] * metric[b, b] * metric[c, c] * metric[d, d])
        for (a, b, c, d), v in nonzero.items()
    ))
    return ricci, kretschmann, nonzero


general_metric = s.diag(
    -1, T**(2*p), T**(2*p), T**(2*p), T**(2*q)
)
ricci_general = geometry(general_metric)
assert s.simplify(
    ricci_general[0, 0] - (3*p*(1-p) + q*(1-q)) / T**2
) == 0
for i in (1, 2, 3):
    assert s.simplify(
        ricci_general[i, i] - p * (3*p+q-1) * T**(2*p-2)
    ) == 0
assert s.simplify(
    ricci_general[4, 4] - q * (3*p+q-1) * T**(2*q-2)
) == 0
assert all(
    ricci_general[i, j] == 0
    for i in range(5) for j in range(5) if i != j
)

# Full real power-law vacuum classification, including static (0,0).
time_residual = 3*p*(1-p) + q*(1-q)
external_residual = p * (3*p+q-1)
circle_residual = q * (3*p+q-1)
assert s.solve_poly_system(
    [time_residual, external_residual, circle_residual], p, q
) == [
    (s.S.Zero, s.S.Zero),
    (s.S.Zero, s.S.One),
    (s.Rational(1, 2), -s.Rational(1, 2))
]
print("PASS all real power-law branches: static, Milne, expanding Kasner")

metric5 = general_metric.subs({
    p: s.Rational(1, 2), q: -s.Rational(1, 2)
})
ricci5, K5, components5 = geometry(metric5, riemann=True)
assert all(v == 0 for v in ricci5)  # all 25 entries
assert s.factor(K5 - s.Rational(9, 2) / T**4) == 0
powers = [s.Rational(1, 2)]*3 + [-s.Rational(1, 2)]
K_independent = 4 * (
    sum((v*(v-1))**2 for v in powers)
    + sum(
        powers[i]**2 * powers[j]**2
        for i in range(4) for j in range(i+1, 4)
    )
) / T**4
assert s.factor(K5 - K_independent) == 0
print("PASS 5D Ricci_5=0 componentwise; Kretschmann=9/(2*t^4) by two methods")

# Circle radius b=t^(-1/2).  ds5^2 = b^(-1)*ds_E4^2 + b^2*dchi^2.
# Define phi=(sqrt(3)/2)*log(b), so the standard 4D Einstein-frame
# vacuum equations are Ric_E(mu,nu)=2*d_mu phi*d_nu phi and box_E phi=0.
b = T**(-s.Rational(1, 2))
metricE = s.diag(-b, *([b*T]*3))
ricciE = geometry(metricE)
phi_prime = -s.sqrt(3) / (4*T)
for i in range(4):
    for j in range(4):
        source = 2 * phi_prime**2 if (i, j) == (0, 0) else s.S.Zero
        assert s.simplify(ricciE[i, j] - source) == 0, (i, j)
sqrt_abs_detE = T**s.Rational(1, 2)
assert s.simplify(
    s.diff(sqrt_abs_detE * (1/metricE[0,0]) * phi_prime, T)
) == 0
print("PASS 4D Einstein-frame Ricci=2*dphi*dphi, scalar box(phi)=0")

# Einstein proper time tau = (4/3)t^(3/4) ; a_E=t^(1/4).
tau = s.Rational(4, 3) * T**s.Rational(3, 4)
scaleE = T**s.Rational(1, 4)
H = s.simplify(s.diff(scaleE, T)/scaleE / s.diff(tau, T))
assert s.simplify(H-1/(3*tau)) == 0
phi_dot = s.simplify(phi_prime / s.diff(tau, T))
assert s.simplify(phi_dot**2 - 3*H**2) == 0
scale_dot = s.simplify(s.diff(scaleE,T)/s.diff(tau,T))
scale_ddot = s.simplify(s.diff(scale_dot,T)/s.diff(tau,T))
assert s.simplify(scale_ddot + 2*scaleE/(9*tau**2)) == 0
assert scale_ddot.is_negative
print("PASS a_E propto tau^(1/3), massless scalar w=1; decelerating")

# Bare 4D chi=constant slice g_J is *not* Einstein frame.
# Its Einstein tensor looks radiation-like, w_J=1/3, but this is
# a frame-dependent geometric effective stress tensor, not real matter.
metricJ = s.diag(-1, T, T, T)
ricciJ = geometry(metricJ)
scalarJ = s.simplify(sum(
    ricciJ[i,i] / metricJ[i,i] for i in range(4)
))
G00J = s.simplify(ricciJ[0,0] - metricJ[0,0]*scalarJ/2)
G11J = s.simplify(ricciJ[1,1] - metricJ[1,1]*scalarJ/2)
assert s.simplify(G00J - 3/(4*T**2)) == 0
assert s.simplify(G11J/metricJ[1,1]/G00J - s.Rational(1,3)) == 0
print("PASS raw 4D slice apparent w=1/3 vs Einstein-frame w=1")
print("LIMITS preexisting Kasner; curvature singularity t=0; U(1) only")
