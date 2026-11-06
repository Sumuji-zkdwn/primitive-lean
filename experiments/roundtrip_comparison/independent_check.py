"""Independent numerical re-check of the GPT-side probe (gpt/primitive_465_roundtrip_experiment.py).

Not Lean verification.  Uses a different integrator (fixed-step classical RK4, written here)
and finite differences, and checks the closed-form identities that are proved in Lean in
C01_GPTComparison.inc.  Output: independent_check.json next to this file.
"""
import json
import math
import pathlib

import numpy as np
from scipy.integrate import solve_ivp

HERE = pathlib.Path(__file__).resolve().parent
LAM, R, U, GAMMA, TARGET, BETA = 1.0, 1.0, 0.0, 1.0, 0.5, 2.0
S2 = math.sqrt(2.0)


def E(x, y, lam=LAM, r=R, u=U):
    return lam * x**4 / 4 + r * x * x / 2 - u * x + (y - S2 * x) ** 2 / 2


def grad(x, y, lam=LAM, r=R, u=U):
    return np.array([lam * x**3 + (r + 2) * x - S2 * y - u, y - S2 * x])


def field(z, b, gamma=GAMMA, target=TARGET, lam=LAM, r=R, u=U):
    g = grad(*z, lam, r, u)
    e = E(*z, lam, r, u) - target
    return -gamma * e * g + b * np.array([-g[1], g[0]])


def rk4(z0, b, T, n, **kw):
    h = T / n
    z = np.array(z0, float)
    out = [z.copy()]
    for _ in range(n):
        k1 = field(z, b, **kw)
        k2 = field(z + h / 2 * k1, b, **kw)
        k3 = field(z + h / 2 * k2, b, **kw)
        k4 = field(z + h * k3, b, **kw)
        z = z + h / 6 * (k1 + 2 * k2 + 2 * k3 + k4)
        out.append(z.copy())
    return np.array(out), h


def logistic(e):
    return 1.0 / (1.0 + math.exp(BETA * e))


def entropy(p):
    return -(p * math.log(p) + (1 - p) * math.log1p(-p))


def entropy_closed(e):
    # Lean: entropy_logistic  H(p(e)) = β e p(e) + log(1 + exp(-β e))
    return BETA * e * logistic(e) + math.log1p(math.exp(-BETA * e))


def free_energy(e1, e2, beta=BETA):
    return -math.log(math.exp(-beta * e1) + math.exp(-beta * e2)) / beta


report = {"integrator": "classical RK4, fixed step (independent of scipy DOP853)", "cases": {}}
for label, z0, b in [("below_target", (0.0, 0.5), 0.0), ("above_target", (0.0, 1.5), 0.0),
                     ("shell_stationary", (0.0, 1.0), 0.0), ("shell_circulating", (0.0, 1.0), 1.0)]:
    zs, h = rk4(z0, b, 20.0, 20000)
    es = np.array([E(*z) - TARGET for z in zs])
    Hs = np.array([entropy(logistic(e)) for e in es])
    # finite-difference derivatives at interior points vs. closed forms
    de_fd = (es[2:] - es[:-2]) / (2 * h)
    de_formula = np.array([-GAMMA * e * np.sum(grad(*z) ** 2) for e, z in zip(es[1:-1], zs[1:-1])])
    dH_fd = (Hs[2:] - Hs[:-2]) / (2 * h)
    dH_formula = np.array([BETA**2 * GAMMA * e * e * np.sum(grad(*z) ** 2) * logistic(e) * (1 - logistic(e))
                           for e, z in zip(es[1:-1], zs[1:-1])])
    abs_e = np.abs(es)
    report["cases"][label] = {
        "e_initial": float(es[0]), "e_final": float(es[-1]), "z_final": zs[-1].tolist(),
        "max_abs_de_fd_minus_formula": float(np.max(np.abs(de_fd - de_formula))),
        "max_abs_dH_fd_minus_formula": float(np.max(np.abs(dH_fd - dH_formula))),
        "min_dH_increment": float(np.diff(Hs).min()),
        "max_abs_e_increment_(should_be_<=0)": float(np.diff(abs_e).max()),
        "max_abs_entropy_closed_form_error": float(max(abs(entropy(logistic(e)) - entropy_closed(e)) for e in es)),
        "max_energy_drift": float(np.max(np.abs(es - es[0]))),
    }

# Raw (unrounded) values from the GPT run, to resolve the printed "-0.0".
gpt = json.loads((HERE / "gpt/primitive_465_roundtrip_results.json").read_text(encoding="utf-8"))
report["gpt_raw_H_monotonic_min_increment"] = {k: v["H_monotonic_min_increment"]
                                                for k, v in gpt["trajectories"].items()}

# Period of the circulating shell orbit (b = 1, γ irrelevant on the shell since e = 0).
# The start (0, 1) moves towards x < 0; it returns through x = 0 downward (direction -1).
# The upward crossing is at (0, -1), half a period later (E and the field are odd/even
# under z -> -z).
def crossing(t, z):
    return z[0]
crossing.direction = -1.0
sol = solve_ivp(lambda t, z: field(z, 1.0), (0, 40), (0.0, 1.0), method="RK45", rtol=1e-11,
                atol=1e-12, events=crossing, dense_output=True)
tc = [t for t in sol.t_events[0] if t > 1e-3]
period = float(tc[0]) if tc else None
report["shell_circulating_period_from_x_downcrossing"] = period
if period:
    zp = sol.sol(period)
    report["shell_orbit_return_error"] = float(np.linalg.norm(zp - np.array([0.0, 1.0])))
    report["shell_T20_over_period"] = 20.0 / period

# Thermodynamic identities linking the GPT observer with R05 (Lean: C01).
es_grid = np.linspace(-3, 3, 61)
report["max_err_p_eq_gibbs_two_state"] = float(max(
    abs(logistic(e) - math.exp(-BETA * e) / (math.exp(-BETA * e) + 1.0)) for e in es_grid))
report["max_err_entropy_eq_beta_U_minus_F"] = float(max(
    abs(entropy(logistic(e)) - BETA * (logistic(e) * e - free_energy(e, 0.0))) for e in es_grid))
hh = 1e-6
report["max_err_p_eq_dF_de1"] = float(max(
    abs((free_energy(e + hh, 0.0) - free_energy(e - hh, 0.0)) / (2 * hh) - logistic(e)) for e in es_grid))
report["max_err_tanh_eq_2p_minus_1"] = float(max(
    abs(math.tanh(-BETA * e / 2) - (2 * logistic(e) - 1)) for e in es_grid))

# Independence: exact odds law vs. the product.
p1 = logistic(1.0)
report["independence"] = {
    "p(2)": logistic(2.0), "p(1)^2": p1 * p1,
    "odds_law_p1p2/(p1p2+(1-p1)(1-p2))": p1 * p1 / (p1 * p1 + (1 - p1) ** 2),
    "product_always_smaller_on_grid": all(logistic(a + c) > logistic(a) * logistic(c)
                                          for a in es_grid for c in es_grid),
}

# Circulation term with b = -1, γ = 0 equals the CurvatureBridge phase flow at λ = 1/2, r = -σ/k.
k, sigma, kap, kap1 = 1.3, 0.7, 0.4, -0.25
w = kap1 + S2 * kap
g = grad(kap, w, 0.5, -sigma / k, 0.0)
report["circulation_vs_curvature_flow"] = {
    "gpt_field_b=-1_gamma=0": field(np.array([kap, w]), -1.0, gamma=0.0, lam=0.5, r=-sigma / k).tolist(),
    "curvature_phase_velocity_(gy,-gx)": [float(g[1]), float(-g[0])],
    "kappa_double_prime_from_ODE": float(sigma / k * kap - kap**3 / 2),
    "w_prime_should_equal_kappa_double_prime_plus_sqrt2_kappa_prime": float(sigma / k * kap - kap**3 / 2 + S2 * kap1),
}

# Regime: GPT uses λ = 1, r = 1 > 0 (single well); R04's corner needs r < 0.
def value(u, lam, r):
    xs = np.linspace(-3, 3, 600001)
    return float(np.min(lam * xs**4 / 4 + r * xs**2 / 2 - u * xs))  # y = √2 x is optimal
d = 1e-3
report["value_one_sided_slopes_at_u0"] = {
    "gpt_regime_(1,1)": [(value(d, 1, 1) - value(0, 1, 1)) / d, (value(0, 1, 1) - value(-d, 1, 1)) / d],
    "R04_regime_(1,-1)": [(value(d, 1, -1) - value(0, 1, -1)) / d, (value(0, 1, -1) - value(-d, 1, -1)) / d],
}

# Scaling conjugacy (Lean: circulation_scale): GPT's shell orbit at λ = 1, r = 1, with the
# circulation reversed (b = -1, γ = 0), divided by α = 1/√2, should be a λ = 1/2, r = 1 orbit,
# i.e. κ(s) = √2 x(s) should solve κ'' = -κ - κ³/2 (baseline curvature equation, σ/k = -1).
sol2 = solve_ivp(lambda t, z: field(z, -1.0, gamma=0.0), (0, 12), (0.0, 1.0), method="DOP853",
                 rtol=1e-12, atol=1e-13, dense_output=True)
ss = np.linspace(0.5, 11.5, 2201)
hs = 1e-3
kap = lambda s: S2 * sol2.sol(s)[0]
res = [abs((kap(s + hs) - 2 * kap(s) + kap(s - hs)) / hs**2 + kap(s) + kap(s) ** 3 / 2) for s in ss]
wv = lambda s: S2 * sol2.sol(s)[1]
res_w = [abs(wv(s) - ((kap(s + hs) - kap(s - hs)) / (2 * hs) + S2 * kap(s))) for s in ss]
report["gpt_shell_orbit_as_curvature_equation"] = {
    "max_residual_kappa''+kappa+kappa^3/2": float(max(res)),
    "max_residual_w_minus_(kappa'+sqrt2*kappa)": float(max(res_w)),
    "phase_energy_lambda_half_r_one": float(E(*(S2 * np.array([0.0, 1.0])), 0.5, 1.0, 0.0)),
}
(HERE / "independent_check.json").write_text(json.dumps(report, indent=1, ensure_ascii=False) + "\n",
                                             encoding="utf-8")
print(json.dumps(report, indent=1, ensure_ascii=False))
