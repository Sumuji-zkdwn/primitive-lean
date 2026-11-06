#!/usr/bin/env python3
"""Independent IVP check for PR #88's two-motion outgoing-channel model.

Only Python's standard library is required. Integrates the five-state ODE plus
cumulative emitted work with classical RK4; estimates global error by step
doubling (order-four Richardson factor 15). Also computes exact rational
Taylor coefficients by formal power-series substitution. This is numerical and
finite algebraic evidence, not an analytic ODE existence proof.
"""
from fractions import Fraction as Q
from itertools import product
from math import isfinite
import json


def force(s, p):
    k, c, g, w1, w2 = p
    x1, v1, x2, v2, y, work = s
    return k * (g * x1 * x2 - y)


def energy(s, p):
    k, c, g, w1, w2 = p
    x1, v1, x2, v2, y = s[:5]
    return (v1*v1 + w1*w1*x1*x1 + v2*v2 + w2*w2*x2*x2)/2 + k*(y-g*x1*x2)**2/2


def rhs(s, p):
    k, c, g, w1, w2 = p
    x1, v1, x2, v2, y, work = s
    f = k * (g * x1 * x2 - y)
    return (v1,
            -w1*w1*x1 - g*x2*f,
            v2,
            -w2*w2*x2 - g*x1*f,
            f/(2*c),
            f*f/(2*c))


def add_scaled(a, b, scale):
    return tuple(x + scale*y for x, y in zip(a, b))


def rk4_step(s, h, p):
    k1 = rhs(s, p)
    k2 = rhs(add_scaled(s, k1, h/2), p)
    k3 = rhs(add_scaled(s, k2, h/2), p)
    k4 = rhs(add_scaled(s, k3, h), p)
    return tuple(x + h*(a + 2*b + 2*c + d)/6
                 for x, a, b, c, d in zip(s, k1, k2, k3, k4))


def integrate(p, initial, steps, sample_every=None):
    h = 1.0 / steps
    s = tuple(float(v) for v in initial) + (0.0,)
    samples = [(0.0, s)]
    for i in range(1, steps+1):
        s = rk4_step(s, h, p)
        if sample_every and i % sample_every == 0:
            samples.append((i*h, s))
    return s, samples


def conv(a, b, n):
    return sum((a[i]*b[n-i] for i in range(n+1)), Q(0))


def taylor_coefficients(p, initial, order=8):
    """Return exact coefficients a_n in state(t)=sum a_n t^n."""
    k, c, g, w1, w2 = p
    x10, v10, x20, v20, y0 = initial
    # Five ODE coordinates followed by W, all coefficient arrays start at n=0.
    coeff = [[Q(0) for _ in range(order+1)] for _ in range(6)]
    for row, value in zip(coeff, (x10, v10, x20, v20, y0, Q(0))):
        row[0] = value
    for n in range(order):
        f_n = k*(g*conv(coeff[0], coeff[2], n)-coeff[4][n])
        rhs_n = (
            coeff[1][n],
            -w1*w1*coeff[0][n]-g*conv(coeff[2], [k*(g*conv(coeff[0], coeff[2], j)-coeff[4][j]) for j in range(order+1)], n),
            coeff[3][n],
            -w2*w2*coeff[2][n]-g*conv(coeff[0], [k*(g*conv(coeff[0], coeff[2], j)-coeff[4][j]) for j in range(order+1)], n),
            f_n/(2*c),
            sum((
                k*(g*conv(coeff[0], coeff[2], j)-coeff[4][j]) *
                k*(g*conv(coeff[0], coeff[2], n-j)-coeff[4][n-j])
                for j in range(n+1)), Q(0))/(2*c),
        )
        for row, value in zip(coeff, rhs_n):
            row[n+1] = value/Q(n+1)
    return coeff


def fraction_string(v):
    return str(v.numerator) if v.denominator == 1 else f"{v.numerator}/{v.denominator}"


def parameter_grid_search():
    """Finite search inside the theorem assumptions; exact edge cases are separate."""
    tested = 0
    min_work = float("inf")
    max_balance = 0.0
    for k, c, g, w1, w2, x1, x2 in product(
            (0.25, 1.0, 2.0), (0.5, 1.0, 2.0), (-2.0, -1.0, 1.0, 2.0),
            (0.0, 1.0), (0.0, 1.0), (-1.0, 1.0), (-1.0, 1.0)):
        p = (k, c, g, w1, w2)
        u = (x1, 0.0, x2, 0.0, 0.0)
        s, _ = integrate(p, u, 1000)
        row = diagnostics(s, p, u)
        assert force(tuple(u)+(0.0,), p) != 0
        assert row["emitted_work"] > 0
        assert abs(row["balance_residual"]) < 1e-8
        min_work = min(min_work, row["emitted_work"])
        max_balance = max(max_balance, abs(row["balance_residual"]))
        tested += 1
    return {"cases": tested, "assumptions": "kappa>0,c>0,g!=0,y(0)=0,x1(0)*x2(0)!=0; omega_i in {0,1}",
            "counterexamples_found": 0, "minimum_emitted_work_at_t1": min_work,
            "maximum_energy_balance_residual": max_balance,
            "meaning": "finite numerical search only; the Lean theorem proves the conditional equivalence for supplied solutions"}


def diagnostics(s, p, initial=None):
    f = force(s, p)
    e = energy(s, p)
    e0 = energy(initial_state if initial is None else initial, p)
    return {"x1": s[0], "v1": s[1], "x2": s[2], "v2": s[3],
            "y": s[4], "force": f, "local_energy": e,
            "emitted_work": s[5], "balance_residual": e+s[5]-e0}


# Main initial-value problem from the request.
parameters = (1.0, 1.0, 1.0, 0.0, 0.0)  # kappa,c,g,omega1,omega2
initial_state = (1.0, 0.0, 1.0, 0.0, 0.0)


def main():
    coarse, _ = integrate(parameters, initial_state, 100)
    medium, _ = integrate(parameters, initial_state, 200)
    refined, _ = integrate(parameters, initial_state, 400)
    fine, samples = integrate(parameters, initial_state, 20000, sample_every=2000)
    twice_fine, _ = integrate(parameters, initial_state, 40000)
    final = diagnostics(fine, parameters)
    final_twice = diagnostics(twice_fine, parameters)
    diff = {name: abs(final[name]-final_twice[name]) for name in
            ("x1", "v1", "x2", "v2", "y", "force", "local_energy", "emitted_work")}
    coarse_diagnostics = diagnostics(coarse, parameters)
    medium_diagnostics = diagnostics(medium, parameters)
    refined_diagnostics = diagnostics(refined, parameters)
    coarse_diff = {name: abs(coarse_diagnostics[name]-medium_diagnostics[name]) for name in diff}
    medium_diff = {name: abs(medium_diagnostics[name]-refined_diagnostics[name]) for name in diff}
    # Exact dyadic coefficient calculation for the chosen initial state.
    tq = tuple(map(Q, (1, 1, 1, 0, 0)))
    iq = tuple(map(Q, (1, 0, 1, 0, 0)))
    coeff = taylor_coefficients(tq, iq, order=7)
    labels = ("x1", "v1", "x2", "v2", "y", "W")
    taylor = {label: [fraction_string(a) for a in row[:6]] for label, row in zip(labels, coeff)}

    # Parameter variations that keep the theorem's positivity assumptions.
    variants = [
        {"name": "positive_coupling_and_frequencies", "p": (2.0, 0.7, -1.2, 0.5, 1.1), "u": (0.7, 0.0, -1.3, 0.0, 0.0)},
        {"name": "weaker_coupling", "p": (0.5, 2.0, 1.5, 1.0, 0.3), "u": (1.2, 0.0, 0.8, 0.0, 0.0)},
        {"name": "boundary_equilibrium_no_emission", "p": (1.0, 1.0, 1.0, 0.0, 0.0), "u": (1.0, 0.0, 1.0, 0.0, 1.0)},
        {"name": "zero_coupling_counterexample", "p": (1.0, 1.0, 0.0, 0.0, 0.0), "u": (1.0, 0.0, 1.0, 0.0, 0.0)},
        {"name": "zero_stiffness_counterexample", "p": (0.0, 1.0, 1.0, 0.0, 0.0), "u": (1.0, 0.0, 1.0, 0.0, 0.0)},
    ]
    variant_results = []
    for item in variants:
        s, _ = integrate(item["p"], item["u"], 20000)
        row = diagnostics(s, item["p"], item["u"])
        row["name"] = item["name"]
        row["initial_force"] = force(tuple(item["u"])+(0.0,), item["p"])
        row["hypotheses_kappa_positive_c_positive_g_nonzero"] = (
            item["p"][0] > 0 and item["p"][1] > 0 and item["p"][2] != 0)
        variant_results.append(row)

    output = {
        "status": "all finite numeric checks passed",
        "model": "PR #88 SolvesAt vector field with W'=F^2/(2c)",
        "parameters": {"kappa": 1, "c": 1, "g": 1, "omega1": 0, "omega2": 0},
        "initial_state": {"x1": 1, "v1": 0, "x2": 1, "v2": 0, "y": 0},
        "integrator": "classical RK4, independent implementation",
        "steps": {"coarse": 100, "medium": 200, "refined": 400, "reported_fine": 20000, "twice_fine": 40000},
        "sampled_trajectory": [dict(time=t, **diagnostics(s, parameters)) for t, s in samples],
        "t1": final,
        "step_doubling_100_to_200_difference": coarse_diff,
        "step_doubling_error_estimate_at_200_order4": {k: v/15 for k, v in coarse_diff.items()},
        "step_doubling_200_to_400_difference": medium_diff,
        "step_doubling_error_estimate_at_400_order4": {k: v/15 for k, v in medium_diff.items()},
        "refinement_difference_fine_vs_twice_fine": diff,
        "richardson_error_estimate_order4": {k: v/15 for k, v in diff.items()},
        "max_energy_balance_residual_fine": max(abs(diagnostics(s, parameters)["balance_residual"]) for _,s in samples),
        "taylor_coefficients_exact": taylor,
        "parameter_variations_and_boundary_cases": variant_results,
        "parameter_grid_search": parameter_grid_search(),
        "scope": "Local existence follows analytically from Picard-Lindelof for the polynomial vector field. Numerical agreement is not that proof; finite parameter samples do not prove the universal theorem."
    }
    assert all(isfinite(v) for v in final.values())
    assert abs(final["balance_residual"]) < 1e-10
    assert abs(final["x1"]-0.649517359) < 2e-8
    assert abs(final["y"]-0.291491797) < 2e-8
    assert abs(final["local_energy"]-0.294759577) < 2e-8
    assert abs(final["emitted_work"]-0.205240423) < 2e-8
    assert all(abs(row["balance_residual"]) < 1e-10 for row in variant_results)
    for item, row in zip(variants, variant_results):
        if item["name"] == "boundary_equilibrium_no_emission":
            assert abs(row["emitted_work"]) < 1e-14 and abs(row["force"]) < 1e-14
        if row["hypotheses_kappa_positive_c_positive_g_nonzero"] and row["initial_force"] != 0:
            assert row["emitted_work"] > 0
        if item["name"] in ("zero_coupling_counterexample", "zero_stiffness_counterexample"):
            assert abs(row["emitted_work"]) < 1e-14 and abs(row["force"]) < 1e-14
    print(json.dumps(output, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
