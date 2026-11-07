"""Numerical study of the GPT-side flow in the double-well regime (λ = 1, r = -1).

Not Lean verification. Flow (baseline IsTrajectory with constant b):
    z' = -γ (E - T) ∇E + b J ∇E,   J (gx, gy) = (-gy, gx).
Output: double_well_check.json next to this file.
"""
import json
import math
import pathlib

import numpy as np
from scipy.integrate import solve_ivp

HERE = pathlib.Path(__file__).resolve().parent
LAM, R, GAMMA = 1.0, -1.0, 1.0
S2 = math.sqrt(2.0)
A0 = math.sqrt(-R / LAM)            # well bottoms at ±A0 (u = 0)
BOTTOM = -R * R / (4 * LAM)         # -1/4


def E(x, y, u=0.0):
    return LAM * x**4 / 4 + R * x * x / 2 - u * x + (y - S2 * x) ** 2 / 2


def grad(x, y, u=0.0):
    return np.array([LAM * x**3 + (R + 2) * x - S2 * y - u, y - S2 * x])


def make_field(T, b, u=0.0):
    def fld(t, z):
        g = grad(z[0], z[1], u)
        e = E(z[0], z[1], u) - T
        return -GAMMA * e * g + b * np.array([-g[1], g[0]])
    return fld


def run(z0, T, b, u=0.0, t_end=1500.0):
    sol = solve_ivp(make_field(T, b, u), (0, t_end), z0, method="DOP853", rtol=1e-10,
                    atol=1e-12, dense_output=False, max_step=1.0)
    z = sol.y[:, -1]
    xs = sol.y[0]
    e_end = E(z[0], z[1], u) - T
    return z, e_end, xs


def classify(z, e_end):
    if abs(e_end) < 1e-6:
        return "shell+" if z[0] > 0 else "shell-"
    if np.linalg.norm(z) < 1e-3:
        return "saddle"
    if min(np.linalg.norm(z - [A0, S2 * A0]), np.linalg.norm(z + [A0, S2 * A0])) < 1e-3:
        return "bottom"
    return "unresolved"


MIRROR = {"shell+": "shell-", "shell-": "shell+", "saddle": "saddle", "bottom": "bottom",
          "unresolved": "unresolved"}
report = {"parameters": {"lambda": LAM, "r": R, "u": 0.0, "gamma": GAMMA, "a0": A0,
                         "bottom_energy": BOTTOM, "saddle_energy": 0.0}}

# (a) two shells, T in (bottom, 0): selection, symmetry, basin boundary
grid = np.linspace(-2.4, 2.4, 41)
for b in (0.0, 0.5):
    T = -0.1
    classes, viol_sign, viol_mirror, counts = {}, 0, 0, {}
    neg_start_total = 0
    for x0 in grid:
        for y0 in grid:
            z, e_end, xs = run([x0, y0], T, b)
            c = classify(z, e_end)
            classes[(round(x0, 6), round(y0, 6))] = c
            counts[c] = counts.get(c, 0) + 1
            if E(x0, y0) < 0:
                neg_start_total += 1
                if np.any(np.sign(xs) != np.sign(x0)):
                    viol_sign += 1
    for (x0, y0), c in classes.items():
        if classes[(round(-x0, 6), round(-y0, 6))] != MIRROR[c]:
            viol_mirror += 1
    # saddle linearization A = (γ T I + b J) H  (e = -T at the saddle)
    H = np.array([[R + 2, -S2], [-S2, 1.0]])
    Jm = np.array([[0.0, -1.0], [1.0, 0.0]])
    A = (GAMMA * T * np.eye(2) + b * Jm) @ H
    w, V = np.linalg.eig(A)
    vs = np.real(V[:, np.argmin(np.real(w))])
    stable_angle = math.atan2(vs[1], vs[0]) % math.pi
    # classify starts on a small circle around the saddle; locate class changes
    rho, flips = 0.05, []
    angles = np.linspace(0, 2 * math.pi, 721)[:-1]
    ring = [classify(*run([rho * math.cos(a), rho * math.sin(a)], T, b)[:2]) for a in angles]
    for i in range(len(angles)):
        if ring[i] != ring[i - 1]:
            flips.append(float(((angles[i] + angles[i - 1]) / 2) % math.pi))
    report[f"two_shells_T=-0.1_b={b}"] = {
        "grid": f"{len(grid)}x{len(grid)} on [-2.4,2.4]^2, t_end=1500",
        "counts": counts,
        "starts_with_E<0": neg_start_total,
        "sign_change_violations_for_E<0_starts": viol_sign,
        "mirror_symmetry_violations": viol_mirror,
        "saddle_eigenvalues": [complex(v).real for v in w],
        "saddle_stable_direction_angle_mod_pi": stable_angle,
        "basin_boundary_angles_mod_pi_on_circle_rho=0.05": flips,
    }

# (b) one shell, T > 0: no confinement
T = 0.3
counts, crossed, starts = {}, 0, 0
for x0 in grid[::2]:
    for y0 in grid[::2]:
        z, e_end, xs = run([x0, y0], T, 0.0)
        c = classify(z, e_end)
        counts[c] = counts.get(c, 0) + 1
        if E(x0, y0) < 0:
            starts += 1
            crossed += int(np.any(np.sign(xs) != np.sign(x0)))
report["one_shell_T=0.3_b=0"] = {"counts": counts, "starts_with_E<0": starts,
                                 "of_which_changed_sign_of_x": crossed}

# (c) T below the well bottoms: unreachable
T = -0.4
gaps, counts = [], {}
for x0 in grid[::4]:
    for y0 in grid[::4]:
        z, e_end, xs = run([x0, y0], T, 0.0)
        counts[classify(z, e_end)] = counts.get(classify(z, e_end), 0) + 1
        gaps.append(e_end)
report["below_bottom_T=-0.4_b=0"] = {"counts": counts, "min_final_gap": float(min(gaps)),
                                     "lean_lower_bound_for_gap": BOTTOM - T}


# (d) tilted double well near the Maxwell point: which wells reach T = global value + δ
def wells(u):
    roots = np.sort(np.real(np.roots([LAM, 0.0, R, -u])))  # λx³ + r x - u = 0
    f = lambda x: LAM * x**4 / 4 + R * x * x / 2 - u * x
    return roots[0], roots[1], roots[2], f


tilt = {}
for delta in (0.02, 0.005):
    rows = []
    for u in np.linspace(-0.05, 0.05, 41):
        aL, c, aR, f = wells(u)
        phi = min(f(aL), f(aR))
        T = phi + delta
        out = {}
        for name, a in (("left", aL), ("right", aR)):
            z, e_end, xs = run([a, S2 * a + 0.002], T, 0.0, u=u, t_end=600)
            ok = abs(e_end) < 1e-6
            predicted_trapped = f(a) > T  # Lean `trapped`, with barrier f(c) above T and start
            out[name] = {"bottom": float(f(a)), "reached": bool(ok), "final_gap": float(e_end),
                         "lean_predicts_trapped": bool(predicted_trapped),
                         "stayed_in_well": bool(np.all((xs < c) if name == "left" else (xs > c)))}
        rows.append({"u": float(u), "T": float(T), "barrier": float(f(c)), **out})
    both = [r["u"] for r in rows if r["left"]["reached"] and r["right"]["reached"]]
    # Lean (`trapped`) proves only: bottom > T  =>  never reached.
    lean_part_ok = all(not r[s]["reached"] for r in rows for s in ("left", "right")
                       if r[s]["lean_predicts_trapped"])
    # Numerical-only claim: bottom < T  =>  reached.  List the exceptions with their margins.
    unconverged = [{"u": r["u"], "well": s, "bottom_minus_T": r[s]["bottom"] - r["T"],
                    "final_gap": r[s]["final_gap"]}
                   for r in rows for s in ("left", "right")
                   if not r[s]["lean_predicts_trapped"] and not r[s]["reached"]]
    # analytic window: |f(aL) - f(aR)| < δ
    def gap(u):
        aL, c, aR, f = wells(u)
        return abs(f(aL) - f(aR))
    us = np.linspace(0, 0.05, 50001)
    half = float(us[np.argmax([gap(v) >= delta for v in us])])
    tilt[f"delta={delta}"] = {
        "both_wells_reach_target_for_u_in": [min(both), max(both)] if both else None,
        "analytic_half_width_|f(aL)-f(aR)|<delta": half,
        "first_order_estimate_delta/(2 a0)": delta / (2 * A0),
        "lean_trapped_cases_all_unreached": lean_part_ok,
        "predicted_reachable_but_unconverged_at_t=600": unconverged,
        "all_trajectories_stayed_in_their_well": all(r[s]["stayed_in_well"]
                                                     for r in rows for s in ("left", "right")),
        "rows": rows,
    }
report["tilted_wells_near_maxwell"] = tilt
(HERE / "double_well_check.json").write_text(json.dumps(report, indent=1) + "\n", encoding="utf-8")
summary = {k: v for k, v in report.items() if k != "tilted_wells_near_maxwell"}
summary["tilted"] = {k: {kk: vv for kk, vv in v.items() if kk != "rows"} for k, v in tilt.items()}
print(json.dumps(summary, indent=1))
