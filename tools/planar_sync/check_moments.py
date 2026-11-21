#!/usr/bin/env python3
"""Verify an observable reduction for two interacting planar point meshes.

Model (columns are corresponding observed points, not unlabelled outlines):
    X_next = A @ ((1-alpha) * X + alpha * Y) + U
    Y_next = A @ (alpha * X + (1-alpha) * Y) + U

Here A is a known common 2x2 linear map; U can be any common, point-specific
displacement.  With beta = 1-2*alpha and N corresponding points,
    D = X-Y, S = D @ D.T / N, E = trace(S),
the proposed exact observable update is
    S_next = beta**2 * A @ S @ A.T.

The program compares directly updated point meshes against this reduction,
checks rational identities exactly, and gives explicit counterexamples to
stronger reductions.  It does not validate a law of celestial or quantum
physics.  Only the Python standard library and NumPy are required.

Run:
    python tools/planar_sync/check_moments.py
    python tools/planar_sync/check_moments.py --output-dir /some/output/directory
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
from fractions import Fraction as F
from itertools import product
import json
from pathlib import Path
import platform
import random
import sys
from typing import Any, Callable

import numpy as np


Matrix = list[list[F]]


def require(condition: bool, explanation: str) -> None:
    if not condition:
        raise AssertionError(explanation)


def add(a: Matrix, b: Matrix) -> Matrix:
    return [[x + y for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def scale(k: F, a: Matrix) -> Matrix:
    return [[k * x for x in row] for row in a]


def subtract(a: Matrix, b: Matrix) -> Matrix:
    return add(a, scale(F(-1), b))


def transpose(a: Matrix) -> Matrix:
    return [list(row) for row in zip(*a)]


def multiply(a: Matrix, b: Matrix) -> Matrix:
    bt = transpose(b)
    return [[sum((x * y for x, y in zip(ar, bc)), F(0))
             for bc in bt] for ar in a]


def direct_mesh_step(
    x: Matrix, y: Matrix, a: Matrix, u: Matrix, alpha: F
) -> tuple[Matrix, Matrix]:
    """Compute each complete mesh before measuring its difference."""
    x_mixed = add(scale(1 - alpha, x), scale(alpha, y))
    y_mixed = add(scale(alpha, x), scale(1 - alpha, y))
    return add(multiply(a, x_mixed), u), add(multiply(a, y_mixed), u)


def discrepancy_moment(x: Matrix, y: Matrix) -> Matrix:
    d = subtract(x, y)
    n = len(d[0])
    return scale(F(1, n), multiply(d, transpose(d)))


def reduced_moment_step(s: Matrix, a: Matrix, alpha: F) -> Matrix:
    return scale((1 - 2 * alpha) ** 2, multiply(multiply(a, s), transpose(a)))


def trace(s: Matrix) -> F:
    return s[0][0] + s[1][1]


def strings(a: Matrix) -> list[list[str]]:
    return [[str(x) for x in row] for row in a]


def exact_exhaustive_check() -> dict[str, Any]:
    points = list(product((-1, 0, 1), repeat=2))
    alphas = (F(0), F(1, 4), F(1, 2), F(3, 4), F(1))
    maps = {
        "identity": [[F(1), F(0)], [F(0), F(1)]],
        "anisotropic": [[F(2), F(0)], [F(0), F(1, 2)]],
        "shear": [[F(1), F(1)], [F(0), F(1)]],
        "rank_one_projection": [[F(1), F(0)], [F(0), F(0)]],
    }
    count = 0
    counts_by_map = {key: 0 for key in maps}
    for xp, yp, up, alpha, map_name in product(
        points, points, points, alphas, maps
    ):
        x = [[F(xp[0])], [F(xp[1])]]
        y = [[F(yp[0])], [F(yp[1])]]
        u = [[F(up[0])], [F(up[1])]]
        a = maps[map_name]
        xn, yn = direct_mesh_step(x, y, a, u, alpha)
        s_direct = discrepancy_moment(xn, yn)
        s_reduced = reduced_moment_step(discrepancy_moment(x, y), a, alpha)
        require(s_direct == s_reduced, f"Moment identity failed in case {count}")
        d_reduced = scale(1 - 2 * alpha, multiply(a, subtract(x, y)))
        require(subtract(xn, yn) == d_reduced,
                f"Difference identity failed in case {count}")
        require(trace(s_direct) == trace(s_reduced),
                f"Trace identity failed in case {count}")
        count += 1
        counts_by_map[map_name] += 1
    require(count == 14580, "Unexpected exhaustive case count")
    return {
        "status": "passed", "arithmetic": "exact Fraction",
        "cases": count, "points_per_mesh": 1,
        "point_coordinate_values": [-1, 0, 1],
        "alphas": [str(x) for x in alphas],
        "counts_by_map": counts_by_map,
        "max_absolute_error": "0",
        "claims_checked": ["D_next = beta A D", "S_next = beta^2 A S A^T",
                           "E_next = trace(S_next)"],
    }


def exact_multi_point_check() -> dict[str, Any]:
    rng = random.Random(20261122)
    counts = {2: 0, 3: 0, 7: 0}
    alphas = (F(0), F(1, 4), F(1, 2), F(3, 4), F(1))

    def rational() -> F:
        return F(rng.randint(-4, 4), rng.randint(1, 7))

    for n in counts:
        for case_index in range(32):
            x = [[rational() for _ in range(n)] for _ in range(2)]
            y = [[rational() for _ in range(n)] for _ in range(2)]
            u = [[rational() for _ in range(n)] for _ in range(2)]
            a = [[rational() for _ in range(2)] for _ in range(2)]
            alpha = alphas[case_index % len(alphas)]
            xn, yn = direct_mesh_step(x, y, a, u, alpha)
            direct = discrepancy_moment(xn, yn)
            reduced = reduced_moment_step(discrepancy_moment(x, y), a, alpha)
            require(direct == reduced, f"N={n}, case={case_index} failed")
            require(trace(direct) == trace(reduced), "Multi-point trace failed")
            counts[n] += 1
    return {
        "status": "passed", "arithmetic": "exact Fraction",
        "cases": sum(counts.values()),
        "counts_by_mesh_size": {str(n): c for n, c in counts.items()},
        "random_seed": 20261122,
        "max_absolute_error": "0",
        "notes": "Arbitrary rational common linear maps and point-specific common displacements.",
    }


def numerical_simulation() -> dict[str, Any]:
    grid = np.linspace(-1.0, 1.0, 21)
    gu, gv = np.meshgrid(grid, grid, indexing="xy")
    u0, v0 = gu.ravel(), gv.ravel()
    n = len(u0)
    x = np.vstack((u0 + 0.05 * np.sin(np.pi * v0),
                   v0 + 0.08 * np.cos(np.pi * u0)))
    y = np.vstack((0.85 * u0 + 0.12 * np.cos(np.pi * v0),
                   1.12 * v0 - 0.06 * np.sin(np.pi * u0)))
    alpha = 2.0 / 25.0
    beta = 1.0 - 2.0 * alpha
    steps = 80
    collapse_step = 31
    d0 = x - y
    s_reduced = d0 @ d0.T / n
    max_s_error = 0.0
    max_e_error = 0.0
    max_e_relative_error = 0.0
    trajectory: list[dict[str, Any]] = []
    snapshots: list[dict[str, Any]] = []
    snapshot_steps = {0, 1, collapse_step, collapse_step + 1, steps}

    def geometric_rank(points: np.ndarray) -> int:
        return int(np.linalg.matrix_rank(
            points - points.mean(axis=1, keepdims=True), tol=1e-10
        ))

    def record(step: int, a: np.ndarray | None) -> None:
        nonlocal max_s_error, max_e_error, max_e_relative_error
        d = x - y
        s_direct = d @ d.T / n
        e_direct = float(np.mean(np.sum(d * d, axis=0)))
        e_reduced = float(np.trace(s_reduced))
        s_error = float(np.max(np.abs(s_direct - s_reduced)))
        e_error = abs(e_direct - e_reduced)
        max_s_error = max(max_s_error, s_error)
        max_e_error = max(max_e_error, e_error)
        if e_direct > 1e-25:
            max_e_relative_error = max(max_e_relative_error, e_error / e_direct)
        ranks = [geometric_rank(x), geometric_rank(y)]
        trajectory.append({
            "step": step,
            "A_used": None if a is None else a.tolist(),
            "S_direct": s_direct.tolist(),
            "S_reduced": s_reduced.tolist(),
            "E_direct": e_direct,
            "E_reduced": e_reduced,
            "max_S_absolute_error": s_error,
            "E_absolute_error": e_error,
            "geometric_ranks": ranks,
        })
        if step in snapshot_steps:
            snapshots.append({
                "step": step, "X_points": x.T.tolist(), "Y_points": y.T.tolist(),
                "geometric_ranks": ranks,
            })

    record(0, None)
    for step in range(1, steps + 1):
        a = np.array([
            [1.0 + 0.025 * np.cos(0.37 * step), 0.06 * np.sin(0.23 * step)],
            [0.04 * np.cos(0.31 * step), 1.0 - 0.02 * np.sin(0.19 * step)],
        ])
        common = np.vstack((
            0.012 * np.sin(2 * np.pi * u0 + 0.31 * step) * np.cos(np.pi * v0)
            + 0.004 * v0**2 * np.sin(0.13 * step),
            0.010 * np.cos(2 * np.pi * v0 - 0.21 * step) * np.sin(np.pi * u0)
            + 0.003 * u0**2 * np.cos(0.17 * step),
        ))
        if step == collapse_step:
            a = np.array([[1.0, 0.2], [0.0, 0.0]])
            common[1, :] = 0.0
        x_next = a @ ((1.0 - alpha) * x + alpha * y) + common
        y_next = a @ (alpha * x + (1.0 - alpha) * y) + common
        s_reduced = beta**2 * (a @ s_reduced @ a.T)
        x, y = x_next, y_next
        record(step, a)

    tolerance = 1e-11
    require(max_s_error < tolerance, "Reduced S disagrees with directly updated meshes")
    require(max_e_error < tolerance, "Reduced E disagrees with directly updated meshes")
    collapsed = trajectory[collapse_step]
    reopened = trajectory[collapse_step + 1]
    require(collapsed["geometric_ranks"] == [1, 1], "Expected two line-shaped meshes")
    require(collapsed["E_direct"] > 1e-12, "Collapse should not imply synchronization")
    require(reopened["geometric_ranks"] == [2, 2], "Common deformation should reopen the meshes")
    return {
        "status": "passed", "arithmetic": "NumPy float64",
        "points_per_mesh": n, "direct_coordinate_count": 4 * n,
        "reduced_dynamic_number_count": 3,
        "known_inputs": ["alpha", "A at each step"],
        "eliminated_inputs": ["common point-specific displacement U"],
        "alpha": alpha, "alpha_exact": "2/25", "beta": beta,
        "updates": steps, "recorded_states": steps + 1,
        "rank_one_map_step": collapse_step,
        "max_S_absolute_error": max_s_error,
        "max_E_absolute_error": max_e_error,
        "max_E_relative_error_where_E_above_1e_minus_25": max_e_relative_error,
        "absolute_tolerance": tolerance,
        "E_at_line_collapse": collapsed["E_direct"],
        "reopened_next_step": True,
        "trajectory": trajectory,
        "shape_snapshots": snapshots,
    }


def scalar_energy_counterexample() -> dict[str, Any]:
    a = [[F(2), F(0)], [F(0), F(1, 2)]]
    alpha = F(1, 4)
    zero = [[F(0)], [F(0)]]
    ds = ([[F(1)], [F(0)]], [[F(0)], [F(1)]])
    before, after = [], []
    for d in ds:
        before.append(trace(discrepancy_moment(d, zero)))
        xn, yn = direct_mesh_step(d, zero, a, zero, alpha)
        after.append(trace(discrepancy_moment(xn, yn)))
    require(before == [F(1), F(1)], "Counterexample must begin with equal E")
    require(after == [F(1), F(1, 16)], "Unexpected anisotropic counterexample values")
    return {
        "status": "passed", "A": strings(a), "alpha": str(alpha),
        "D_columns": [strings(d) for d in ds],
        "E_before": [str(e) for e in before],
        "E_after": [str(e) for e in after],
        "conclusion": "E alone is not an exact state for arbitrary known common linear maps.",
    }


def cross_moment_counterexample() -> dict[str, Any]:
    a = [[F(1), F(1)], [F(0), F(1)]]
    alpha = F(1, 4)
    zero = [[F(0)], [F(0)]]
    ds = ([[F(1)], [F(1)]], [[F(1)], [F(-1)]])
    moments = [discrepancy_moment(d, zero) for d in ds]
    after = []
    for d in ds:
        xn, yn = direct_mesh_step(d, zero, a, zero, alpha)
        after.append(trace(discrepancy_moment(xn, yn)))
    require([s[0][0] for s in moments] == [F(1), F(1)], "Sxx should be equal")
    require([s[1][1] for s in moments] == [F(1), F(1)], "Syy should be equal")
    require(after == [F(5, 4), F(1, 4)], "Unexpected shear counterexample values")
    return {
        "status": "passed", "A": strings(a), "alpha": str(alpha),
        "S_before": [strings(s) for s in moments],
        "E_after": [str(e) for e in after],
        "conclusion": "Keeping Sxx and Syy but discarding Sxy is insufficient under shear.",
    }


def logistic_bound_check() -> dict[str, Any]:
    alpha = F(9, 20)
    beta = 1 - 2 * alpha
    lipschitz = F(4)
    bound = abs(beta) * lipschitz
    maximum_ratio = F(0)
    maximum_energy_ratio = F(0)
    checked = 0
    nonzero_pairs = 0

    def logistic(z: F) -> F:
        return 4 * z * (1 - z)

    for i, j in product(range(101), repeat=2):
        x, y = F(i, 100), F(j, 100)
        fx, fy = logistic(x), logistic(y)
        xn = (1 - alpha) * fx + alpha * fy
        yn = alpha * fx + (1 - alpha) * fy
        require(0 <= xn <= 1 and 0 <= yn <= 1, "Coupled logistic map left [0,1]")
        require(abs(xn - yn) <= bound * abs(x - y), "Nonlinear contraction bound failed")
        require((xn - yn)**2 <= bound**2 * (x - y)**2, "Energy bound failed")
        if x != y:
            ratio = abs((xn - yn) / (x - y))
            maximum_ratio = max(maximum_ratio, ratio)
            maximum_energy_ratio = max(maximum_energy_ratio, ratio**2)
            nonzero_pairs += 1
        checked += 1
    require(checked == 10201, "Unexpected nonlinear grid count")
    require(maximum_ratio == F(99, 250), "Unexpected grid maximum")

    # Equal initial squared difference does not provide an exact recurrence.
    pairs = ((F(0), F(1, 10)), (F(9, 20), F(11, 20)))
    initial_energies = [(x - y)**2 for x, y in pairs]
    next_energies = [(beta * (logistic(x) - logistic(y)))**2 for x, y in pairs]
    require(initial_energies[0] == initial_energies[1], "Initial energies should agree")
    require(next_energies[0] != next_energies[1], "Nonlinear E should not close exactly")
    return {
        "status": "passed", "arithmetic": "exact Fraction",
        "model": "x_next=(1-alpha)*f(x)+alpha*f(y), y_next=alpha*f(x)+(1-alpha)*f(y)",
        "f": "4*x*(1-x)", "domain": "[0,1]^2", "alpha": str(alpha),
        "lipschitz_bound": str(lipschitz),
        "difference_contraction_bound": str(bound),
        "energy_contraction_bound": str(bound**2),
        "grid": "{0,1/100,...,1} squared", "cases": checked,
        "nonzero_difference_cases": nonzero_pairs,
        "maximum_grid_difference_ratio": str(maximum_ratio),
        "maximum_grid_energy_ratio": str(maximum_energy_ratio),
        "continuum_justification": "f(x)-f(y)=4*(x-y)*(1-x-y); abs(1-x-y)<=1 on [0,1]^2.",
        "exact_closure_counterexample": {
            "pairs": [[str(x), str(y)] for x, y in pairs],
            "E_before": [str(e) for e in initial_energies],
            "E_after": [str(e) for e in next_energies],
        },
        "scope": "A verified upper bound, not an exact scalar recurrence for the nonlinear model.",
    }


def observation_closure_check() -> dict[str, Any]:
    transition = (1, 2, 0)
    observation = ("line", "line", "sheet")
    require(observation[0] == observation[1], "Observations should agree")
    next_observations = (observation[transition[0]], observation[transition[1]])
    require(next_observations == ("line", "sheet"), "Different futures were expected")
    two_state_cases = 0
    for t, q in product(product(range(2), repeat=2), repeat=2):
        for i, j in product(range(2), repeat=2):
            require(q[i] != q[j] or q[t[i]] == q[t[j]],
                    "A two-state counterexample should not exist")
        two_state_cases += 1
    require(two_state_cases == 16, "Unexpected two-state exhaustion count")
    widths = (0, 1, 2, 1)
    signatures = [tuple(widths[(state + k) % 4] for k in range(4))
                  for state in range(4)]
    require(len(set(signatures)) == 4, "All four predictive states should be distinct")
    return {
        "status": "passed", "three_state_transition": ["B", "C", "A"],
        "three_state_observations": list(observation),
        "same_observation_states": ["A", "B"],
        "their_next_observations": list(next_observations),
        "two_state_models_exhausted": two_state_cases,
        "minimality_scope": "Deterministic state updates, state-based observations, at least one distinct next observation.",
        "four_phase_widths": list(widths),
        "four_phase_future_signatures": [list(s) for s in signatures],
        "four_phase_same_width_states": [1, 3],
        "their_next_widths": [2, 0],
        "conclusion": "A current image can omit a predictive distinction; the branch or adequate history must be retained.",
    }


def polygon_area(points: Matrix) -> F:
    n = len(points[0])
    doubled = sum((points[0][i] * points[1][(i + 1) % n]
                   - points[1][i] * points[0][(i + 1) % n]
                   for i in range(n)), F(0))
    return abs(doubled) / 2


def area_and_scalar_special_case() -> dict[str, Any]:
    x = [[F(-1), F(1), F(1), F(-1)], [F(-1), F(-1), F(1), F(1)]]
    y = [[F(-2), F(2), F(2), F(-2)], [F(-1), F(-1), F(1), F(1)]]
    zero = [[F(0)] * 4, [F(0)] * 4]
    projection = [[F(1), F(0)], [F(0), F(0)]]
    alpha = F(1, 4)
    xn, yn = direct_mesh_step(x, y, projection, zero, alpha)
    s = discrepancy_moment(xn, yn)
    require(polygon_area(xn) == polygon_area(yn) == 0,
            "Both shapes should have zero area")
    require(s == [[F(1, 4), F(0)], [F(0), F(0)]], "Expected nonzero rank-one discrepancy")
    require(trace(s) == F(1, 4), "Zero area should not imply zero discrepancy")

    scalar_x, scalar_y = F(2), F(1)
    scalar_trace = []
    for step in range(11):
        d = scalar_x - scalar_y
        e = d**2
        require(d == F(1, 2**step), "Incorrect scalar difference recurrence")
        require(e == F(1, 4**step), "Incorrect scalar energy recurrence")
        scalar_trace.append({"step": step, "a": str(scalar_x), "b": str(scalar_y),
                             "difference": str(d), "E": str(e)})
        scalar_x, scalar_y = ((1 - alpha) * scalar_x + alpha * scalar_y,
                             alpha * scalar_x + (1 - alpha) * scalar_y)
    require(F(scalar_trace[-1]["difference"]) < F(1, 1000), "Ten-step tolerance not reached")
    return {
        "status": "passed", "arithmetic": "exact Fraction",
        "area_counterexample": {
            "areas_before": [str(polygon_area(x)), str(polygon_area(y))],
            "areas_after": [str(polygon_area(xn)), str(polygon_area(yn))],
            "S_after": strings(s), "E_after": str(trace(s)),
            "conclusion": "Two zero-area, line-shaped meshes can remain unsynchronized.",
        },
        "scalar_identity_case": {
            "alpha": "1/4", "common_linear_map": "identity",
            "initial_width_parameters": ["2", "1"],
            "difference_formula": "2^(-step)", "energy_formula": "4^(-step)",
            "trajectory": scalar_trace,
            "finite_exact_lock": False,
            "note": "For nonzero initial discrepancy and alpha=1/4, equality is asymptotic; alpha=1/2 gives exact equality in one step.",
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=Path(__file__).resolve().parents[2] / "verification" / "planar-sync")
    args = parser.parse_args()
    checks: list[tuple[str, Callable[[], dict[str, Any]]]] = [
        ("exact_single_point_exhaustion", exact_exhaustive_check),
        ("exact_multiple_points", exact_multi_point_check),
        ("direct_vs_reduced_441_points", numerical_simulation),
        ("energy_alone_counterexample", scalar_energy_counterexample),
        ("cross_moment_counterexample", cross_moment_counterexample),
        ("nonlinear_logistic_bound", logistic_bound_check),
        ("observation_closure_counterexample", observation_closure_check),
        ("area_and_scalar_special_case", area_and_scalar_special_case),
    ]
    results: dict[str, Any] = {}
    for name, check in checks:
        try:
            results[name] = check()
        except Exception as exc:  # Preserve other independent checks in a failed run.
            results[name] = {"status": "failed", "error": f"{type(exc).__name__}: {exc}"}
        print(f"{name}: {results[name]['status']}", flush=True)
    success = all(result["status"] == "passed" for result in results.values())
    report = {
        "title": "Observable synchronization under common planar deformation",
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "overall_status": "passed" if success else "failed",
        "checks_passed": sum(r["status"] == "passed" for r in results.values()),
        "checks_total": len(results),
        "runtime": {"python": platform.python_version(), "numpy": np.__version__},
        "model": {
            "full_update": ["X_next=A*((1-alpha)*X+alpha*Y)+U",
                            "Y_next=A*(alpha*X+(1-alpha)*Y)+U"],
            "observable": "S=(X-Y)*(X-Y)^T/N; E=trace(S)",
            "exact_reduction": "S_next=(1-2*alpha)^2*A*S*A^T",
            "independent_reduced_numbers": ["Sxx", "Sxy", "Syy"],
        },
        "limitations": [
            "This verifies constructed mathematical models, not celestial or quantum measurements.",
            "Corresponding observed points must be specified; an unlabelled outline is insufficient in general.",
            "A and alpha must be known inputs or have their own closed update; their computation is not eliminated.",
            "A common point-specific displacement U cancels only because it is identical for both meshes.",
            "Three numbers predict discrepancy moments, not the complete future images.",
            "E alone need not close under anisotropic common maps, and even Sxx and Syy omit needed cross information under shear.",
            "Projection can erase distinctions. E=0 establishes equality of the retained observed points, not equality of all hidden states.",
            "The nonlinear extension proves a contraction bound, not an exact recurrence for E.",
            "Numerical agreement is supplementary; exact identity checks and an algebraic proof establish the reduction.",
            "The dimension count is not a benchmark or a proof of globally minimal encoding size.",
        ],
        "results": results,
    }
    args.output_dir.mkdir(parents=True, exist_ok=True)
    output_path = args.output_dir / "verification-results.json"
    output_path.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"overall_status: {report['overall_status']}")
    print(f"report: {output_path}")
    return 0 if success else 1


if __name__ == "__main__":
    sys.exit(main())
