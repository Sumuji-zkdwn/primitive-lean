"""Re-run exact coefficient checks and independent numerical/CLI checks.

Python standard library is sufficient. NumPy is an optional independent root
oracle; its actual version and whether it ran are recorded. These checks are
not Lean proofs and do not certify floating-point interval endpoints.
"""

from __future__ import annotations

from datetime import datetime, timezone
from fractions import Fraction as F
import itertools
import json
import math
from pathlib import Path
import random
import subprocess
import sys

import linear_input as tool


class P:
    """Small exact sparse polynomial, used only as an independent identity check."""
    def __init__(self, value):
        if isinstance(value, dict):
            self.terms = {k: F(v) for k, v in value.items() if v}
        elif isinstance(value, str):
            self.terms = {(value,): F(1)}
        else:
            self.terms = {(): F(value)} if value else {}

    def __add__(self, other):
        other = other if isinstance(other, P) else P(other)
        result = self.terms.copy()
        for k, v in other.terms.items():
            result[k] = result.get(k, F(0)) + v
        return P(result)

    __radd__ = __add__

    def __neg__(self):
        return P({k: -v for k, v in self.terms.items()})

    def __sub__(self, other):
        return self + -(other if isinstance(other, P) else P(other))

    def __rsub__(self, other):
        return -self + other

    def __mul__(self, other):
        other = other if isinstance(other, P) else P(other)
        result = {}
        for ka, va in self.terms.items():
            for kb, vb in other.terms.items():
                key = tuple(sorted(ka+kb))
                result[key] = result.get(key, F(0)) + va*vb
        return P(result)

    __rmul__ = __mul__

    def __pow__(self, degree):
        result = P(1)
        for _ in range(degree):
            result = result*self
        return result


def close(actual, expected, tol=2e-12):
    assert math.isclose(actual, expected, rel_tol=tol, abs_tol=tol), (actual, expected)


def exact_identities():
    lam, r, x, t, u1, u2, E0, Y, U = map(P, ("lam", "r", "x", "t", "u1", "u2", "E0", "Y", "U"))
    input_at_x = lam*x**3+r*x
    fx = lam*x**4*F(1, 4)+r*x**2*F(1, 2)-input_at_x*x
    ft = lam*t**4*F(1, 4)+r*t**2*F(1, 2)-input_at_x*t
    transformed_input = U+lam*x**3*F(1, 4)+r*x*F(1, 2)
    identities = {
        "inverse_design_global_certificate": ft-fx-(t-x)**2*(lam*(t+x)**2*F(1, 4)+(lam*x**2+r)*F(1, 2)),
        "critical_energy_identity": fx-(-3*lam*x**4*F(1, 4)-r*x**2*F(1, 2)),
        "critical_energy_bound_completed_square": 12*lam*fx-(r**2-(3*lam*x**2+r)**2),
        "two_input_state_recovery": ((E0-u1*x)-(E0-u2*x))-(u2-u1)*x,
        "two_input_zero_energy_recovery": u2*(E0-u1*x)-u1*(E0-u2*x)-(u2-u1)*E0,
        "polynomial_coordinate_identity": lam*x**4*F(1, 4)+r*x**2*F(1, 2)+Y**2*F(1, 2)-transformed_input*x-(Y**2*F(1, 2)-x*U),
    }
    for name, polynomial in identities.items():
        assert not polynomial.terms, (name, polynomial.terms)
    return list(identities)


def exact_counterexample():
    x, u = -F(2, 3), F(10, 27)
    assert x**3-x-u == 0
    e = x**4/4-x**2/2-u*x
    assert e == F(2, 27) > F(1, 27) > 0
    return {"x": str(x), "u": str(u), "critical_energy": str(e), "target": "1/27"}


def known_roots_and_folds():
    cases = [
        (1, -1, 0, [-1, 0, 1], ["local_minimum", "saddle", "local_minimum"]),
        (1, -3, 2, [-1, 2], ["degenerate_fold", "local_minimum"]),
        (4, -3, 1, [-0.5, 1], ["degenerate_fold", "local_minimum"]),
        (1, 0, 0, [0], ["quartic_minimum"]),
        (2, 3, 0, [0], ["local_minimum"]),
        (1, 0, 8, [2], ["local_minimum"]),
    ]
    for lam, r, u, roots, types in cases:
        points = tool.critical_points(lam, r, u)
        assert len(points) == len(roots)
        for point, root, kind in zip(points, roots, types):
            close(point["x"], root)
            assert point["type"] == kind
    # Adjacent representable inputs must not be merged into a fold.
    for u, count in ((math.nextafter(2.0, 0.0), 3), (2.0, 2), (math.nextafter(2.0, math.inf), 1)):
        points = tool.critical_points(1, -3, u)
        assert len(points) == count, (u, points)
    # Zero input must preserve the central root even for widely different scales.
    for lam, r in ((1e-12, -1e12), (1e12, -1e-12), (1e-100, -1e100)):
        roots = tool.critical_points(lam, r, 0)
        assert len(roots) == 3 and roots[1]["x"] == 0
        close(roots[2]["x"], math.sqrt(-r/lam), 1e-12)
    return len(cases)+3+3


def recovery_and_bounds():
    tested = 0
    for x, base, u1, u2 in itertools.product((-2.5, 0, 1.25), (-0.25, 3.0), (-1.0, 0.0), (0.5, 2.0)):
        recovered = tool.recover(u1, base-u1*x, u2, base-u2*x)
        close(recovered["x"], x)
        close(recovered["energy_at_zero_input"], base)
        for noise1, noise2 in itertools.product((-0.01, 0.01), (-0.02, 0.02)):
            result = tool.recover(u1, base-u1*x+noise1, u2, base-u2*x+noise2, 0.01, 0.02)
            assert abs(result["x"]-x) <= result["absolute_x_error_bound"]+1e-12
            assert abs(result["energy_at_zero_input"]-base) <= result["absolute_zero_energy_error_bound"]+1e-12
            tested += 1
    return tested


def design_and_coordinates():
    cases = [
        (1, -1, 1.2, "unique_global_minimum"),
        (1, -1, 1, "two_tied_global_minima"),
        (1, -1, -1, "two_tied_global_minima"),
        (1, -1, 0.8, "not_a_global_minimum_for_any_input"),
        (1, -1, 0, "not_a_global_minimum_for_any_input"),
        (1, 0, 0, "unique_global_minimum"),
        (2, 3, -0.8, "unique_global_minimum"),
    ]
    for lam, r, x, status in cases:
        result = tool.design(lam, r, x)
        assert result["global_status"] == status
        close(result["required_input"], lam*x**3+r*x)
        analyzed = tool.analyze(lam, r, result["required_input"])
        nearest = min(analyzed["critical_points"], key=lambda p: abs(p["x"]-x))
        close(nearest["x"], x)
        assert nearest["global_minimum"] == (status != "not_a_global_minimum_for_any_input")
    for lam, r, x, y, u in ((1, -1, 1, 0, 0.2), (2, 3, -0.5, 4, -2), (0.25, 0, 2, -1, 3)):
        result = tool.coordinates(lam, r, x, y, u)
        close(result["energy_original"], tool.energy(lam, r, x, y, u))
        close(result["energy_original"], result["energy_quadratic"])
        for key, expected in (("x", x), ("y", y), ("u", u)):
            close(result["inverse"][key], expected)
    return len(cases)+3


def energy_bands():
    safe = tool.analyze(1, -1, 0.7, target=0.1, upper=1)
    assert safe["target_band"]["analytic_uniform_no_critical_points"]
    assert safe["target_band"]["numerical_no_critical_points"]
    unsafe = tool.analyze(1, -1, 10/27, target=1/27, upper=0.2)
    assert not unsafe["target_band"]["analytic_uniform_no_critical_points"]
    assert not unsafe["target_band"]["numerical_no_critical_points"]
    boundary = tool.analyze(1, -3, 2, target=0.75, upper=1)
    assert not boundary["target_band"]["analytic_uniform_no_critical_points"]
    assert not boundary["target_band"]["numerical_no_critical_points"]
    for r in (0, 2):
        result = tool.analyze(1, r, 3, target=0.01)
        assert result["uniform_critical_energy_upper_bound"] == 0
        assert result["target_band"]["analytic_uniform_no_critical_points"]
    return 5


def independent_numpy():
    try:
        import numpy as np
    except ImportError:
        return {"ran": False, "reason": "NumPy not installed; optional oracle skipped"}
    rng = random.Random(20261020)
    count = 0
    for _ in range(100):
        lam, r, u = 10**rng.uniform(-2, 2), rng.uniform(-5, 5), rng.uniform(-10, 10)
        expected = sorted(float(z.real) for z in np.roots([lam, 0, r, -u]) if abs(z.imag) < 1e-8)
        actual = tool.analyze(lam, r, u)
        points = actual["critical_points"]
        assert len(expected) == len(points), (lam, r, u, expected, points)
        for point, x in zip(points, expected):
            close(point["x"], x, 2e-9)
        # Global status is checked against independent root energies and a grid.
        reference_energies = [lam*x**4/4+r*x**2/2-u*x for x in expected]
        close(actual["global_minimum_energy"], min(reference_energies), 2e-9)
        xbest = actual["global_minimizers"][0]
        for t in np.linspace(-max(2, 2*abs(xbest)), max(2, 2*abs(xbest)), 101):
            grid_energy = lam*t**4/4+r*t**2/2-u*t
            assert grid_energy >= actual["global_minimum_energy"]-1e-9
        count += 1
    return {"ran": True, "version": np.__version__, "parameter_cases": count, "grid_points_per_case": 101}


def rejection_and_cli():
    invalid = [
        lambda: tool.analyze(lam=0), lambda: tool.analyze(lam=-1),
        lambda: tool.analyze(u=math.nan), lambda: tool.analyze(r=math.inf),
        lambda: tool.analyze(target=1, upper=1), lambda: tool.analyze(upper=1),
        lambda: tool.recover(0, 1, 0, 2),
        lambda: tool.recover(0, 1, 1, 2, error1=-1),
        lambda: tool.coordinates(1, -1, math.inf, 0, 0),
        lambda: tool.design(x=math.nan),
    ]
    for action in invalid:
        try:
            action()
        except ValueError:
            pass
        else:
            raise AssertionError("invalid input was accepted")
    script = str(Path(tool.__file__).resolve())
    commands = [
        ["analyze", "--target", "0.1", "--upper", "1"],
        ["recover", "--u1", "0", "--energy1", "-0.25", "--u2", "0.1", "--energy2", "-0.35"],
        ["coordinates", "--x", "1", "--y", "0", "--u", "0.2"],
        ["design", "--x", "1.2"], ["demo"],
    ]
    for command in commands:
        completed = subprocess.run([sys.executable, script, *command], text=True, encoding="utf-8", capture_output=True)
        assert completed.returncode == 0, completed.stderr
        result = json.loads(completed.stdout, parse_constant=lambda text: (_ for _ in ()).throw(ValueError(text)))
        assert isinstance(result, dict)
    rejected = subprocess.run([sys.executable, script, "analyze", "--lam", "0"], text=True, encoding="utf-8", capture_output=True)
    assert rejected.returncode == 2 and "error" in json.loads(rejected.stderr)
    return {"invalid_api_inputs": len(invalid), "successful_cli_commands": len(commands), "invalid_cli_inputs": 1}


def main():
    report = {
        "passed": False,
        "timestamp_utc": datetime.now(timezone.utc).isoformat(),
        "python": sys.version.split()[0],
        "exact_polynomial_coefficient_checks": exact_identities(),
        "exact_rational_counterexample": exact_counterexample(),
        "known_roots_fold_and_scale_cases": known_roots_and_folds(),
        "measurement_error_corner_cases": recovery_and_bounds(),
        "design_and_coordinate_cases": design_and_coordinates(),
        "energy_band_cases": energy_bands(),
        "independent_numpy_oracle": independent_numpy(),
        "input_and_cli_checks": rejection_and_cli(),
        "scope": "Exact rational coefficient identities and one rational counterexample; numerical root/type/design/error checks and CLI checks. Not Lean proofs, no ODE integration, no interval-certified root bounds.",
    }
    report["passed"] = True
    destination = Path(__file__).resolve().parent
    (destination/"checks.json").write_text(json.dumps(report, ensure_ascii=False, indent=2, allow_nan=False)+"\n", encoding="utf-8")
    (destination/"demo.json").write_text(json.dumps(tool.demo(), ensure_ascii=False, indent=2, allow_nan=False)+"\n", encoding="utf-8")
    print(json.dumps(report, ensure_ascii=False, indent=2, allow_nan=False))


if __name__ == "__main__":
    main()
