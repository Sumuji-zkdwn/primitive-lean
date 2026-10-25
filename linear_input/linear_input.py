"""Inspect the linear input term -u*x; standard-library runtime only.

Potential: E = lam*x**4/4 + r*x**2/2 + (y-sqrt(2)*x)**2/2 - u*x.
All ``minimum`` labels describe this potential, not stability of a dynamics.
Polynomial root decisions use Decimal arithmetic for the supplied decimal
coefficients. Displayed values are finite floats; no formal proof is claimed.
"""

from __future__ import annotations

import argparse
from decimal import Decimal, localcontext
import json
import math
import sys


def _finite(name, value):
    try:
        value = float(value)
    except (ValueError, TypeError, OverflowError) as exc:
        raise ValueError(f"{name} must be a finite real number") from exc
    if not math.isfinite(value):
        raise ValueError(f"{name} must be finite")
    return value


def _parameters(lam, r, u):
    lam, r, u = (_finite(n, v) for n, v in (("lam", lam), ("r", r), ("u", u)))
    if lam <= 0:
        raise ValueError("lam must be strictly positive")
    return lam, r, u


def _out(value):
    result = float(value)
    if not math.isfinite(result):
        raise ValueError("result exceeds finite floating-point output range; rescale the units")
    if result == 0 and value != 0:
        raise ValueError("nonzero result underflows floating-point output range; rescale the units")
    return result


def _decimal(value):
    return Decimal(str(value))


def _cbrt(value):
    if not value:
        return Decimal(0)
    guess = Decimal(10) ** ((value.adjusted() + 3) // 3)
    for _ in range(400):
        updated = (2 * guess + value / guess**2) / 3
        if abs(updated - guess) <= abs(updated) * Decimal("1e-95"):
            return updated
        guess = updated
    raise ValueError("cube-root iteration failed; rescale the units")


def _bisect(function, lo, hi):
    flo, fhi = function(lo), function(hi)
    if flo == 0:
        return lo
    if fhi == 0:
        return hi
    if (flo > 0) == (fhi > 0):
        raise ValueError("root bracket could not be resolved")
    for _ in range(4096):
        middle = (lo + hi) / 2
        if middle == lo or middle == hi:
            return middle
        fm = function(middle)
        if fm == 0:
            return middle
        if (fm > 0) == (flo > 0):
            lo, flo = middle, fm
        else:
            hi = middle
    raise ValueError("root bisection failed; rescale the units")


def _roots(lam, r, u):
    """High-precision roots with no tolerance merging near a fold."""
    disc = -4 * lam * r**3 - 27 * lam**2 * u**2
    if u == 0:
        if r < 0:
            a = (-r / lam).sqrt()
            return [-a, Decimal(0), a], disc
        return [Decimal(0)], disc
    if disc == 0:
        double = 3 * u / (2 * r)
        return sorted([double, -2 * double]), disc
    scale = max((abs(r) / lam).sqrt(), _cbrt(abs(u) / lam))
    p, q = r / (lam * scale**2), u / (lam * scale**3)
    f = lambda t: t**3 + p * t - q
    if disc > 0:
        a = (-p / 3).sqrt()
        intervals = [(Decimal(-2), -a), (-a, a), (a, Decimal(2))]
    else:
        intervals = [(Decimal(-2), Decimal(2))]
    return [scale * _bisect(f, lo, hi) for lo, hi in intervals], disc


def _critical_data(lam, r, u):
    roots, disc = _roots(lam, r, u)
    points = []
    for x in roots:
        reduced_second = 3 * lam * x**2 + r
        is_fold = disc == 0 and r < 0 and x == 3 * u / (2 * r)
        if is_fold:
            kind, multiplicity = "degenerate_fold", 2
        elif r == 0 and u == 0:
            kind, multiplicity = "quartic_minimum", 3
        elif reduced_second > 0:
            kind, multiplicity = "local_minimum", 1
        else:
            kind, multiplicity = "saddle", 1
        global_min = kind in ("local_minimum", "quartic_minimum") and (
            u == 0 or (x > 0) == (u > 0)
        )
        value = lam * x**4 / 4 + r * x**2 / 2 - u * x
        residual = lam * x**3 + r * x - u
        normalizer = max(abs(lam * x**3) + abs(r * x) + abs(u), Decimal(1))
        points.append({
            "x": _out(x), "y": _out(Decimal(2).sqrt() * x),
            "energy": _out(value), "type": kind,
            "polynomial_root_multiplicity": multiplicity,
            "global_minimum": global_min,
            "reduced_second_derivative": _out(reduced_second) if not is_fold else 0.0,
            "scaled_root_residual": float(abs(residual) / normalizer),
        })
    return points, disc, roots


def critical_points(lam=1.0, r=-1.0, u=0.0):
    """Return all real stationary points, their potential type and global status."""
    lam, r, u = _parameters(lam, r, u)
    with localcontext() as ctx:
        ctx.prec = 100
        return _critical_data(*map(_decimal, (lam, r, u)))[0]


def analyze(lam=1.0, r=-1.0, u=0.0, target=None, upper=None):
    """Analyze a fixed-input potential and an optional closed energy band.

The symbolic bound is valid for every fixed input u. Root-based band inspection
is a numerical check, not a proof certificate. If upper is omitted, inspect all
critical energies greater than or equal to target.
"""
    lam, r, u = _parameters(lam, r, u)
    if upper is not None and target is None:
        raise ValueError("upper requires target")
    if target is not None:
        target = _finite("target", target)
    if upper is not None:
        upper = _finite("upper", upper)
        if upper <= target:
            raise ValueError("upper must be strictly greater than target")
    with localcontext() as ctx:
        ctx.prec = 100
        dl, dr, du = map(_decimal, (lam, r, u))
        points, disc, roots = _critical_data(dl, dr, du)
        threshold = max(-dr, Decimal(0))**2 / (12 * dl)
        fold = 2 * (-dr / 3).sqrt()**3 / dl.sqrt() if dr < 0 else None
        minimum = min(p["energy"] for p in points if p["global_minimum"])
        result = {
            "parameters": {"lam": lam, "r": r, "u": u},
            "potential": "lam*x^4/4 + r*x^2/2 + (y-sqrt(2)*x)^2/2 - u*x",
            "critical_points": points,
            "global_minimum_energy": minimum,
            "global_minimizers": [p["x"] for p in points if p["global_minimum"]],
            "fold_input_magnitude": _out(fold) if fold is not None else None,
            "discriminant_sign": 1 if disc > 0 else -1 if disc < 0 else 0,
            "uniform_critical_energy_upper_bound": _out(threshold),
            "analytic_bound": {
                "formula": "max(-r,0)^2/(12*lam)",
                "critical_energy_identity": "Ecrit = -3*lam*x^4/4 - r*x^2/2",
                "scope": "For every real fixed input u; target strictly above this bound excludes all critical points from E >= target.",
            },
            "evidence": "Decimal(100) root calculation and analytic formulas; not Lean verification. Types describe potential extrema, not dynamical stability.",
        }
        if target is not None:
            dt = _decimal(target)
            upper_d = _decimal(upper) if upper is not None else None
            in_band = [i for i, x in enumerate(roots)
                       if (ev := dl*x**4/4 + dr*x**2/2 - du*x) >= dt
                       and (upper_d is None or ev <= upper_d)]
            result["target_band"] = {
                "target": target, "upper": upper,
                "numerically_detected_critical_indices": in_band,
                "numerical_no_critical_points": not in_band,
                "analytic_uniform_no_critical_points": dt > threshold,
                "origin_excluded_by_positive_target": target > 0,
                "scope": "Fixed u only. A moving u adds -x*du/dt to dE/dt. Numerically inspected endpoints are not interval-certified.",
            }
        return result


def recover(u1, energy1, u2, energy2, error1=0.0, error2=0.0):
    """Recover x and E_0 from two energies of ONE unchanged state.

error1/error2 bound absolute measurement errors. Bounds cover measurement
errors only, not floating-point rounding or state changes between measurements.
"""
    values = dict(u1=u1, energy1=energy1, u2=u2, energy2=energy2, error1=error1, error2=error2)
    values = {key: _finite(key, value) for key, value in values.items()}
    if values["error1"] < 0 or values["error2"] < 0:
        raise ValueError("measurement-error bounds must be nonnegative")
    if values["u1"] == values["u2"]:
        raise ValueError("u1 and u2 must differ; one input cannot recover x")
    with localcontext() as ctx:
        ctx.prec = 100
        a, b, c, d, e, f = (_decimal(values[k]) for k in values)
        gap = c-a
        return {
            "x": _out((b-d)/gap),
            "energy_at_zero_input": _out((c*b-a*d)/gap),
            "input_gap": _out(abs(gap)),
            "absolute_x_error_bound": _out((e+f)/abs(gap)),
            "absolute_zero_energy_error_bound": _out((abs(c)*e+abs(a)*f)/abs(gap)),
            "assumption": "Both energies refer to exactly the same state; error bounds cover measurement errors only.",
        }


def energy(lam, r, x, y, u):
    lam, r, u = _parameters(lam, r, u)
    x, y = _finite("x", x), _finite("y", y)
    with localcontext() as ctx:
        ctx.prec = 100
        dl, dr, dx, dy, du = map(_decimal, (lam, r, x, y, u))
        return _out(dl*dx**4/4 + dr*dx**2/2 + (dy-Decimal(2).sqrt()*dx)**2/2-du*dx)


def coordinates(lam, r, x, y, u):
    """Global polynomial coordinate change; fixed-u slices become curved."""
    lam, r, u = _parameters(lam, r, u)
    x, y = _finite("x", x), _finite("y", y)
    with localcontext() as ctx:
        ctx.prec = 100
        dl, dr, dx, dy, du = map(_decimal, (lam, r, x, y, u))
        Y, U = dy-Decimal(2).sqrt()*dx, du-dl*dx**3/4-dr*dx/2
        e = dl*dx**4/4+dr*dx**2/2+(dy-Decimal(2).sqrt()*dx)**2/2-du*dx
        q = Y**2/2-dx*U
        return {
            "original": {"x": x, "y": y, "u": u},
            "transformed": {"x": x, "Y": _out(Y), "U": _out(U)},
            "inverse": {"x": x, "y": _out(Y+Decimal(2).sqrt()*dx), "u": _out(U+dl*dx**3/4+dr*dx/2)},
            "energy_original": _out(e), "energy_quadratic": _out(q),
            "absolute_identity_residual": float(abs(e-q)),
            "jacobian_determinant": 1,
            "fixed_input_slice": "U = u_fixed - lam*x^3/4 - r*x/2",
            "scope": "Coordinate identity only. Constraints, metrics and vector fields must also be transported before inferring dynamical equivalence.",
        }


def design(lam=1.0, r=-1.0, x=1.0):
    """Find the unique input making the requested x stationary.

Then determine whether it is a local or global potential minimum. This is
input design for a static minimization problem, not a controller or stability
certificate for a dynamic system.
"""
    lam, r, _ = _parameters(lam, r, 0)
    x = _finite("x", x)
    with localcontext() as ctx:
        ctx.prec = 100
        dl, dr, dx = map(_decimal, (lam, r, x))
        du = dl*dx**3+dr*dx
        second = 3*dl*dx**2+dr
        if second > 0:
            kind = "local_minimum"
        elif second < 0:
            kind = "saddle"
        elif dx == 0 and dr == 0:
            kind = "quartic_minimum"
        else:
            kind = "degenerate_fold"
        if dr >= 0:
            global_status = "unique_global_minimum"
        else:
            gap = dl*dx**2+dr
            global_status = ("unique_global_minimum" if gap > 0
                             else "two_tied_global_minima" if gap == 0
                             else "not_a_global_minimum_for_any_input")
        return {
            "parameters": {"lam": lam, "r": r},
            "requested_x": x, "stationary_y": _out(Decimal(2).sqrt()*dx),
            "required_input": _out(du), "potential_type": kind,
            "reduced_second_derivative": _out(second),
            "global_margin": _out(dl*dx**2+dr),
            "global_status": global_status,
            "global_realizability_boundary": _out((-dr/dl).sqrt()) if dr < 0 else None,
            "formula": "u = lam*x^3 + r*x",
            "global_certificate": "f_u(t)-f_u(x) = (t-x)^2 * [lam*(t+x)^2/4 + (lam*x^2+r)/2]",
            "scope": "Static potential design only. Decimal input is used literally; no tolerance rounds a requested point onto a fold or the global-realizability boundary.",
        }


def demo():
    return {
        "symmetric_wells": analyze(),
        "exact_fold": analyze(lam=1, r=-3, u=2),
        "single_well": analyze(lam=1, r=1, u=0.5),
        "safe_target": analyze(target=0.1, upper=1),
        "positive_target_counterexample": {
            "exact_data": {"lam": "1", "r": "-1", "u": "10/27", "x": "-2/3", "critical_energy": "2/27", "target": "1/27"},
            "meaning": "A positive target alone does not exclude a stationary initial point above it.",
        },
        "two_measurements": recover(0, -0.25, 0.1, -0.35, 0.001, 0.001),
        "coordinate_change": coordinates(1, -1, 1, 0, 0.2),
        "design_global_minimum": design(1, -1, 1.2),
        "design_impossible_global_minimum": design(1, -1, 0.8),
        "scope": "Static identities and numerical examples. No ODE simulation, hysteresis law or Lean theorem is asserted.",
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    subs = parser.add_subparsers(dest="command", required=True)
    analyze_parser = subs.add_parser("analyze", help="stationary points and fixed-input energy bands")
    for name, default in (("lam", 1.0), ("r", -1.0), ("u", 0.0)):
        analyze_parser.add_argument("--"+name, type=float, default=default)
    analyze_parser.add_argument("--target", type=float)
    analyze_parser.add_argument("--upper", type=float)
    recover_parser = subs.add_parser("recover", help="recover x from two measurements of the same state")
    for name in ("u1", "energy1", "u2", "energy2"):
        recover_parser.add_argument("--"+name, type=float, required=True)
    for name in ("error1", "error2"):
        recover_parser.add_argument("--"+name, type=float, default=0.0)
    coord_parser = subs.add_parser("coordinates", help="quadratic-coordinate identity and inverse")
    for name, default in (("lam", 1.0), ("r", -1.0)):
        coord_parser.add_argument("--"+name, type=float, default=default)
    for name in ("x", "y", "u"):
        coord_parser.add_argument("--"+name, type=float, required=True)
    design_parser = subs.add_parser("design", help="input required for a requested stationary x, and its minimum status")
    for name, default in (("lam", 1.0), ("r", -1.0)):
        design_parser.add_argument("--"+name, type=float, default=default)
    design_parser.add_argument("--x", type=float, required=True)
    subs.add_parser("demo", help="all representative examples")
    args = vars(parser.parse_args(argv))
    command = args.pop("command")
    try:
        result = {"analyze": analyze, "recover": recover, "coordinates": coordinates, "design": design, "demo": demo}[command](**args)
        print(json.dumps(result, ensure_ascii=False, indent=2, allow_nan=False))
        return 0
    except (ValueError, ArithmeticError) as exc:
        print(json.dumps({"error": str(exc)}, ensure_ascii=False), file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
