#!/usr/bin/env python3
"""Independent oblique-incidence check for the PR #93 glass/film/air stack.

The optical input angle is measured inside glass from the glass/film normal.
The prism apex is a separate geometric parameter and is not used as that angle.
All indices are real and lossless. The fluid index is illustrative (n=1.40).
"""
from __future__ import annotations

import cmath
import math

N_GLASS = 1.67667
N_FILM = 1.40  # illustrative; not a measured liquid
N_AIR = 1.00
LAMBDA_NM = 1529.6
D_HALF_WAVE_NM = LAMBDA_NM / (2 * N_FILM)
D_THREE_QUARTER_NM = 3 * LAMBDA_NM / (4 * N_FILM)


def kz_index(n: float, alpha0: float) -> complex:
    """q_j = kz_j/k0 = sqrt(n_j^2 - (n0 sin(alpha0))^2), outgoing branch."""
    tangential_index = N_GLASS * math.sin(alpha0)
    q = cmath.sqrt(complex(n * n - tangential_index * tangential_index, 0.0))
    if q.real < 0 or (abs(q.real) < 1e-15 and q.imag < 0):
        q = -q
    return q


def admittance(n: float, q: complex, polarization: str) -> complex:
    """Tangential-E optical admittance, up to a common vacuum factor."""
    if polarization == "s":
        return q
    if polarization == "p":
        if abs(q) < 1e-15:
            raise ValueError("p admittance is singular exactly at a critical angle")
        return n * n / q
    raise ValueError("polarization must be 's' or 'p'")


def transfer_matrix_reflection(
    alpha0: float, thickness_nm: float, polarization: str
) -> tuple[complex, complex, float, float]:
    """Return (r,t,R,T) from the characteristic matrix of the liquid film.

    Matrix convention:
      M = [[cos(delta), -i sin(delta)/Y1],
           [-i Y1 sin(delta), cos(delta)]],
      delta = 2*pi*q1*d/lambda.
    r is the reflected tangential-electric-field amplitude. Its intensity is
    invariant under the conventional sign change for the local p basis.
    """
    ns = (N_GLASS, N_FILM, N_AIR)
    qs = tuple(kz_index(n, alpha0) for n in ns)
    ys = tuple(admittance(n, q, polarization) for n, q in zip(ns, qs))
    y0, y1, y2 = ys

    delta = 2 * math.pi * qs[1] * thickness_nm / LAMBDA_NM
    cosine = cmath.cos(delta)
    sine = cmath.sin(delta)
    a = cosine
    b = -1j * sine / y1
    c = -1j * y1 * sine
    d = cosine

    denominator = y0 * (a + b * y2) + c + d * y2
    numerator = y0 * (a + b * y2) - c - d * y2
    r = numerator / denominator
    t = 2 * y0 / denominator
    reflectance = abs(r) ** 2
    transmittance = max(0.0, y2.real / y0.real * abs(t) ** 2)
    return r, t, reflectance, transmittance


def airy_recursion_reflection(
    alpha0: float, thickness_nm: float, polarization: str
) -> complex:
    """Independent interface-recursion expression for the same stack."""
    ns = (N_GLASS, N_FILM, N_AIR)
    qs = tuple(kz_index(n, alpha0) for n in ns)
    ys = tuple(admittance(n, q, polarization) for n, q in zip(ns, qs))
    r01 = (ys[0] - ys[1]) / (ys[0] + ys[1])
    r12 = (ys[1] - ys[2]) / (ys[1] + ys[2])
    round_trip = cmath.exp(4j * math.pi * qs[1] * thickness_nm / LAMBDA_NM)
    return (r01 + r12 * round_trip) / (1 + r01 * r12 * round_trip)


def interface_fringe_span(alpha0: float, polarization: str) -> float:
    """Full max-min reflectance as film thickness varies, when all q are real."""
    qs = tuple(kz_index(n, alpha0) for n in (N_GLASS, N_FILM, N_AIR))
    if any(abs(q.imag) > 1e-12 or q.real <= 0 for q in qs):
        return 0.0
    ys = tuple(admittance(n, q, polarization) for n, q in zip((N_GLASS, N_FILM, N_AIR), qs))
    r01 = (ys[0] - ys[1]) / (ys[0] + ys[1])
    r12 = (ys[1] - ys[2]) / (ys[1] + ys[2])
    upper = abs((r01 + r12) / (1 + r01 * r12)) ** 2
    lower = abs((r01 - r12) / (1 - r01 * r12)) ** 2
    return abs(upper - lower)


def critical_angles_deg() -> tuple[float, float]:
    """(glass->air transmission cutoff, glass->film TIR cutoff)."""
    return (
        math.degrees(math.asin(N_AIR / N_GLASS)),
        math.degrees(math.asin(N_FILM / N_GLASS)),
    )


def state_gap(alpha0: float, polarization: str) -> float:
    r_a = transfer_matrix_reflection(alpha0, D_HALF_WAVE_NM, polarization)[2]
    r_b = transfer_matrix_reflection(alpha0, D_THREE_QUARTER_NM, polarization)[2]
    return r_a - r_b


def state_gap_roots_deg(polarization: str) -> list[float]:
    """Find isolated equal-intensity angles for the two PR #93 film states."""
    air_cutoff, _ = critical_angles_deg()
    right = math.radians(air_cutoff - 1e-6)
    count = 20000
    roots: list[float] = []
    left_x = 0.0
    left_y = state_gap(left_x, polarization)
    for j in range(1, count + 1):
        x = right * j / count
        y = state_gap(x, polarization)
        if left_y * y < 0:
            lo, hi, flo = left_x, x, left_y
            for _ in range(70):
                mid = (lo + hi) / 2
                fm = state_gap(mid, polarization)
                if flo * fm <= 0:
                    hi = mid
                else:
                    lo, flo = mid, fm
            roots.append(math.degrees((lo + hi) / 2))
        left_x, left_y = x, y
    return roots


def main() -> None:
    air_cutoff, film_cutoff = critical_angles_deg()
    alpha_air = math.radians(air_cutoff)
    alpha_film = math.radians(film_cutoff)

    # Preserve the two normal-incidence PR #93 states and their reported gap.
    normal = {
        pol: (
            transfer_matrix_reflection(0.0, D_HALF_WAVE_NM, pol)[2],
            transfer_matrix_reflection(0.0, D_THREE_QUARTER_NM, pol)[2],
        )
        for pol in "sp"
    }
    assert math.isclose(normal["s"][0], 0.0639093178950225, abs_tol=1e-14)
    assert math.isclose(normal["s"][1], 0.00606984128672157, abs_tol=1e-14)
    assert math.isclose(normal["s"][0] - normal["s"][1], 0.0578394766083009, abs_tol=1e-14)

    # Transfer matrix and independent Airy recursion agree, and power balances
    # when the glass, film and air all carry propagating waves.
    checked = 0
    for deg in (0.0, 7.5, 15.0, 25.0, 29.0, 30.0, 35.0, 36.0):
        alpha = math.radians(deg)
        for pol in "sp":
            for thickness in (0.0, 83.7, D_HALF_WAVE_NM, D_THREE_QUARTER_NM, 1000.0):
                r, _, reflectance, transmittance = transfer_matrix_reflection(alpha, thickness, pol)
                r_air = airy_recursion_reflection(alpha, thickness, pol)
                assert abs(r - r_air) < 2e-12, (deg, pol, thickness, r, r_air)
                assert abs(reflectance + transmittance - 1.0) < 2e-12
                checked += 1

    # Compare the complex amplitudes in the evanescent-output and 60-degree
    # regimes too, not just their unit intensities.
    for deg in (37.0, 60.0):
        alpha = math.radians(deg)
        for pol in "sp":
            for thickness in (0.0, D_HALF_WAVE_NM, D_THREE_QUARTER_NM, 1000.0):
                r, _, _, _ = transfer_matrix_reflection(alpha, thickness, pol)
                r_air = airy_recursion_reflection(alpha, thickness, pol)
                assert abs(r-r_air) < 2e-12, (deg, pol, thickness, r, r_air)
                checked += 1

    # The pair aliases at the exact internal angle for which cos(alpha1)=4/5:
    # their round-trip phases are 1.6*pi and 2.4*pi, with equal cosines.
    alpha_pair_alias = math.asin((N_FILM * 3 / 5) / N_GLASS)
    for pol in "sp":
        assert abs(state_gap(alpha_pair_alias, pol)) < 2e-14

    # At the p-polarized film/air Brewster angle the second interface has no
    # reflected p amplitude; the entire p-reflectance curve is thickness-flat.
    alpha_p_brewster = math.asin(
        N_FILM * N_AIR / (N_GLASS * math.sqrt(N_FILM**2 + N_AIR**2))
    )
    assert interface_fringe_span(alpha_p_brewster, "p") < 2e-13
    assert interface_fringe_span(alpha_p_brewster, "s") > 1e-3

    # Below the glass/air critical angle, generic thickness dependence exists.
    for deg in (0.0, 15.0, 30.0, 35.0, 36.0):
        for pol in "sp":
            assert interface_fringe_span(math.radians(deg), pol) > 0.0

    # At and above the glass/air critical angle the semi-infinite air output is
    # evanescent. A lossless stack carries no transmitted normal power, so R=1
    # at every film thickness (including the 60-degree check requested here).
    for deg in (37.0, 40.0, 56.0, 57.0, 60.0, 75.0):
        alpha = math.radians(deg)
        for pol in "sp":
            values = []
            for j in range(101):
                thickness = j * 19.37
                _, _, reflectance, transmittance = transfer_matrix_reflection(alpha, thickness, pol)
                assert abs(reflectance - 1.0) < 3e-12, (deg, pol, thickness, reflectance)
                assert transmittance < 1e-14
                values.append(reflectance)
            assert max(values) - min(values) < 3e-12

    # Intensity becomes thickness-independent at 60 degrees, while the
    # reflected coherent phase retains a nonzero state difference.
    phase_differences_deg = {}
    for pol in "sp":
        r_a = transfer_matrix_reflection(math.radians(60), D_HALF_WAVE_NM, pol)[0]
        r_b = transfer_matrix_reflection(math.radians(60), D_THREE_QUARTER_NM, pol)[0]
        phase_difference = math.degrees(cmath.phase(r_b / r_a))
        assert abs(phase_difference) > 1.0
        phase_differences_deg[pol] = phase_difference

    roots = {pol: state_gap_roots_deg(pol) for pol in "sp"}
    assert len(roots["s"]) == 1 and abs(roots["s"][0] - 30.06572076) < 1e-6
    assert len(roots["p"]) == 2
    assert abs(roots["p"][0] - 29.03390855) < 1e-6
    assert abs(roots["p"][1] - 30.06572076) < 1e-6

    print(f"PASS transfer matrix vs independent Airy recursion: {checked} cases")
    print("PASS R+T=1 for all tested subcritical propagating s/p cases")
    print("PASS 60-degree s/p reflectance is 1 and thickness-independent")
    print("PASS 60-degree reflected phase remains thickness-dependent")
    print(f"critical glass->air angle: {air_cutoff:.9f} deg")
    print(f"critical glass->film angle: {film_cutoff:.9f} deg")
    print(f"p film/air Brewster angle: {math.degrees(alpha_p_brewster):.9f} deg")
    print(f"two-state equal-phase angle: {math.degrees(alpha_pair_alias):.9f} deg")
    print(f"60-degree phase difference d2/d1: s={phase_differences_deg['s']:.6f} deg, "
          f"p={phase_differences_deg['p']:.6f} deg")
    print(f"two-state intensity-collision angles: s={roots['s']}, p={roots['p']}")
    print("alpha0 | gap(s) pp | span(s) pp | gap(p) pp | span(p) pp")
    for deg in (0.0, 15.0, 25.0, 29.0, 29.03390855, 30.0, 30.06572076, 35.0, 36.0, 36.5):
        alpha = math.radians(deg)
        gs = 100 * state_gap(alpha, "s")
        gp = 100 * state_gap(alpha, "p")
        ss = 100 * interface_fringe_span(alpha, "s")
        sp = 100 * interface_fringe_span(alpha, "p")
        print(f"{deg:8.5f} | {gs:9.6f} | {ss:10.6f} | {gp:9.6f} | {sp:10.6f}")


if __name__ == "__main__":
    main()
