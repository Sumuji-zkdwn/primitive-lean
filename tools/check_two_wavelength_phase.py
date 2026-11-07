#!/usr/bin/env python3
"""Independent exact and numerical checks of two cosine-intensity channels.

Exact arithmetic: fold rational coefficients of pi into [0, 1], using
cos(pi*x) = cos(pi*y) iff x-y or x+y belongs to 2 Z.  No floating-point
tolerance is used to declare optical states equal.  This analytically valid
cosine criterion is checked by two different rational algorithms below.

Numerical experiments: minimum L-infinity signal spacing and seeded nearest
codeword decoding with independent additive Gaussian detector errors.  The
first channel stays calibrated; a wavelength ratio w=lambda2/lambda1 and
index-contrast ratio d=DeltaN2/DeltaN1 give the effective phase ratio r=d/w.
These are model parameters, not measurements or material dispersion data.

This script imports neither Lean output nor the earlier Python checker.
Run: python -B tools/check_two_wavelength_phase.py --output RESULTS.json
"""

import argparse
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations, product
import json
import math
from pathlib import Path
import random


IDEAL_RATIO = F(3, 2)
BASE_COMMIT = "b293710217765e12992de522a866d0fafef4d95a"


def phase_units(height):
    """phi1 / pi, kept rational."""
    return (F(height) + 1) / 2


def folded_cosine_key(q):
    """Unique representative of q modulo q ~ +/- q + 2 Z."""
    residue = F(q) % 2
    return min(residue, 2 - residue)


def cosine_equal_exact(q, s):
    """Signed-period criterion, independent of the folding implementation."""
    return ((q - s) / 2).denominator == 1 or ((q + s) / 2).denominator == 1


def observation_key(height, ratio=IDEAL_RATIO, channels=2):
    q = phase_units(height)
    factors = (F(1), F(ratio))[:channels]
    return tuple(folded_cosine_key(factor * q) for factor in factors)


def collision_three_halves(h, k):
    """All four sign choices, with the two equal-sign cases simplified."""
    difference = F(h) - F(k)
    total = F(h) + F(k) + 2
    integral = lambda x: x.denominator == 1
    return (
        integral(difference / 8)
        or integral(total / 8)
        or (integral(difference / 4) and integral(3 * total / 8))
        or (integral(total / 4) and integral(3 * difference / 8))
    )


def intensity_from_key(q):
    # Return exactly representable special values before the numerical cosine.
    special = {F(0): 1.0, F(1, 3): 0.75, F(1, 2): 0.5,
               F(2, 3): 0.25, F(1): 0.0}
    return special[q] if q in special else (1 + math.cos(math.pi * float(q))) / 2


def observation(height, ratio=IDEAL_RATIO, channels=2):
    # Equal exact keys deliberately produce bit-identical numerical codewords.
    # Floating-point cosine roundoff must not make an exact alias distinguishable.
    return tuple(intensity_from_key(q) for q in observation_key(height, ratio, channels))


def exact_rational_observation(height, ratio=IDEAL_RATIO):
    special = {F(0): F(1), F(1, 3): F(3, 4), F(1, 2): F(1, 2),
               F(2, 3): F(1, 4), F(1): F(0)}
    return tuple(special[q] for q in observation_key(height, ratio))


def partition(heights, ratio=IDEAL_RATIO, channels=2):
    groups = defaultdict(list)
    for h in heights:
        groups[observation_key(h, ratio, channels)].append(F(h))
    return [
        {"folded_phase_over_pi": [str(q) for q in key],
         "heights": [str(h) for h in group]}
        for key, group in groups.items()
    ]


def distance_inf(a, b):
    return max(abs(x - y) for x, y in zip(a, b))


def minimum_spacing(heights, ratio=IDEAL_RATIO):
    code = [observation(h, ratio) for h in heights]
    gap, i, j = min((distance_inf(code[i], code[j]), i, j)
                    for i, j in combinations(range(len(heights)), 2))
    return {"minimum_linf_spacing": gap,
            "closest_height_pair": [str(heights[i]), str(heights[j])],
            "strict_bounded_error_sufficient_limit": gap / 2}


def nearest_index(measurement, code):
    """L-infinity nearest codeword; exact ties select the first input state."""
    x, y = measurement
    return min(range(len(code)),
               key=lambda j: max(abs(x - code[j][0]), abs(y - code[j][1])))


def exact_checks():
    assert exact_rational_observation(F(-1)) == (F(1), F(1))
    assert exact_rational_observation(F(3)) == (F(1), F(0))
    assert observation_key(-1, channels=1) == observation_key(3, channels=1)
    assert observation_key(-1) != observation_key(3)
    assert exact_rational_observation(F(-1, 3)) == (F(3, 4), F(1, 2))
    assert exact_rational_observation(F(7, 3)) == (F(3, 4), F(1, 2))

    # Exhaustive comparison of the canonical-key and signed-period algorithms.
    fine_grid = [F(i, 6) for i in range(-54, 91)]
    checked_pairs = 0
    for h, k in combinations(fine_grid, 2):
        q, s = phase_units(h), phase_units(k)
        equality = all(cosine_equal_exact(r * q, r * s) for r in (F(1), IDEAL_RATIO))
        assert (observation_key(h) == observation_key(k)) == equality
        assert collision_three_halves(h, k) == equality
        checked_pairs += 1
    for h in fine_grid:
        assert observation_key(h + 8) == observation_key(h)
        assert observation_key(6 - h) == observation_key(h)
        for ratio in (F(1), F(3, 2), F(4, 3), F(101, 67)):
            assert observation_key(-h - 2, ratio) == observation_key(h, ratio)

    grids = {
        "five_representatives": [F(i) for i in range(-1, 4)],
        "integer_minus1_to7": [F(i) for i in range(-1, 8)],
        "integer_minus9_to15": [F(i) for i in range(-9, 16)],
        "thirds_minus1_to7": [F(i, 3) for i in range(-3, 22)],
    }
    expected = {
        "five_representatives": (3, 5), "integer_minus1_to7": (3, 5),
        "integer_minus9_to15": (3, 5), "thirds_minus1_to7": (7, 12),
    }
    summaries = {}
    for name, heights in grids.items():
        single = partition(heights, channels=1)
        dual = partition(heights)
        assert (len(single), len(dual)) == expected[name]
        summaries[name] = {"state_count": len(heights), "single_class_count": len(single),
                           "dual_class_count": len(dual), "single_classes": single,
                           "dual_classes": dual, **minimum_spacing(heights)}

    five = grids["five_representatives"]
    assert minimum_spacing(five)["minimum_linf_spacing"] == 0.5
    bounded_rng = random.Random(20261107)
    code = [observation(h) for h in five]
    bounded_samples = 0
    for i, center in enumerate(code):
        errors = list(product((-0.24, 0.24), repeat=2))
        errors.extend((bounded_rng.uniform(-0.24, 0.24),
                       bounded_rng.uniform(-0.24, 0.24)) for _ in range(1000))
        for error in errors:
            assert nearest_index((center[0] + error[0], center[1] + error[1]), code) == i
            bounded_samples += 1

    return {"fine_grid_state_count": len(fine_grid),
            "exhaustive_pair_comparisons": checked_pairs,
            "bounded_noise_sample_count": bounded_samples,
            "bounded_noise_magnitude": 0.24,
            "bounded_noise_note": "Finite checks; the analytic spacing bound is epsilon < 1/4.",
            "grids": summaries}


def parameter_scan():
    five = [F(i) for i in range(-1, 4)]
    nine = [F(i) for i in range(-1, 8)]
    scenarios = [
        ("equal_wavelengths", F(1), F(1)),
        ("second_harmonic", F(1, 2), F(1)),
        ("ideal_two_thirds", F(2, 3), F(1)),
        ("wavelength_three_quarters", F(3, 4), F(1)),
        ("wavelength_four_fifths", F(4, 5), F(1)),
        ("wavelength_plus_1pct", F(2, 3) * F(101, 100), F(1)),
        ("wavelength_minus_1pct", F(2, 3) * F(99, 100), F(1)),
        ("contrast_plus_0_01pct", F(2, 3), F(10001, 10000)),
        ("contrast_plus_0_1pct", F(2, 3), F(1001, 1000)),
        ("contrast_plus_1pct", F(2, 3), F(101, 100)),
        ("contrast_minus_1pct", F(2, 3), F(99, 100)),
        ("contrast_plus_10pct", F(2, 3), F(11, 10)),
        ("contrast_plus_one_third", F(2, 3), F(4, 3)),
    ]
    rows = []
    optical_checks = 0
    for name, wavelength_ratio, contrast_ratio in scenarios:
        ratio = contrast_ratio / wavelength_ratio
        # Verify the physical phase normalization algebra exactly (units: nm).
        wavelength1, contrast1 = F(1550), F(111, 250)
        wavelength2 = wavelength_ratio * wavelength1
        contrast2 = contrast_ratio * contrast1
        scale = wavelength1 / (4 * contrast1)
        for h in [F(i, 3) for i in range(-3, 22)]:
            path = scale * (h + 1)
            assert 2 * contrast1 * path / wavelength1 == phase_units(h)
            assert 2 * contrast2 * path / wavelength2 == ratio * phase_units(h)
            optical_checks += 1
        rows.append({"scenario": name, "wavelength_ratio": str(wavelength_ratio),
                     "index_contrast_ratio": str(contrast_ratio),
                     "effective_phase_ratio": str(ratio),
                     "five_state_exact_classes": len(partition(five, ratio)),
                     "nine_state_exact_classes": len(partition(nine, ratio)),
                     "five_state_spacing": minimum_spacing(five, ratio),
                     "nine_state_spacing": minimum_spacing(nine, ratio),
                     "example_minus1_vs3_second_channel_gap":
                         abs(observation(-1, ratio)[1] - observation(3, ratio)[1])})
    assert optical_checks == 325
    assert rows[0]["nine_state_exact_classes"] == 3
    assert rows[1]["nine_state_exact_classes"] == 3
    assert rows[2]["nine_state_exact_classes"] == 5
    assert rows[9]["nine_state_exact_classes"] == 9
    assert rows[-1]["five_state_exact_classes"] == 3
    return {"exact_optical_calibration_checks": optical_checks, "scenarios": rows}


def noise_experiments(trials_per_state, seed):
    five = [F(i) for i in range(-1, 4)]
    nine = [F(i) for i in range(-1, 8)]
    settings = [
        ("five_ideal", five, F(2, 3), F(1)),
        ("nine_ideal", nine, F(2, 3), F(1)),
        ("five_contrast_plus_1pct", five, F(2, 3), F(101, 100)),
        ("nine_contrast_plus_1pct", nine, F(2, 3), F(101, 100)),
        ("five_contrast_plus_10pct", five, F(2, 3), F(11, 10)),
        ("nine_wavelength_plus_1pct", nine, F(2, 3) * F(101, 100), F(1)),
        ("nine_wavelength_four_fifths", nine, F(4, 5), F(1)),
    ]
    sigmas = (0.0, 0.001, 0.01, 0.05, 0.1, 0.2)
    rows = []
    for index, (name, heights, wavelength_ratio, contrast_ratio) in enumerate(settings):
        ratio = contrast_ratio / wavelength_ratio
        actual = [observation(h, ratio) for h in heights]
        nominal = [observation(h, IDEAL_RATIO) for h in heights]
        same_decoder = actual == nominal
        for sigma_index, sigma in enumerate(sigmas):
            rng = random.Random(seed + 100 * index + sigma_index)
            calibrated_errors = nominal_errors = 0
            per_state = []
            for i, center in enumerate(actual):
                calibrated_state_errors = nominal_state_errors = 0
                for _ in range(trials_per_state):
                    y = (center[0] + rng.gauss(0, sigma), center[1] + rng.gauss(0, sigma))
                    detected = nearest_index(y, actual)
                    nominal_detected = detected if same_decoder else nearest_index(y, nominal)
                    calibrated_state_errors += detected != i
                    nominal_state_errors += nominal_detected != i
                calibrated_errors += calibrated_state_errors
                nominal_errors += nominal_state_errors
                per_state.append({"height": str(heights[i]),
                                  "calibrated_errors": calibrated_state_errors,
                                  "nominal_errors": nominal_state_errors})
            total = len(heights) * trials_per_state
            rows.append({"scenario": name, "effective_phase_ratio": str(ratio),
                         "sigma": sigma, "samples": total,
                         "calibrated_error_count": calibrated_errors,
                         "calibrated_error_rate": calibrated_errors / total,
                         "nominal_error_count": nominal_errors,
                         "nominal_error_rate": nominal_errors / total,
                         "per_state_errors": per_state})
    for row in rows:
        if row["sigma"] == 0:
            if row["scenario"] == "nine_ideal":
                assert row["calibrated_error_count"] == 4 * trials_per_state
            else:
                assert row["calibrated_error_count"] == 0
    return {"seed": seed, "trials_per_state": trials_per_state,
            "decoder": "L-infinity nearest codeword; ties select first height in ascending order",
            "sampling": "Equal numbers per state; independent additive N(0,sigma^2) errors on both channels; no clipping",
            "calibrated_decoder": "Uses the actual effective phase ratio d/w",
            "nominal_decoder": "Continues to use ideal ratio 3/2 even when d/w changes",
            "scenarios": rows}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Write deterministic JSON evidence")
    parser.add_argument("--trials-per-state", type=int, default=5000)
    parser.add_argument("--seed", type=int, default=20261107)
    args = parser.parse_args()
    if args.trials_per_state <= 0:
        parser.error("--trials-per-state must be positive")
    exact = exact_checks()
    scan = parameter_scan()
    noise = noise_experiments(args.trials_per_state, args.seed)
    evidence = {
        "schema_version": 1, "parent_commit": BASE_COMMIT,
        "model": {"first_phase": "pi*(h+1)/2", "second_phase": "(d/w)*pi*(h+1)/2",
                  "intensity": "(1+cos(phase))/2", "ideal_wavelength_ratio": "2/3",
                  "ideal_index_contrast_ratio": "1",
                  "exact_equality": "Rational phase coefficients modulo sign and 2; never a floating tolerance"},
        "exact_checks": exact, "parameter_scan": scan, "noise_experiments": noise,
        "limits": [
            "Finite sets and parameter samples do not establish a global optimum or a generic physical device.",
            "Dispersion ratios are chosen hypothetical parameters; no Sellmeier curve or measured material is used.",
            "The first wavelength calibration, common path, static state, unit fringe visibility and zero bias are assumed.",
            "Only additive detector noise is simulated; phase noise, shot statistics, heating, drift and cross-talk are absent.",
            "Signal identifiability does not imply stability, writability or retention at these additional heights.",
            "Numerical margins and Monte Carlo rates are not Lean theorems or experimental observations.",
        ],
    }
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(evidence, indent=2, ensure_ascii=False) + "\n")
    print(f"PASS: {exact['exhaustive_pair_comparisons']} exact pairs; signed-period and canonical-key criteria agree")
    for name, grid in exact["grids"].items():
        print(f"PASS: {name}: {grid['state_count']} states, {grid['single_class_count']} single -> {grid['dual_class_count']} dual classes")
    print(f"PASS: {scan['exact_optical_calibration_checks']} exact wavelength/dispersion calibrations")
    print(f"PASS: {exact['bounded_noise_sample_count']} bounded-error samples at epsilon=0.24 on five states")
    print(f"PASS: {len(noise['scenarios'])} seeded Gaussian scenarios, {args.trials_per_state} trials per state")
    if args.output:
        print(f"Evidence: {args.output}")


if __name__ == "__main__":
    main()
