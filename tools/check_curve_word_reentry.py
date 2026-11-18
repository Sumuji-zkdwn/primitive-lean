"""Exact finite replay of curvature jumps in the A/B arc-word model.

Curvature is recorded as a rational coefficient of pi/h, with h > 0.
This checks the combinatorics of the source arc model, not Lean proof terms,
regularity of a smoothed curve, or elastica stationarity/minimality.
"""

import argparse
from fractions import Fraction
from itertools import product
import json

# In CurveWordArc.inc, arcAngle h a s = (a / h) * s.
# In CurveWordPiecewise.inc, A has total turn pi/2 and B has 3*pi/2.
TURN_OVER_PI = {"A": Fraction(1, 2), "B": Fraction(3, 2)}


def splice_data(word):
    """Compute exact one-sided curvature data at each interior splice.

    The normalized curvature is kappa/(pi/h). A separate analytic argument
    establishes that gamma''_+ - gamma''_- = (kappa_+ - kappa_-) J gamma',
    where the continuous tangent gamma' has unit norm.
    """
    if not isinstance(word, str) or not word or any(c not in TURN_OVER_PI for c in word):
        raise ValueError("word must be a nonempty string over A and B")

    joins = []
    accumulated_turn = Fraction(0)
    for index, (left, right) in enumerate(zip(word, word[1:]), 1):
        accumulated_turn += TURN_OVER_PI[left]
        k_left = TURN_OVER_PI[left]
        k_right = TURN_OVER_PI[right]
        jump = k_right - k_left
        joins.append({
            "position_over_h": index,
            "left": left,
            "right": right,
            "angle_over_pi": str(accumulated_turn),
            "kappa_left_over_pi_per_h": str(k_left),
            "kappa_right_over_pi_per_h": str(k_right),
            "signed_jump_over_pi_per_h": str(jump),
            "jump_norm_over_pi_per_h": str(abs(jump)),
            "C2_at_join": jump == 0,
        })
    return {
        "word": word,
        "joins": joins,
        "all_splices_C2": all(j["C2_at_join"] for j in joins),
        "has_mixed_adjacent_letters": any(a != b for a, b in zip(word, word[1:])),
    }


def audit(max_length=8):
    """Exhaustive finite check, not a quantified theorem for all lengths."""
    if type(max_length) is not int or max_length < 1:
        raise ValueError("max_length must be a positive integer")
    rows = []
    errors = []
    for length in range(1, max_length + 1):
        data = [splice_data("".join(word)) for word in product("AB", repeat=length)]
        smooth = sum(row["all_splices_C2"] for row in data)
        mixed = sum(row["has_mixed_adjacent_letters"] for row in data)
        expected_smooth, expected_mixed = 2, 2 ** length - 2
        if smooth != expected_smooth or mixed != expected_mixed:
            errors.append(f"word length {length}: unexpected adjacency classification")
        if any(row["all_splices_C2"] == row["has_mixed_adjacent_letters"] for row in data):
            errors.append(f"word length {length}: inconsistent splice classification")
        rows.append({
            "length": length,
            "words": 2 ** length,
            "all_splices_C2": smooth,
            "mixed_words_not_C2": mixed,
        })
    return {
        "passed": not errors,
        "errors": errors,
        "rows": rows,
        "scope": "Exact finite adjacency and normalized one-sided curvature coefficients; no Lean check or stationarity claim.",
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-length", type=int, default=8)
    args = parser.parse_args()
    result = audit(args.max_length)
    print(json.dumps(result, indent=2))
    raise SystemExit(0 if result["passed"] else 1)
