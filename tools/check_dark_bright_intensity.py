#!/usr/bin/env python3
"""Exact rational regressions for intensity-only exchange invisibility.

These finite checks complement, but do not replace, the universal Lean proofs.
"""

from collections import Counter
from fractions import Fraction as F
from itertools import product
import json


def exchange(x):
    br, bi, dr, di = x
    return dr, di, br, bi


def coherence(x):
    br, bi, dr, di = x
    return br * dr + bi * di, bi * dr - br * di


def intensity(x):
    re, im = coherence(x)
    return re * re + im * im


def mix(x, pulse):
    c, s = pulse
    br, bi, dr, di = x
    return (c * br + s * di, c * bi - s * dr,
            c * dr + s * bi, c * di - s * br)


def trace(word, x):
    out = [intensity(x)]
    for pulse in word:
        x = mix(x, pulse)
        out.append(intensity(x))
    return tuple(out)


def all_words(alphabet, max_length):
    for n in range(max_length + 1):
        yield from product(alphabet, repeat=n)


def main():
    states = [tuple(map(F, xs)) for xs in product(range(-2, 3), repeat=4)]
    pulses = [
        (F(1), F(0)),
        (F(0), F(1)),
        (F(3, 5), F(4, 5)),
        (F(5, 13), F(12, 13)),
    ]
    word_tests = Counter()
    checks = Counter()

    for x in states:
        sx = exchange(x)
        assert exchange(sx) == x
        checks["exchange_involution"] += 1
        qr, qi = coherence(x)
        sr, si = coherence(sx)
        assert (sr, si) == (qr, -qi)
        checks["coherence_conjugation"] += 1
        assert intensity(sx) == intensity(x)
        checks["intensity_exchange"] += 1

        for pulse in pulses:
            assert exchange(mix(x, pulse)) == mix(sx, pulse)
            checks["mixer_commutation"] += 1

        for word in all_words(pulses[:3], 3):
            assert trace(word, x) == trace(word, sx)
            word_tests[len(word)] += 1
            checks["finite_trace_comparison"] += 1

    left = (F(1), F(0), F(0), F(1))  # B=1, D=i
    right = exchange(left)           # B=i, D=1
    assert coherence(left) == (F(0), F(-1))
    assert coherence(right) == (F(0), F(1))
    assert coherence(left) != coherence(right)
    assert intensity(left) == intensity(right) == F(1)
    assert coherence(left)[1] == -coherence(right)[1]

    # Every nonzero Gaussian-integer amplitude has squared modulus at least 1.
    # This witness has |B|^2=|D|^2=1, so its total amplitude norm 2 is minimal
    # among Gaussian-integer witnesses with both amplitudes nonzero.
    assert sum(v * v for v in left) == F(2)
    checks["minimal_gaussian_integer_witness"] += 1

    print(json.dumps({
        "status": "all checks passed",
        "sample_states": len(states),
        "state_grid": "[-2,2]^4 over integers",
        "arithmetic": "fractions.Fraction",
        "pulse_alphabet": ["(1,0)", "(0,1)", "(3/5,4/5)"],
        "word_lengths_tested": sorted(word_tests),
        "words_per_length": {str(k): v for k, v in sorted(word_tests.items())},
        "checks": dict(checks),
        "witness": {
            "B": "1", "D": "i", "exchanged_B": "i", "exchanged_D": "1",
            "Q": "-i", "exchanged_Q": "+i", "both_abs_Q_squared": "1",
            "total_norm_squared": "2",
        },
        "scope": "Finite exact regressions only; universal claims are proved in Lean.",
    }, indent=2))


if __name__ == "__main__":
    main()
