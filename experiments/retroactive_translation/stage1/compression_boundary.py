#!/usr/bin/env python3
"""Finite audit: when can a later interpretation be recovered from an old one?

This checks exact factorization on finite sets. It does not implement an
encryption scheme and does not establish a cryptographic work lower bound.
Run with Python 3.10+; no third-party dependencies.
"""

from __future__ import annotations

import json
from itertools import product
from pathlib import Path

if not __debug__:
    raise RuntimeError("Finite verification requires assertions; do not use -O or PYTHONOPTIMIZE.")


def collision_condition(old: tuple[int, ...], new: tuple[int, ...]) -> bool:
    """New observations must agree wherever the stored old values agree."""
    return all(
        old[x] != old[y] or new[x] == new[y]
        for x in range(len(old))
        for y in range(len(old))
    )


def factor_map(old: tuple[int, ...], new: tuple[int, ...]) -> dict[int, int] | None:
    """Construct a factor on the reached image, or exhibit its impossibility."""
    result: dict[int, int] = {}
    for a, b in zip(old, new, strict=True):
        if a in result and result[a] != b:
            return None
        result[a] = b
    return result


def verify() -> dict[str, object]:
    maps = list(product(range(2), repeat=4))
    possible, impossible = 0, 0
    for old in maps:
        for new in maps:
            # Independent brute-force search over every binary decoder h.
            decoders = [
                h for h in product(range(2), repeat=2)
                if all(h[old[x]] == new[x] for x in range(4))
            ]
            condition = collision_condition(old, new)
            witness = factor_map(old, new)
            assert condition == bool(decoders)
            assert condition == (witness is not None)
            if witness is not None:
                assert all(witness[old[x]] == new[x] for x in range(4))
                possible += 1
            else:
                impossible += 1
    assert (possible, impossible) == (60, 196)

    states = list(product(range(2), repeat=2))
    old = tuple(a for a, _ in states)
    new = tuple(b for _, b in states)
    assert factor_map(old, new) is None
    summary_counts = {
        "old_summary_values": len(set(old)),
        "joint_summary_values": len(set(zip(old, new))),
    }
    assert summary_counts == {"old_summary_values": 2, "joint_summary_values": 4}

    index_rows = []
    for dimension in range(1, 11):
        strings = list(product(range(2), repeat=dimension))
        # The vector of answers to every future coordinate query equals x.
        signatures = {
            tuple(x[j] for j in range(dimension)) for x in strings
        }
        assert len(signatures) == 1 << dimension
        index_rows.append({
            "source_bits": dimension,
            "possible_sources": len(strings),
            "required_summary_states": len(signatures),
            "minimum_fixed_width_summary_bits": dimension,
            "query_index_bits": (dimension - 1).bit_length(),
        })

    return {
        "scope": "finite exact factorization, not cryptographic security",
        "all_binary_maps_on_four_states": {
            "pairs_checked": len(maps) ** 2,
            "factorable_pairs": possible,
            "nonfactorable_pairs": impossible,
            "candidate_decoders_per_pair": 4,
        },
        "two_bit_witness": {
            "states": states,
            "old_reading_first_bit": old,
            "new_reading_second_bit": new,
            "factorization_possible": False,
            **summary_counts,
        },
        "index_problem": index_rows,
        "theorem_status": {
            "general_factorization_equivalence": "elementary proof in report",
            "general_exact_index_storage_bound": "injectivity proof in report",
            "finite_checks": "passed",
            "lean_verification": "not performed",
        },
    }


if __name__ == "__main__":
    result = verify()
    destination = Path(__file__).with_name("compression_results.json")
    destination.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "status": "passed",
        "binary_map_pairs_checked": result["all_binary_maps_on_four_states"]["pairs_checked"],
        "result_file": str(destination),
    }, ensure_ascii=False))
