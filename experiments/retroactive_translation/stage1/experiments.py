#!/usr/bin/env python3
"""Finite experiments for retroactive translation; not a secure cipher.

Python 3.10+, standard library only. Run:
    python3 experiments.py --output results.json

All reported counts are exact integer enumeration; floating-point logarithms
are used only to display entropies. No computational-security lower bound,
novel cryptographic construction, or production encryption is claimed.
The dynamic models reinterpret an already fixed ciphertext. They do not in
general let a sender transmit any independently chosen new plaintext.
"""

from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
from itertools import permutations, product
import json
from math import factorial, log2
from pathlib import Path

if not __debug__:
    raise RuntimeError("Finite verification requires assertions; do not use -O or PYTHONOPTIMIZE.")


def compose(p: tuple[int, ...], q: tuple[int, ...]) -> tuple[int, ...]:
    """p after q, both permutations of the same finite set."""
    return tuple(p[q[i]] for i in range(len(p)))


def parity(x: int) -> int:
    return x.bit_count() & 1


def reinterpret_bit(ciphertext: int, key: int, public_state: int) -> int:
    return ciphertext ^ parity(key & public_state)


def gf2_rank(rows: list[int], width: int) -> int:
    """Independent Gaussian elimination over GF(2), using integer rows."""
    basis = [0] * width
    rank = 0
    for original in rows:
        row = original
        for bit in range(width - 1, -1, -1):
            if row & (1 << bit):
                if basis[bit]:
                    row ^= basis[bit]
                else:
                    basis[bit] = row
                    rank += 1
                    break
    return rank


def entropy_counts(counts: list[int]) -> float:
    total = sum(counts)
    if not total:
        return 0.0
    return -sum((count / total) * log2(count / total) for count in counts if count)


def permutation_collapse() -> dict:
    alphabet = tuple(range(4))
    group = tuple(permutations(alphabet))
    assert len(group) == factorial(4) == 24
    distribution: Counter = Counter({alphabet: 1})
    rows = []
    direct_comparison_sequences = 0
    for depth in range(1, 5):
        next_distribution: Counter = Counter()
        for state, count in distribution.items():
            for update in group:
                next_distribution[compose(update, state)] += count
        distribution = next_distribution
        expected_sequences = 24 ** depth
        expected_multiplicity = 24 ** (depth - 1)
        assert sum(distribution.values()) == expected_sequences
        assert len(distribution) == 24
        assert set(distribution.values()) == {expected_multiplicity}

        # A second implementation enumerates each complete history rather than
        # accumulating multiplicities. It agrees through depth three.
        direct_checked = depth <= 3
        if direct_checked:
            direct: Counter = Counter()
            for history in product(group, repeat=depth):
                values = list(alphabet)
                for update in history:
                    values = [update[value] for value in values]
                direct[tuple(values)] += 1
            assert direct == distribution
            direct_comparison_sequences += expected_sequences
        rows.append({
            "depth": depth,
            "internal_histories": expected_sequences,
            "distinct_effective_maps": len(distribution),
            "histories_per_effective_map": expected_multiplicity,
            "distinct_readings_of_one_fixed_symbol": len({p[0] for p in distribution}),
            "direct_enumeration_cross_checked": direct_checked,
        })

    p = (1, 0, 2, 3)  # transposition (0 1)
    q = (0, 2, 1, 3)  # transposition (1 2)
    pq, qp = compose(p, q), compose(q, p)
    assert pq != qp
    assert pq[0] == 1 and qp[0] == 2
    state = alphabet
    updates = [p, q] * 8
    chronological_states = [state]
    for update in updates:
        state = compose(update, state)
        chronological_states.append(state)
    assert len(set(chronological_states)) <= 24
    return {
        "alphabet_size": 4,
        "composition_convention": "compose(p, q) = p after q",
        "rows": rows,
        "direct_comparison_histories": direct_comparison_sequences,
        "noncommutative_example": {
            "p": p, "q": q, "p_after_q": pq, "q_after_p": qp,
            "states_in_16_updates": chronological_states,
            "eager_map_update_entries_per_step": 4,
        },
        "interpretation": (
            "Noncommutativity does not prevent closure: independently selected "
            "permutations still compose to one of 24 maps. This counts final "
            "readings only; an entire sequence of intermediate readings is a "
            "different target."
        ),
    }


def fixed_key_public_update() -> dict:
    width = 8
    keys = range(1 << width)
    challenges = range(1 << width)
    roundtrip_cases = 0
    for key in keys:
        for public_state in challenges:
            for plaintext in (0, 1):
                ciphertext = reinterpret_bit(plaintext, key, public_state)
                recovered = reinterpret_bit(ciphertext, key, public_state)
                assert recovered == plaintext
                roundtrip_cases += 1

    balanced_states = 0
    for public_state in range(1, 256):
        readings = Counter(reinterpret_bit(0, key, public_state) for key in keys)
        assert readings == {0: 128, 1: 128}
        balanced_states += 1
    assert {reinterpret_bit(1, key, 0) for key in keys} == {1}

    # Public challenges themselves do not depend on the secret in this model.
    # Thus merely receiving them never excludes or adds a secret-key candidate.
    states = [((index * 73) % 255) + 1 for index in range(64)]
    true_key = 0xA5
    ciphertext = 1
    current_readings = [reinterpret_bit(ciphertext, true_key, v) for v in states]
    reading_changes = sum(a != b for a, b in zip(current_readings, current_readings[1:]))
    all_key_current_values = {
        key: reinterpret_bit(ciphertext, key, states[0]) for key in keys
    }
    candidate_counts = [len(all_key_current_values)]
    for public_state in states[1:]:
        # One direct evaluation per retained key. No prior history is replayed.
        all_key_current_values = {
            key: reinterpret_bit(ciphertext, key, public_state) for key in all_key_current_values
        }
        candidate_counts.append(len(all_key_current_values))
    assert candidate_counts == [256] * len(states)
    assert all_key_current_values[true_key] == current_readings[-1]

    # Known plaintext/ciphertext gives one linear equation <K,v>=c XOR m.
    # Dependent rows (3 and 5) are included deliberately.
    evidence_rows = [1, 2, 3, 4, 5, 8, 16, 32, 64, 128]
    prefixes = []
    old_target_state = 3
    old_target_ciphertext = 1
    persistent_candidates = set(keys)
    old_target_original = reinterpret_bit(old_target_ciphertext, true_key, old_target_state)
    for length in range(len(evidence_rows) + 1):
        prefix = evidence_rows[:length]
        rank = gf2_rank(prefix, width)
        signatures = Counter(tuple(parity(key & v) for v in prefix) for key in keys)
        assert len(signatures) == 2 ** rank
        assert set(signatures.values()) == {2 ** (width - rank)}
        true_answers = tuple(parity(true_key & v) for v in prefix)
        candidates = {
            key for key in keys
            if tuple(parity(key & v) for v in prefix) == true_answers
        }
        assert candidates <= persistent_candidates
        persistent_candidates = candidates
        assert len(candidates) == 2 ** (width - rank)
        old_target_values = Counter(
            reinterpret_bit(old_target_ciphertext, key, old_target_state)
            for key in candidates
        )
        prefixes.append({
            "observations": length,
            "public_challenges": prefix,
            "rank": rank,
            "feasible_response_patterns": len(signatures),
            "keys_per_response_pattern": 2 ** (width - rank),
            "remaining_keys_for_example": len(candidates),
            "old_target_plaintext_distribution": dict(sorted(old_target_values.items())),
        })
        if length >= 2:
            assert set(old_target_values) == {old_target_original}
    assert persistent_candidates == {true_key}

    return {
        "model": "D(c,K,v) = c XOR parity(K AND v)",
        "width": width,
        "roundtrip_cases_exhausted": roundtrip_cases,
        "nonzero_public_states_with_128_128_balance": balanced_states,
        "zero_public_state": "D(c,K,0)=c; deliberately included as a revealing edge case",
        "public_only_sequence": {
            "length": len(states),
            "public_states": states,
            "example_key": true_key,
            "fixed_ciphertext_bit": ciphertext,
            "readings": current_readings,
            "reading_changes": reading_changes,
            "remaining_key_counts": candidate_counts,
            "receiver_direct_evaluations": len(states),
            "all_keys_direct_evaluations": 256 * len(states),
            "all_keys_naive_replay_evaluations": 256 * len(states) * (len(states) + 1) // 2,
            "cost_units": "one 8-bit parity/readout evaluation; not wall-clock benchmarks",
        },
        "known_plaintext_evidence": prefixes,
        "old_target": {
            "ciphertext": old_target_ciphertext,
            "public_state": old_target_state,
            "actual_plaintext": old_target_original,
            "first_identified_after_observations": 2,
            "remains_identified_after_later_updates": True,
        },
        "limitations": [
            "This is a linear research model, immediately broken by eight independent known-plaintext equations.",
            "A balanced single-bit marginal is not a claim of multi-message or chosen-plaintext security.",
            "The all-keys method is an explicit upper bound on attack cost, not an optimal-attack lower bound.",
            "Changing v changes the current target meaning; it cannot erase knowledge of an earlier fixed target.",
            "An arbitrary independently chosen future plaintext cannot necessarily be encoded by changing v.",
        ],
    }


def posterior_revision() -> dict:
    hypotheses = set(range(10))
    labels = {h: int(h in (4, 5)) for h in hypotheses}
    event_a = set(range(6))
    event_b = {0, 4, 5}
    assert event_b <= event_a <= hypotheses

    def summarize(group: set[int]) -> dict:
        counts = [sum(labels[h] == value for h in group) for value in (0, 1)]
        posterior = [str(Fraction(count, len(group))) for count in counts]
        map_value = 0 if counts[0] >= counts[1] else 1
        return {
            "hypotheses": sorted(group),
            "candidate_count": len(group),
            "message_counts": counts,
            "posterior_probabilities": posterior,
            "map_value": map_value,
            "message_entropy_bits": entropy_counts(counts),
        }

    prior = summarize(hypotheses)
    after_a = summarize(event_a)
    after_b = summarize(event_b)
    assert after_a["message_counts"] == [4, 2]
    assert after_b["message_counts"] == [1, 2]
    assert after_a["map_value"] == 0 and after_b["map_value"] == 1
    assert after_a["message_entropy_bits"] > prior["message_entropy_bits"]

    partitions = [
        [hypotheses],
        [event_a, hypotheses - event_a],
        [event_b, event_a - event_b, hypotheses - event_a],
    ]
    expectation_rows = []
    for partition in partitions:
        mean_entropy = sum(
            len(group) / len(hypotheses) * summarize(group)["message_entropy_bits"]
            for group in partition
        )
        expectation_rows.append({
            "partition": [sorted(group) for group in partition],
            "conditional_entropy_bits": mean_entropy,
        })
    assert all(
        b["conditional_entropy_bits"] <= a["conditional_entropy_bits"] + 1e-12
        for a, b in zip(expectation_rows, expectation_rows[1:])
    )

    true_hypothesis = 4
    premature_commitment = {h for h in event_a if labels[h] == after_a["map_value"]}
    later_survivors_after_commitment = premature_commitment & event_b
    assert true_hypothesis not in premature_commitment
    assert true_hypothesis in event_a & event_b
    assert later_survivors_after_commitment == {0}
    return {
        "prior": prior,
        "observed_path_A": after_a,
        "observed_path_B_nested_in_A": after_b,
        "expected_entropies": expectation_rows,
        "all_hypotheses_retained": {
            "candidate_sizes_on_observed_path": [10, 6, 3],
            "true_hypothesis": true_hypothesis,
            "truth_remains_possible": True,
            "update_from_A_to_B": "delete hypotheses 1, 2, 3; no resurrected or newly created hypothesis",
        },
        "premature_single_message_commitment": {
            "committed_message_after_A": after_a["map_value"],
            "retained_hypotheses": sorted(premature_commitment),
            "retained_after_B": sorted(later_survivors_after_commitment),
            "truth_was_lost": True,
        },
        "interpretation": (
            "The MAP interpretation reverses while the exact feasible set shrinks. "
            "Conditional entropy decreases in expectation; its value along one "
            "realized observation can increase. Forced restart applies to an "
            "observer that discarded alternatives, not automatically to an "
            "observer retaining all feasible hypotheses."
        ),
    }


def wide_change_small_choice() -> dict:
    size = 4096
    fixed_ciphertext = tuple(parity(i) for i in range(size))
    outputs = {u: tuple(bit ^ u for bit in fixed_ciphertext) for u in (0, 1)}
    changed_positions = sum(a != b for a, b in zip(outputs[0], outputs[1]))
    assert changed_positions == size
    assert len(set(outputs.values())) == 2
    requested_arbitrary_output = (0,) * size
    assert requested_arbitrary_output not in outputs.values()
    return {
        "ciphertext_bits": size,
        "update_bits": 1,
        "model": "current reading = C XOR (u repeated 4096 times)",
        "positions_changed_by_toggling_u": changed_positions,
        "possible_current_readings": len(set(outputs.values())),
        "maximum_uncertainty_due_to_u_bits": 1,
        "lazy_descriptor_update_bits": 1,
        "full_output_materialization_bits": size,
        "example_unreachable_requested_plaintext": "4096 zero bits",
        "interpretation": (
            "Many changed output positions do not imply many possible readings. "
            "The one-bit control selects only two strings and cannot transmit an "
            "arbitrary new 4096-bit message. If the bit is public its uncertainty "
            "is zero; if genuinely secret, its uncertainty is at most one bit."
        ),
    }


def preshared_lookup_table() -> dict:
    """Small public selections access a larger secret installed in advance."""
    alphabet_size = 4
    slots = 4
    tables = tuple(product(range(alphabet_size), repeat=slots))
    assert len(tables) == 256
    ciphertext = 2
    rows = []
    table_prefix_cases = 0
    uniform_unobserved_slot_checks = 0
    known_slot_checks = 0
    for observed_slots in range(slots + 1):
        expected_remaining = 4 ** (slots - observed_slots)
        counts = Counter(table[:observed_slots] for table in tables)
        assert len(counts) == 4 ** observed_slots
        assert set(counts.values()) == {expected_remaining}
        for true_table in tables:
            candidates = [
                table for table in tables
                if table[:observed_slots] == true_table[:observed_slots]
            ]
            assert len(candidates) == expected_remaining
            table_prefix_cases += 1
            for slot in range(slots):
                readings = Counter(ciphertext ^ table[slot] for table in candidates)
                if slot < observed_slots:
                    assert readings == {ciphertext ^ true_table[slot]: expected_remaining}
                    known_slot_checks += 1
                else:
                    assert readings == {value: expected_remaining // 4 for value in range(4)}
                    uniform_unobserved_slot_checks += 1
        rows.append({
            "revealed_distinct_slots": observed_slots,
            "consistent_secret_tables": expected_remaining,
            "remaining_secret_table_entropy_bits": 2 * (slots - observed_slots),
            "unknown_slot_distribution": None if observed_slots == slots else {
                str(value): "1/4" for value in range(4)
            },
        })
    constant_table = (0, 0, 0, 0)
    reachable_outputs = {ciphertext ^ constant_table[slot] for slot in range(slots)}
    assert reachable_outputs == {ciphertext}
    return {
        "model": "D(c,table,slot) = c XOR table[slot]",
        "secret_table_count": len(tables),
        "secret_table_bits_in_advance": 8,
        "public_selection_bits_per_update": 2,
        "receiver_lookups_per_update": 1,
        "fixed_ciphertext_symbol": ciphertext,
        "all_table_prefix_cases_checked": table_prefix_cases,
        "uniform_unobserved_slot_checks": uniform_unobserved_slot_checks,
        "known_slot_checks": known_slot_checks,
        "rows": rows,
        "constant_table_counterexample": {
            "table": constant_table,
            "reachable_plaintexts": sorted(reachable_outputs),
            "arbitrary_new_plaintext_possible": False,
        },
        "interpretation": (
            "A two-bit public choice can select one entry from an eight-bit "
            "secret installed in advance. A fresh independent slot remains "
            "uniform after other entries are learned; revisiting a known slot "
            "does not restore secrecy. Low online cost therefore need not mean "
            "low total secret-distribution cost. This is a secret-table "
            "reinterpretation model, not general chosen-message encryption."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("results.json"))
    args = parser.parse_args()
    result = {
        "purpose": "Finite models of changing interpretations; not a deployable cryptosystem",
        "method": "Deterministic exact finite enumeration; no random samples",
        "verification_status": "All assertions passed",
        "permutation_collapse": permutation_collapse(),
        "fixed_key_public_update": fixed_key_public_update(),
        "posterior_revision": posterior_revision(),
        "wide_change_small_choice": wide_change_small_choice(),
        "preshared_lookup_table": preshared_lookup_table(),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps({
        "status": result["verification_status"],
        "output": str(args.output.resolve()),
        "permutation_histories_directly_checked": result["permutation_collapse"]["direct_comparison_histories"],
        "bit_roundtrip_cases": result["fixed_key_public_update"]["roundtrip_cases_exhausted"],
        "known_plaintext_prefixes_checked": len(result["fixed_key_public_update"]["known_plaintext_evidence"]),
        "wide_change": result["wide_change_small_choice"]["positions_changed_by_toggling_u"],
        "secret_table_prefix_cases": result["preshared_lookup_table"]["all_table_prefix_cases_checked"],
    }, ensure_ascii=False))


if __name__ == "__main__":
    main()
