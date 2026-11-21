#!/usr/bin/env python3
"""Exact query-budget model for retroactive interpretation by column parity.

A public table has M columns and N mutually independent uniform bits per
column. An adversary may keep unlimited memory and perform unlimited free
computation, but learning one table bit costs one oracle query. Before the
public, independent uniform column choice J, it gets at most p queries;
afterward it gets at most q more. The task is to guess parity(column J).

This is an oracle query model, not a secure encryption implementation or a
wall-clock lower bound. All bits are public and can be retained indefinitely.
The distinction is between retaining the opaque table and probing its bits.
An honest party that precomputes all answers pays for generating/reading
N*M table bits and storing the results; that work is not free.

Run with Python 3.10+ and assertions enabled:
    python3 parity_probe_model.py --output parity_probe_results.json
Only Python's standard library is required. All optimization uses Fraction.
"""

from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
from functools import cache
import json
from pathlib import Path


if not __debug__:
    raise RuntimeError("Run without -O: these verification experiments require assertions.")


HALF = Fraction(1, 2)
ONE = Fraction(1)


def fraction_record(value: Fraction) -> dict:
    return {
        "exact": str(value),
        "numerator": value.numerator,
        "denominator": value.denominator,
        "decimal_for_display": float(value),
    }


def claimed_optimum(n: int, m: int, p: int, q: int) -> Fraction:
    """Formula to test, kept separate from both optimization algorithms."""
    if n <= 0 or m <= 0 or p < 0 or q < 0:
        raise ValueError("Require N,M positive and p,q nonnegative.")
    if q >= n:
        return ONE
    return HALF + Fraction(min(m, p // (n - q)), 2 * m)


class FullValueAdaptiveDP:
    """Optimize every deterministic adaptive decision by finite Bellman DP.

    State retains both known positions and their observed 0/1 values.
    Every unknown bit is an allowed next query, even outside the selected
    column in the online stage. Both equiprobable outcomes are evaluated.
    Stopping and making the best immediate guess is always allowed.

    Repeating a known query cannot help and is omitted. Randomization cannot
    improve the optimum because its expected payoff is a convex combination
    of deterministic choices. This DP does not enumerate every syntax tree;
    it merges subproblems having identical sufficient information.
    """

    def __init__(self, n: int, m: int):
        self.n, self.m = n, m
        self.bits = n * m
        self.full_mask = (1 << self.bits) - 1
        self.column_masks = tuple(((1 << n) - 1) << (n * j) for j in range(m))

    def immediate_success(self, mask: int, column: int) -> Fraction:
        target = self.column_masks[column]
        return ONE if mask & target == target else HALF

    @cache
    def online(self, mask: int, values: int, column: int, remaining: int) -> tuple[Fraction, int | None]:
        assert values & ~mask == 0
        best = self.immediate_success(mask, column)
        action = None
        if not remaining or best == ONE:
            return best, action
        for bit in range(self.bits):
            probe = 1 << bit
            if mask & probe:
                continue
            updated_mask = mask | probe
            after_zero = self.online(updated_mask, values, column, remaining - 1)[0]
            after_one = self.online(updated_mask, values | probe, column, remaining - 1)[0]
            value = (after_zero + after_one) / 2
            if value > best:
                best, action = value, bit
        return best, action

    @cache
    def offline(self, mask: int, values: int, remaining: int, online_budget: int) -> tuple[Fraction, int | None]:
        assert values & ~mask == 0
        # Stopping offline lets J be sampled uniformly independently of this
        # transcript. J is not available to any earlier decision.
        best = sum(
            (self.online(mask, values, j, online_budget)[0] for j in range(self.m)),
            Fraction(0),
        ) / self.m
        action = None
        if not remaining or best == ONE:
            return best, action
        for bit in range(self.bits):
            probe = 1 << bit
            if mask & probe:
                continue
            updated_mask = mask | probe
            after_zero = self.offline(updated_mask, values, remaining - 1, online_budget)[0]
            after_one = self.offline(updated_mask, values | probe, remaining - 1, online_budget)[0]
            value = (after_zero + after_one) / 2
            if value > best:
                best, action = value, bit
        return best, action

    def replay_every_table_and_column(self, p: int, q: int) -> dict:
        """Replay the optimized policy on all 2^(N*M) tables and all M choices."""
        successes = 0
        trials = (1 << self.bits) * self.m
        offline_query_counts: Counter = Counter()
        online_query_counts: Counter = Counter()
        maximum_covered_columns = 0
        maximum_offline_queries = 0
        maximum_online_queries = 0
        for table in range(1 << self.bits):
            mask = values = used_offline = 0
            remaining = p
            while True:
                _, action = self.offline(mask, values, remaining, q)
                if action is None:
                    break
                probe = 1 << action
                assert not mask & probe
                mask |= probe
                values |= table & probe
                remaining -= 1
                used_offline += 1
            assert used_offline <= p
            offline_query_counts[used_offline] += 1
            maximum_offline_queries = max(maximum_offline_queries, used_offline)
            if q < self.n:
                covered = sum(
                    (mask & target).bit_count() >= self.n - q
                    for target in self.column_masks
                )
                assert covered <= min(self.m, p // (self.n - q))
            else:
                covered = self.m
            maximum_covered_columns = max(maximum_covered_columns, covered)

            for column, target in enumerate(self.column_masks):
                online_mask, online_values = mask, values
                remaining_online = q
                used_online = 0
                while True:
                    _, action = self.online(online_mask, online_values, column, remaining_online)
                    if action is None:
                        break
                    probe = 1 << action
                    assert not online_mask & probe
                    online_mask |= probe
                    online_values |= table & probe
                    remaining_online -= 1
                    used_online += 1
                assert used_online <= q
                online_query_counts[used_online] += 1
                maximum_online_queries = max(maximum_online_queries, used_online)
                if online_mask & target == target:
                    guess = (online_values & target).bit_count() & 1
                else:
                    guess = 0  # Either fixed guess attains 1/2 for an unknown parity.
                true_parity = (table & target).bit_count() & 1
                successes += guess == true_parity

        empirical_exact = Fraction(successes, trials)
        optimized_exact = self.offline(0, 0, p, q)[0]
        assert empirical_exact == optimized_exact
        return {
            "table_count": 1 << self.bits,
            "column_choices_per_table": self.m,
            "trials": trials,
            "successes": successes,
            "success_probability": fraction_record(empirical_exact),
            "maximum_offline_queries": maximum_offline_queries,
            "maximum_online_queries": maximum_online_queries,
            "maximum_covered_columns_before_J": maximum_covered_columns,
            "offline_query_count_histogram_over_tables": dict(sorted(offline_query_counts.items())),
            "online_query_count_histogram_over_table_J_pairs": dict(sorted(online_query_counts.items())),
        }


class SymmetryMaskDP:
    """Independent DP on exact orbits of known masks.

    The unknown bits remain independent fair coins for every adaptive query
    transcript. Observed values therefore do not affect the optimum success
    probability. Permuting columns or bit positions within each column is a
    symmetry. A sorted tuple of known-bit counts identifies a mask orbit.

    In the online stage, the target's known count is distinguished; the other
    columns remain interchangeable. All distinct query actions, including
    useless probes into other columns, are considered. No optimum formula is
    called inside either recurrence.
    """

    def __init__(self, n: int, m: int):
        self.n, self.m = n, m

    @cache
    def online(self, target_known: int, other_counts: tuple[int, ...], remaining: int) -> Fraction:
        best = ONE if target_known == self.n else HALF
        if not remaining or best == ONE:
            return best
        if target_known < self.n:
            best = max(best, self.online(target_known + 1, other_counts, remaining - 1))
        for index, count in enumerate(other_counts):
            if count == self.n or (index and count == other_counts[index - 1]):
                continue
            updated = list(other_counts)
            updated[index] += 1
            best = max(best, self.online(target_known, tuple(sorted(updated)), remaining - 1))
        return best

    @cache
    def offline(self, counts: tuple[int, ...], remaining: int, online_budget: int) -> Fraction:
        best = sum((
            self.online(count, counts[:index] + counts[index + 1:], online_budget)
            for index, count in enumerate(counts)
        ), Fraction(0)) / self.m
        if not remaining or best == ONE:
            return best
        for index, count in enumerate(counts):
            if count == self.n or (index and count == counts[index - 1]):
                continue
            updated = list(counts)
            updated[index] += 1
            best = max(best, self.offline(tuple(sorted(updated)), remaining - 1, online_budget))
        return best


def exhaustive_small_model() -> dict:
    n, m = 3, 2
    full = FullValueAdaptiveDP(n, m)
    compressed = SymmetryMaskDP(n, m)
    cases = []
    total_replays = 0
    for q in range(n + 1):
        for p in range(n * m + 1):
            optimum = full.offline(0, 0, p, q)[0]
            compressed_optimum = compressed.offline((0,) * m, p, q)
            prediction = claimed_optimum(n, m, p, q)
            assert optimum == prediction == compressed_optimum
            replay = full.replay_every_table_and_column(p, q)
            assert replay["success_probability"]["exact"] == str(prediction)
            total_replays += replay["trials"]
            cases.append({
                "p": p, "q": q,
                "optimal_success_probability": fraction_record(optimum),
                "formula_match": True,
                "mask_symmetry_DP_match": True,
                "policy_replay": replay,
            })
    return {
        "N": n, "M": m,
        "strategy_optimization": "Full observed-mask-and-values adaptive Bellman DP",
        "budget_case_count": len(cases),
        "p_range_inclusive": [0, n * m],
        "q_range_inclusive": [0, n],
        "table_count_per_case": 1 << (n * m),
        "total_replayed_table_J_pairs_across_budget_cases": total_replays,
        "offline_DP_cached_states": full.offline.cache_info().currsize,
        "online_DP_cached_states": full.online.cache_info().currsize,
        "cases": cases,
    }


def symmetry_compressed_larger_model() -> dict:
    n, m = 4, 3
    # @cache on a method is shared across instances; subtract previously
    # cached small-model entries when reporting this model's state counts.
    offline_state_baseline = SymmetryMaskDP.offline.cache_info().currsize
    online_state_baseline = SymmetryMaskDP.online.cache_info().currsize
    compressed = SymmetryMaskDP(n, m)
    cases = []
    for q in range(n + 1):
        for p in range(n * m + 1):
            optimum = compressed.offline((0,) * m, p, q)
            prediction = claimed_optimum(n, m, p, q)
            assert optimum == prediction
            cases.append({
                "p": p, "q": q,
                "optimal_success_probability": fraction_record(optimum),
                "formula_match": True,
            })
    return {
        "N": n, "M": m,
        "strategy_optimization": "Exact symmetry quotient of known-mask DP; observed values omitted by fair-bit symmetry",
        "budget_case_count": len(cases),
        "p_range_inclusive": [0, n * m],
        "q_range_inclusive": [0, n],
        "all_tables_replayed": False,
        "offline_DP_cached_states": compressed.offline.cache_info().currsize - offline_state_baseline,
        "online_DP_cached_states": compressed.online.cache_info().currsize - online_state_baseline,
        "cases": cases,
    }


def illustrative_formula_predictions() -> dict:
    n, m = 1024, 256
    budgets = [
        (0, 0), (0, 1023), (1, 1023), (128, 1023), (256, 1023),
        (1024, 0), (131072, 0), (262144, 0),
        (65536, 512), (131072, 512), (0, 1024),
    ]
    return {
        "N": n, "M": m,
        "method": "Formula evaluation only; these large instances were not optimized or table-enumerated",
        "public_index_bits": 8,
        "table_bits": n * m,
        "table_bytes": n * m // 8,
        "all_column_parity_cache_bits": m,
        "honest_full_preprocessing_bit_generation_or_read_cost": n * m,
        "predictions": [{
            "p": p, "q": q,
            "predicted_optimal_success_probability": fraction_record(claimed_optimum(n, m, p, q)),
        } for p, q in budgets],
    }


def expected_budget_counterexample() -> dict:
    """An expected preprocessing budget cannot replace the per-branch cap."""
    n = m = 2
    successes = trials = total_queries = 0
    query_counts: Counter = Counter()
    for table in range(1 << (n * m)):
        for coin in (0, 1):
            # Flip before J. On heads, probe both bits of column zero;
            # on tails, do no work. Store all revealed values permanently.
            mask = 0b0011 if coin else 0
            queries = 2 if coin else 0
            for column in range(m):
                target = 0b0011 << (n * column)
                guess = (table & target).bit_count() & 1 if mask & target == target else 0
                truth = (table & target).bit_count() & 1
                successes += guess == truth
                trials += 1
                total_queries += queries
                query_counts[queries] += 1
    actual_success = Fraction(successes, trials)
    expected_queries = Fraction(total_queries, trials)
    per_branch_cap_formula = claimed_optimum(n, m, 1, 0)
    independent_mixture = HALF * Fraction(3, 4) + HALF * HALF
    assert trials == 64 and successes == 40
    assert expected_queries == 1
    assert actual_success == independent_mixture == Fraction(5, 8)
    assert per_branch_cap_formula == HALF < actual_success
    return {
        "N": n, "M": m, "q": 0,
        "randomized_strategy": "Before J, with probability 1/2 probe both bits of column 0; otherwise probe nothing",
        "tables_enumerated": 16,
        "J_choices": 2,
        "coin_choices": 2,
        "total_table_J_coin_cases": trials,
        "successes": successes,
        "expected_offline_queries": fraction_record(expected_queries),
        "maximum_offline_queries_on_a_branch": max(query_counts),
        "query_count_histogram": dict(sorted(query_counts.items())),
        "actual_success_probability": fraction_record(actual_success),
        "formula_with_a_hard_p1_cap": fraction_record(per_branch_cap_formula),
        "interpretation": (
            "The theorem assumes at most p probes on every realized branch. "
            "An expected budget E[p]=1 permits two probes on half the branches "
            "and achieves 5/8 rather than the hard-cap-p=1 optimum 1/2. "
            "This does not contradict the theorem: the strategy violates its "
            "per-branch budget constraint."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("parity_probe_results.json"))
    args = parser.parse_args()
    small = exhaustive_small_model()
    larger = symmetry_compressed_larger_model()
    result = {
        "title": "Parity-probe model with independent public column update",
        "verification_status": "All exact assertions passed",
        "arithmetic": "fractions.Fraction throughout optimization and comparisons; decimal display only",
        "random_samples": 0,
        "model_assumptions": [
            "The table has M*N mutually independent uniform bits; its prior is public.",
            "One oracle query reveals one selected table bit and costs one unit.",
            "The adversary retains every observed bit and all opaque raw data; memory and other computation are unlimited.",
            "Opaque storage does not itself evaluate the table bits in this query model.",
            "At most p probes precede J, and at most q follow J.",
            "J is uniform on the M columns and independent of preprocessing, table contents, and adversarial randomness.",
            "The goal is parity of column J; it changes with J and is not a previously fixed message.",
            "No independent plaintext authentication or other side information is supplied.",
            "Repeated probes of already known bits are omitted as dominated actions.",
        ],
        "formula": {
            "when_q_lt_N": "1/2 + min(M, floor(p/(N-q)))/(2*M)",
            "when_q_ge_N": "1",
        },
        "proof_outline": [
            "Conditioned on any adaptive query transcript, every unqueried bit is still an independent fair bit.",
            "A column with even one unknown bit has uniform parity, so a best guess succeeds with probability 1/2.",
            "For q<N, a column can be completed online only if at least N-q of its bits were already probed.",
            "On every offline decision-tree branch, at most min(M, floor(p/(N-q))) columns meet that condition.",
            "Because J is independent and uniform, even all adaptive strategies average at most 1/2 plus half that covered-column fraction.",
            "Achieve the bound by probing exactly N-q bits in each of k=min(M,floor(p/(N-q))) columns, completing the chosen column online when it is covered, and guessing otherwise.",
            "For q>=N, probe every bit of the chosen column after J and answer perfectly.",
        ],
        "small_full_adaptive_DP": small,
        "larger_symmetry_DP": larger,
        "large_illustrations": illustrative_formula_predictions(),
        "expected_budget_boundary_counterexample": expected_budget_counterexample(),
        "limitations": [
            "This is an exact oracle-query bound, not measured runtime or a lower bound in a word-RAM, SIMD, GPU, or physical memory model.",
            "N needed probes can all be issued in one parallel round; a sequential delay does not follow.",
            "An honest party's preprocessing/generation and cache costs must be counted; public data gives the attacker the same eventual opportunity.",
            "After enough preprocessing, all M answers are known and every future public column update is answered immediately.",
            "Previously learned bits are never revoked, and all preprocessing can be reused across updates.",
            "Repeated updates are not independent fresh secrecy: previously selected columns may already be cached.",
            "The column selector chooses an existing table parity and does not encode an arbitrary newly chosen message.",
            "Public bit access is deliberately metered. If reading or bulk parity of the raw table is treated as free, this claimed query advantage disappears.",
        ],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps({
        "status": result["verification_status"],
        "output": str(args.output.resolve()),
        "full_value_DP_budget_cases": small["budget_case_count"],
        "replayed_table_J_pairs": small["total_replayed_table_J_pairs_across_budget_cases"],
        "symmetry_DP_budget_cases": larger["budget_case_count"],
        "expected_budget_counterexample": result["expected_budget_boundary_counterexample"]["actual_success_probability"]["exact"],
        "full_DP_states": {
            "offline": small["offline_DP_cached_states"],
            "online": small["online_DP_cached_states"],
        },
    }, ensure_ascii=False))


if __name__ == "__main__":
    main()
