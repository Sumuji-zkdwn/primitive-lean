#!/usr/bin/env python3
"""Toy arithmetic audit for a trapdoor repeated-squaring evaluation.

All moduli here are trivially factorable and deliberately public examples.
This program proves no time-lock security. It verifies arithmetic agreement,
cache reuse, public algebraic relations, and finite-state cycles.
Python 3.10+, standard library only.
"""

from __future__ import annotations

from math import gcd
from pathlib import Path
import json

if not __debug__:
    raise RuntimeError("Verification requires assertions: do not use Python optimization.")


def sequential_square(base: int, steps: int, modulus: int) -> int:
    value = base % modulus
    for _ in range(steps):
        value = value * value % modulus
    return value


def counted_power(base: int, exponent: int, modulus: int) -> tuple[int, int]:
    """Left-to-right binary exponentiation; count modular multiplications.

    A deliberately simple shared implementation. Initialization with the
    leading one saves redundant operations; exponents 0 and 1 cost zero.
    """
    assert exponent >= 0
    if exponent == 0:
        return 1 % modulus, 0
    answer = base % modulus
    operations = 0
    for bit in bin(exponent)[3:]:
        answer = answer * answer % modulus
        operations += 1
        if bit == "1":
            answer = answer * base % modulus
            operations += 1
    assert answer == pow(base, exponent, modulus)
    return answer, operations


def fast_with_factors(base: int, steps: int, p: int, q: int) -> tuple[int, dict]:
    modulus = p * q
    assert p != q and gcd(base, modulus) == 1
    phi = (p - 1) * (q - 1)
    reduced, exponent_cost = counted_power(2, steps, phi)
    answer, group_cost = counted_power(base, reduced, modulus)
    return answer, {
        "reduced_exponent": reduced,
        "multiplications_mod_phi": exponent_cost,
        "multiplications_mod_N": group_cost,
        "nominal_total_multiplications": exponent_cost + group_cost,
    }


def find_cycle(base: int, modulus: int) -> dict:
    seen: dict[int, int] = {}
    values: list[int] = []
    value = base % modulus
    while value not in seen:
        seen[value] = len(values)
        values.append(value)
        value = value * value % modulus
    start = seen[value]
    return {
        "preperiod": start,
        "period": len(values) - start,
        "unique_values_before_repeat": len(values),
        "values": values,
    }


def verify() -> dict:
    pairs = [(11, 19), (17, 23)]
    arithmetic_cases = 0
    reversible_reading_cases = 0
    cache_identity_cases = 0
    relation_cases = 0
    sample_cost_rows = []
    for p, q in pairs:
        n = p * q
        units = [a for a in range(1, n) if gcd(a, n) == 1]
        assert len(units) == (p - 1) * (q - 1)
        old_symbol = 3
        assert gcd(old_symbol, n) == 1
        inverse_symbol = pow(old_symbol, -1, n)
        for a in units:
            # The reference sequence advances one step at a time; its values
            # are compared with the independently reduced exponent method.
            value = a
            for steps in range(65):
                fast, _ = fast_with_factors(a, steps, p, q)
                assert fast == value
                arithmetic_cases += 1
                current_reading = old_symbol * value % n
                assert inverse_symbol * current_reading % n == value
                reversible_reading_cases += 1
                if steps in (0, 1, 5, 16, 64):
                    for delta in (0, 1, 2, 7):
                        assert sequential_square(value, delta, n) == sequential_square(a, steps + delta, n)
                        cache_identity_cases += 1
                    for exponent in (1, 2, 3, 5, 17):
                        related_base = pow(a, exponent, n)
                        assert sequential_square(related_base, steps, n) == pow(value, exponent, n)
                        relation_cases += 1
                value = value * value % n

    p, q, a = 1019, 1231, 2
    n = p * q
    assert gcd(a, n) == 1
    for steps in (1, 4, 16, 64, 256, 1024, 4096, 16384):
        direct = sequential_square(a, steps, n)
        fast, cost = fast_with_factors(a, steps, p, q)
        assert direct == fast
        sample_cost_rows.append({
            "steps": steps,
            "sequential_mod_N_squarings": steps,
            "answer": direct,
            **cost,
        })

    # A public delay counter is not a reset: retain the last endpoint.
    epochs = list(range(64, 257, 64))
    value, last_t, cached_cost = a, 0, 0
    epoch_rows = []
    for steps in epochs:
        delta = steps - last_t
        value = sequential_square(value, delta, n)
        cached_cost += delta
        assert value == sequential_square(a, steps, n)
        epoch_rows.append({
            "target_steps": steps,
            "new_squarings_needed_from_previous_endpoint": delta,
            "cumulative_cached_squarings": cached_cost,
            "answer": value,
        })
        last_t = steps
    assert cached_cost == max(epochs) == 256
    assert sum(epochs) == 640

    # New-looking bases can still have a public cheap relation.
    steps, exponent = 1024, 3
    z = sequential_square(a, steps, n)
    related_base = pow(a, exponent, n)
    related_answer, relation_cost = counted_power(z, exponent, n)
    assert related_answer == sequential_square(related_base, steps, n)
    assert relation_cost == 2

    cycle = find_cycle(2, 209)
    huge_t = 10**6
    if huge_t < len(cycle["values"]):
        from_cycle = cycle["values"][huge_t]
    else:
        index = cycle["preperiod"] + (huge_t - cycle["preperiod"]) % cycle["period"]
        from_cycle = cycle["values"][index]
    from_factors, _ = fast_with_factors(2, huge_t, 11, 19)
    assert from_cycle == from_factors

    return {
        "purpose": "Toy arithmetic/caching checks, not a secure cryptosystem or delay lower bound",
        "all_assertions_passed": True,
        "assumptions": [
            "p and q are distinct primes; inputs lie in Z_N^*",
            "The factors are public tiny test inputs; security is deliberately absent",
            "Counts describe these algorithms, not the fastest possible attacks",
        ],
        "exhaustive_arithmetic": {
            "prime_pairs": pairs,
            "T_range_inclusive": [0, 64],
            "all_unit_base_and_T_cases": arithmetic_cases,
            "invertible_current_reading_cases": reversible_reading_cases,
            "cache_semigroup_identity_cases": cache_identity_cases,
            "related_base_identity_cases": relation_cases,
        },
        "sample_costs": {
            "p": p, "q": q, "N": n, "base": a,
            "cost_units": "modular multiplications; mod phi and mod N reported separately",
            "rows": sample_cost_rows,
        },
        "monotone_target_cache": {
            "rows": epoch_rows,
            "restart_cost": sum(epochs),
            "cached_cost": cached_cost,
        },
        "public_related_base_counterexample": {
            "T": steps,
            "base": a,
            "new_base": related_base,
            "public_exponent": exponent,
            "previous_answer": z,
            "new_answer": related_answer,
            "additional_multiplications_from_previous_answer": relation_cost,
            "naive_restart_squarings": steps,
        },
        "tiny_modulus_cycle_counterexample": {
            "N": 209, "base": 2, **cycle,
            "target_T": huge_t,
            "endpoint_from_cycle": from_cycle,
            "note": "A small state space makes generic cycle enumeration easy; toy timings are not security estimates",
        },
        "limitations": [
            "No bound on arbitrary attackers, factoring, preprocessing, parallel or quantum algorithms is proved here",
            "Hardness of computing the full endpoint is not automatically unpredictability of an arbitrary output bit",
            "A full encryption protocol, authenticated update, and message-recovery security are not implemented",
        ],
        "retroactive_reading_definition": {
            "model": "M_T = C * z_T(a) mod N, for a fixed public unit C",
            "inverse": "z_T(a) = inverse(C) * M_T mod N",
            "consequence": "Full endpoint recovery and full current-reading recovery differ by one cheap invertible map",
            "caveat": "No claim about hiding arbitrary messages, partial bits, or semantic security",
        },
    }


if __name__ == "__main__":
    result = verify()
    output = Path(__file__).with_name("repeated_squaring_results.json")
    output.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "status": "passed",
        "arithmetic_cases": result["exhaustive_arithmetic"]["all_unit_base_and_T_cases"],
        "cache_identity_cases": result["exhaustive_arithmetic"]["cache_semigroup_identity_cases"],
        "related_base_cases": result["exhaustive_arithmetic"]["related_base_identity_cases"],
        "output": str(output),
    }, ensure_ascii=False))
