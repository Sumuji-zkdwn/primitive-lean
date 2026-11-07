"""Finite exact regression for fixed-set Stops closure counts (n <= 4).

The existing Galois checker supplies the independently enumerated Stops
relation and singleton closure. This script checks the new counting formulas
against every endomap and every realizable fixed set through four states.
"""
from itertools import product
from math import comb
from pathlib import Path
import json

from check_strange_operator_galois import polar_pair


ROOT = Path(__file__).resolve().parents[1]


def fixed_set(operator):
    return frozenset(x for x, y in enumerate(operator) if x == y)


def is_idempotent(operator):
    return all(operator[operator[x]] == operator[x] for x in range(len(operator)))


def check():
    results = {}
    closure_cases = 0
    for n in range(1, 5):
        operators = tuple(product(range(n), repeat=n))
        by_fixed_set = {}
        for operator in operators:
            by_fixed_set.setdefault(fixed_set(operator), []).append(operator)

        for mask in range(1 << n):
            fixed = frozenset(x for x in range(n) if mask & (1 << x))
            maps = by_fixed_set.get(fixed, [])
            idempotents = [operator for operator in maps if is_idempotent(operator)]
            expected_maps = (n - 1) ** (n - len(fixed))
            expected_idempotents = len(fixed) ** (n - len(fixed))
            assert len(maps) == expected_maps, (n, fixed, len(maps), expected_maps)
            assert len(idempotents) == expected_idempotents, (
                n, fixed, len(idempotents), expected_idempotents
            )

            if not maps:
                continue
            seed = maps[0]
            all_maps, _, closure = polar_pair(n, (seed,))
            closure = frozenset(closure)
            if 0 < len(fixed) < n:
                assert closure == frozenset(maps), (n, fixed, closure, maps)
                closed_idempotents = sum(is_idempotent(operator) for operator in closure)
                assert closed_idempotents == expected_idempotents
            else:
                assert closure == frozenset(all_maps), (n, fixed, len(closure), len(all_maps))
                total_idempotents = sum(is_idempotent(operator) for operator in closure)
                formula_total = sum(comb(n, r) * r ** (n - r) for r in range(n + 1))
                assert total_idempotents == formula_total
            closure_cases += 1

        results[n] = {
            "endomaps": len(operators),
            "fixed_sets_checked": 1 << n,
            "singleton_closures_checked": len(by_fixed_set),
        }

    report = {
        "passed": True,
        "checked_n": [1, 2, 3, 4],
        "closure_cases": closure_cases,
        "results": results,
        "scope": "Exact exhaustive finite regression; universal claims are separately Lean-proved.",
    }
    out = ROOT / "verification"
    out.mkdir(exist_ok=True)
    (out / "strange-operator-counting-smoke.json").write_text(
        json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
    )
    print(json.dumps(report, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    check()
