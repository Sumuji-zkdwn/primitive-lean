#!/usr/bin/env python3
"""Exact count of raw transformations preserving a finite observation partition.

Every source fiber of size m_i must be mapped into a single target fiber
of size m_j. This yields exactly sum_j (m_j ** m_i) choices for that
source fiber, independently across source fibers.

The effective quotient action is any map on r classes, hence r**r choices.
This script is a finite arithmetic/enumeration check, not a Lean proof
of the general product formula.
"""
from itertools import product
from math import prod
import argparse
import json


def normalize(sizes):
    vals = tuple(int(m) for m in sizes)
    if not vals or any(m <= 0 for m in vals):
        raise ValueError("a nonempty list of strictly positive fiber sizes is required")
    return vals


def formula(sizes):
    sizes = normalize(sizes)
    return prod(sum(target ** source for target in sizes) for source in sizes)


def effective_count(sizes):
    sizes = normalize(sizes)
    return len(sizes) ** len(sizes)


def enumerate_compatible(sizes, max_states=6):
    sizes = normalize(sizes)
    n = sum(sizes)
    if n > max_states:
        raise ValueError(f"exhaustive enumeration capped at {max_states} states")
    classes = tuple(i for i, size in enumerate(sizes) for _ in range(size))
    count = 0
    actions = set()
    for values in product(range(n), repeat=n):
        compatible = all(
            classes[values[x]] == classes[values[y]]
            for x in range(n) for y in range(n)
            if classes[x] == classes[y]
        )
        if compatible:
            count += 1
            representative = []
            start = 0
            for size in sizes:
                representative.append(classes[values[start]])
                start += size
            actions.add(tuple(representative))
    return dict(raw=count, effective=len(actions))


def report(sizes, exhaustive=True):
    sizes = normalize(sizes)
    row = dict(
        fiber_sizes=list(sizes),
        states=sum(sizes),
        initial_observation_classes=len(sizes),
        all_raw_maps=sum(sizes) ** sum(sizes),
        compatible_raw_maps=formula(sizes),
        effective_quotient_maps=effective_count(sizes),
    )
    if exhaustive:
        actual = enumerate_compatible(sizes)
        row["enumerated"] = actual
        row["checks"] = dict(
            raw_matches=actual["raw"] == row["compatible_raw_maps"],
            effective_matches=actual["effective"] == row["effective_quotient_maps"],
        )
    return row


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("fiber_sizes", nargs="*", type=int, default=[2, 1])
    parser.add_argument("--no-enumerate", action="store_true")
    a = parser.parse_args()
    print(json.dumps(report(a.fiber_sizes, not a.no_enumerate), indent=2))
if __name__ == "__main__":
    main()
