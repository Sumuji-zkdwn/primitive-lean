"""Exhaustive finite oracle: simultaneous partial assignment gluing.

All 3^4 pairs of two-coordinate, two-local partial Boolean assignments
are enumerated. Operational checks add actual reachable states and a
separate global constraint: pairwise agreement alone is insufficient.
"""
from itertools import product

VALUES = (None, False, True)
STATES = tuple(product((False, True), repeat=2))
START = (False, False)


def compatible(parts):
    return all(not (parts[0][i] is not None
                    and parts[1][i] is not None
                    and parts[0][i] != parts[1][i])
               for i in range(2))


def glue_states(parts):
    return tuple(s for s in STATES if all(
        parts[loc][i] is None or parts[loc][i] == s[i]
        for loc in range(2) for i in range(2)))


def covered(parts):
    return all(parts[0][i] is not None or parts[1][i] is not None
               for i in range(2))


def canonical(parts):
    return tuple(next((parts[loc][i]
                       for loc in range(2) if parts[loc][i] is not None),
                      False)
                 for i in range(2))


def destructive(loc, x):
    return (True, False) if loc == 0 else (False, True)


def cumulative(loc, x):
    return (True, x[1]) if loc == 0 else (x[0], True)


def closure(step):
    queue = [START]
    found = {START}
    for s in queue:
        for loc in range(2):
            s2 = step(loc, s)
            if s2 not in found:
                found.add(s2)
                queue.append(s2)
    return found


def test_exact_overlap_gluing_for_all_two_local_partial_tables():
    for raw in product(VALUES, repeat=4):
        parts = (raw[:2], raw[2:])
        possible = bool(glue_states(parts))
        assert possible == compatible(parts)
        if covered(parts) and compatible(parts):
            assert glue_states(parts) == (canonical(parts),)


def test_admissibility_and_reachability_factorization():
    options = (destructive, cumulative)
    for raw in product(VALUES, repeat=4):
        parts = (raw[:2], raw[2:])
        if not covered(parts):
            continue
        for step in options:
            reachable = closure(step)
            for accept in (lambda _: True, lambda s: not all(s)):
                operational = any(s in reachable and accept(s)
                                  for s in glue_states(parts))
                factored = (
                    compatible(parts) and
                    accept(canonical(parts)) and
                    canonical(parts) in reachable
                )
                assert operational == factored


def test_different_failure_modes_and_repair():
    separate_success_reports = ((True, None), (None, True))
    destructive_full_snapshots = (
        destructive(0, START), destructive(1, START))
    assert compatible(separate_success_reports)
    assert glue_states(separate_success_reports) == ((True, True),)
    assert not compatible(destructive_full_snapshots)
    assert not glue_states(destructive_full_snapshots)
    assert not any(not all(s) for s in glue_states(separate_success_reports))
    assert (True, True) not in closure(destructive)
    assert (True, True) in closure(cumulative)
