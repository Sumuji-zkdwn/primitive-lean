"""Bounded, deterministic repair synthesis from finite local acceptance tables.

This Python oracle checks the data and search contract only. The Lean source
proves the conditional extension theorem with separate hypotheses.
"""
from itertools import product


def choose_target(states, viable):
    for state in states:
        if viable(state):
            return state
    return None


def patch(start, target):
    return lambda state: target if state == start else state


def synthesis(states, locals_, accepts, start):
    target = choose_target(states, lambda state: any(
        accepts(loc, state) for loc in locals_))
    return None if target is None else patch(start, target)


def test_first_eligible_and_no_phantom_target():
    candidates = (0, 1, 2)
    assert choose_target(candidates, lambda x: x >= 1) == 1
    assert choose_target(candidates, lambda x: False) is None
    assert choose_target((), lambda x: True) is None


def test_exact_search_over_all_three_state_local_tables():
    states = (0, 1, 2)
    for candidate_flags in product((False, True), repeat=3):
        candidates = tuple(s for s, keep in zip(states, candidate_flags) if keep)
        for bits in product((False, True), repeat=6):
            table = {(l, x): bits[3 * l + x] for l in (0, 1) for x in states}
            accepts = lambda l, x: table[(l, x)]
            eligible = tuple(x for x in candidates if any(accepts(l, x) for l in (0, 1)))
            operation = synthesis(candidates, (0, 1), accepts, 1)
            if not eligible:
                assert operation is None
            else:
                assert operation is not None
                assert operation(1) == eligible[0]
                assert all(operation(x) == x for x in states if x != 1)


def test_interval_witness_and_novelty():
    candidates = (0, 1, 2)
    locals_ = (0, 1)
    accepts = lambda l, x: l == 1 and x == 2
    generated = synthesis(candidates, locals_, accepts, start=1)
    assert generated is not None and generated(1) == 2
    assert generated(0) == 0 and generated(2) == 2
    old_action = lambda x: x
    assert all(old_action(1) != generated(1) for _ in range(10))

    # Time 0: local 0 accepts 1. Time 1: only local 1 accepts 2.
    assert (0, 1) == (0, 1)
    assert accepts(1, generated(1))
    observer = lambda x: 0 if x in (0, 1) else 1
    assert observer(0) == observer(1)
    assert observer(generated(0)) != observer(generated(1))


def test_one_local_extinction_does_not_force_extension():
    # New local component 1 can support the unchanged state 1.
    old_action = lambda x: x
    accepts = lambda loc, x: loc == 1 and x == 1
    generated = synthesis((0, 1, 2), (1,), accepts, 1)
    assert old_action(1) == 1
    assert generated is not None and generated(1) == 1
    # A generated operator can be redundant even when a local system died.
    assert all(generated(x) == old_action(x) for x in (0, 1, 2))
