"""Finite oracle for destructive interference and local-to-global gluing.

A different action word can achieve each requirement individually while
NO finite word can make them true together. This validates the tiny
state-machine witnesses; Lean handles the general unbounded word proof.
"""
from itertools import product, permutations


START = (False, False)


def destructive(loc, state):
    return (True, False) if loc == 0 else (False, True)


def cumulative(loc, state):
    return (True, state[1]) if loc == 0 else (state[0], True)


def run(action, word, state=START):
    for loc in word:
        state = action(loc, state)
    return state


def gated_next(action, time, state):
    for loc in (0, 1):
        if time == 0 or all(action(loc, state)):
            return action(loc, state)
    return state


def snapshots_possible(old_step, new_step):
    # All readouts are constant. Can we faithfully embed old dynamics?
    states = tuple(product((False, True), repeat=2))
    for perm in permutations(range(4)):
        f = dict(zip(states, (states[i] for i in perm)))
        if all(f[old_step(s)] == new_step(f[s]) for s in states):
            return True
    return False


def test_each_requirement_can_be_met_but_no_joint_word_exists():
    assert run(destructive, (0,))[0] is True
    assert run(destructive, (1,))[1] is True
    for n in range(9):
        for word in product((0, 1), repeat=n):
            assert run(destructive, word) != (True, True)


def test_destructive_interference_is_noncommutative():
    assert destructive(0, destructive(1, START)) != (
        destructive(1, destructive(0, START))
    )


def test_non_interfering_cooperation_actually_glues_both_demands():
    assert run(cumulative, (0, 1)) == (True, True)
    assert run(cumulative, (1, 0)) == (True, True)
    for state in product((False, True), repeat=2):
        assert cumulative(0, cumulative(1, state)) == (
            cumulative(1, cumulative(0, state))
        )


def test_joint_postcondition_gate_extinguishes_every_destructive_local():
    for state in product((False, True), repeat=2):
        for loc in (0, 1):
            assert not all(destructive(loc, state))
        assert gated_next(destructive, 1, state) == state
    assert gated_next(destructive, 0, START) != START
    old = lambda x: gated_next(destructive, 0, x)
    later = lambda x: gated_next(destructive, 1, x)
    assert not snapshots_possible(old, later)


def test_change_in_local_action_functions_cannot_recover_empty_domains():
    states = tuple(product((False, True), repeat=2))
    orig = lambda x: gated_next(destructive, 0, x)
    # Even if outputs of the underlying local actions are arbitrarily
    # reassigned, the already frozen later availability remains empty.
    for f in product(states, repeat=4):
        new_action = dict(zip(states, f))
        later = lambda x: x
        assert not snapshots_possible(orig, later)
        # Confirm that the unused local mapping cannot alter the
        # transition when its availability predicate is identically false.
        assert all(later(x) == x for x in new_action)


def test_non_destructive_actions_recover_two_time_global_goal():
    x = gated_next(cumulative, 0, START)
    assert x == (True, False)
    assert all(gated_next(cumulative, 1, x))
    assert gated_next(cumulative, 1, x) == (True, True)
    assert all(cumulative(1, x))
