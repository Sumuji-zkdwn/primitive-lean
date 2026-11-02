from itertools import product

import pytest

from affine_belief import AffineBelief, LinearObservable, demonstrate, parity_macro, transport


def apply(state, gates):
    for control,target in gates:
        if state & (1 << control):
            state ^= 1 << target
    return state


@pytest.mark.parametrize("data_bits", range(2,7))
def test_symbolic_posterior_matches_all_small_concrete_states(data_bits):
    gates = parity_macro(data_bits)
    for left,measurement in product([0,1],repeat=2):
        original = {x for x in range(1 << data_bits) if x & 1 == left}
        actual = {apply(x,gates) for x in original}
        belief = AffineBelief(data_bits+1, [(1,left),(1 << data_bits,0)])
        observable = LinearObservable((1 << data_bits)-1)
        observable = transport(belief,observable,gates)
        assert {x for x in range(1 << (data_bits+1)) if belief.contains(x)} == actual
        assert belief.known(LinearObservable(1 << data_bits)) == 0
        actual = {x for x in actual if x & 1 == measurement}
        belief.observe(1,measurement)
        assert {x for x in range(1 << (data_bits+1)) if belief.contains(x)} == actual
        assert belief.known(observable) == measurement
        original_consistent = {apply(x,reversed(gates)) for x in actual}
        observable = transport(belief,observable,reversed(gates))
        assert {x for x in range(1 << (data_bits+1)) if belief.contains(x)} == original_consistent
        assert belief.known(observable) == measurement
        assert belief.cardinality == len(original_consistent)


def test_large_belief_is_not_enumerated_and_still_answers_the_goal():
    result = demonstrate(1000,1,0)
    assert result["remaining_affine_dimension"] == 998
    assert result["retained_independent_constraints"] == 3
    assert result["goal_value_after_restore"] == 0
    assert result["gates_round_trip"] == 3998


def test_inconsistent_observations_are_not_vacuously_certified():
    belief = AffineBelief(3,[(1,0),(1,1)])
    assert belief.inconsistent
    assert belief.cardinality == 0
    assert belief.known(LinearObservable(1)) is None


def test_data_are_not_silently_supplied_to_the_belief():
    belief = AffineBelief(4,[(1,0),(8,0)])
    target = transport(belief,LinearObservable(7),parity_macro(3))
    assert belief.known(target) is None
    assert belief.dimension == 2


def test_nonzero_scratch_requires_a_different_goal_interpretation():
    belief = AffineBelief(4,[(1,0),(8,1)])
    target = transport(belief,LinearObservable(7),parity_macro(3))
    belief.observe(1,0)
    assert belief.known(target) == 1  # Left is parity XOR incoming scratch.
