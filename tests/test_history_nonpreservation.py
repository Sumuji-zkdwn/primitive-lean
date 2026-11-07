"""Finite reference tests for historical nonpreservation, not for a conservation axiom.

Historical preservation means an injective state representation preserving
the readout AND the deterministic successor relation. Explicit enumerations
confirm two independent obstructions and the difference between internal
repair and adding a tagged copy of a lost history.
"""
from itertools import product


def embeddings(old_obs, old_next, new_obs, new_next, dynamics=True):
    n, m = len(old_obs), len(new_obs)
    for f in product(range(m), repeat=n):
        if len(set(f)) != n:
            continue
        if any(new_obs[f[x]] != old_obs[x] for x in range(n)):
            continue
        if dynamics and any(f[old_next[x]] != new_next[f[x]] for x in range(n)):
            continue
        yield f


def test_global_growth_does_not_preserve_lost_label():
    old_obs = (0, 1)
    later_obs = (1, 2, 3, 3)
    assert len(later_obs) > len(old_obs)
    assert len(set(later_obs)) > len(set(old_obs))
    assert not tuple(embeddings(old_obs, (0, 1), later_obs, (0, 1, 2, 3)))
    assert 0 in set(old_obs) and 0 not in set(later_obs)


def test_arbitrary_new_transitions_and_readout_repairs_cannot_recover_label():
    old_obs, later_obs = (0, 1), (1, 2, 3, 3)
    old_next = (0, 1)
    for later_next in product(range(4), repeat=4):
        assert not tuple(embeddings(old_obs, old_next, later_obs, later_next))
        # A state-transformer before observing still only reaches old labels.
        transformed_labels = {later_obs[later_next[y]] for y in range(4)}
        assert 0 not in transformed_labels


def test_current_snapshot_can_survive_while_history_fails():
    constant_obs = (0, 0)
    flip = (1, 0)
    stationary = (0, 1)
    assert tuple(embeddings(constant_obs, flip,
                            constant_obs, stationary, dynamics=False))
    assert not tuple(embeddings(constant_obs, flip,
                                constant_obs, stationary))


def test_one_step_criterion_with_injective_target_readout():
    # For an injective later observer, matching the observed successor
    # is equivalent to matching the actual successor for every candidate map.
    old_obs = (0, 1)
    new_obs = (0, 1, 2)
    for old_next in product(range(2), repeat=2):
        for new_next in product(range(3), repeat=3):
            exact = tuple(embeddings(old_obs, old_next, new_obs, new_next))
            obs_step = []
            for f in product(range(3), repeat=2):
                if len(set(f)) < 2:
                    continue
                if all(new_obs[f[x]] == old_obs[x] for x in range(2)) and all(
                    new_obs[f[old_next[x]]] ==
                    new_obs[new_next[f[x]]] for x in range(2)
                ):
                    obs_step.append(f)
            assert exact == tuple(obs_step)


def test_actual_extension_can_restore_a_lost_history():
    old_obs, old_next = (0, 1), (0, 1)
    later_obs, later_next = (1, 2, 3, 3), (0, 1, 2, 3)
    sum_obs = old_obs + later_obs
    sum_next = old_next + tuple(x + len(old_obs) for x in later_next)
    injections = tuple(embeddings(old_obs, old_next, sum_obs, sum_next))
    assert (0, 1) in injections
    assert not tuple(embeddings(old_obs, old_next, later_obs, later_next))
