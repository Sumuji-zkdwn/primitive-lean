"""Exhaustive two-coordinate, three-value partial-write gluing oracle.

Each local patch writes True, False, or nothing to each coordinate.
For every family of up to four patches, compatibility on overlaps is
equivalent to the existence of a global realization. The implementation
also checks the constructive first-write merge and preservation of
untouched base coordinates.
"""
from itertools import product


OPTIONS = (None, False, True)
PATCHES = tuple(product(OPTIONS, repeat=2))
STATES = tuple(product((False, True), repeat=2))


def compatible(p, q):
    return all(a is None or b is None or a == b for a, b in zip(p, q))


def pairwise(family):
    return all(compatible(p, q) for p in family for q in family)


def realizes(s, p):
    return all(v is None or s[i] == v for i, v in enumerate(p))


def all_realizations(family):
    return tuple(s for s in STATES if all(realizes(s, p) for p in family))


def glue_all(base, family):
    return tuple(next((p[i] for p in family if p[i] is not None), base[i])
                 for i in range(len(base)))


def test_all_up_to_four_partial_writes_have_exact_iff():
    for count in range(5):
        for family in product(PATCHES, repeat=count):
            compatible_all = pairwise(family)
            realizations = all_realizations(family)
            assert compatible_all == bool(realizations)
            if compatible_all:
                for base in STATES:
                    merged = glue_all(base, family)
                    assert merged in realizations
                    for i in range(2):
                        if all(p[i] is None for p in family):
                            assert merged[i] == base[i]
                        else:
                            assert all(s[i] == merged[i] for s in realizations)


def test_conflicting_and_disjoint_partial_writes():
    conflict_left = (True, None)
    conflict_right = (False, None)
    disjoint_left = (True, None)
    disjoint_right = (None, True)
    assert not compatible(conflict_left, conflict_right)
    assert not all_realizations((conflict_left, conflict_right))
    assert compatible(disjoint_left, disjoint_right)
    assert glue_all((False, False), (disjoint_left, disjoint_right)) == (
        True, True)
    assert compatible((True, None), (True, None))


def test_previous_destructive_total_states_are_incompatible():
    destructive_whole_a = (True, False)
    destructive_whole_b = (False, True)
    assert not compatible(destructive_whole_a, destructive_whole_b)
    assert not all_realizations((destructive_whole_a, destructive_whole_b))


def faithful_history(old, new):
    # Both observations are constant on two states; embeddings are bijective.
    return any(all(f[old[x]] == new[f[x]] for x in (0, 1))
               for f in ((0, 1), (1, 0)))


def test_explicit_concurrency_gate_has_sharp_history_boundary():
    flip = (1, 0)
    stationary = (0, 1)
    for p, q in product(PATCHES, repeat=2):
        accepted = compatible(p, q)
        later = flip if accepted else stationary
        assert faithful_history(flip, later) == accepted
    # Gluing alone does not ensure history preservation when the gate
    # and later dynamics are independently changed.
    assert compatible((True, None), (None, False))
    assert not faithful_history(flip, stationary)
