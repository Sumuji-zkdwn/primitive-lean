"""Finite exhaustive reference for capacity overload and historical loss.

Every local may service a bounded subset of requirements. The global
operation remains available only if ONE local satisfies EVERY active
requirement. Pairwise feasibility does not imply simultaneous feasibility.
"""
from itertools import product


def covers(table, local, demands):
    return all(table[local][d] for d in demands)


def enabled_locals(table, demands):
    return tuple(l for l in range(len(table)) if covers(table, l, demands))


def first_action(table, demands, actions, x):
    available = enabled_locals(table, demands)
    return x if not available else actions[available[0]][x]


def has_embedding(old_step, new_step):
    # All current observations constant, and underlying states fixed to 2.
    # All injections Fin2 -> Fin2 are permutations.
    for f in ((0, 1), (1, 0)):
        if all(f[old_step[x]] == new_step[f[x]] for x in (0, 1)):
            return True
    return False


def test_pairwise_compatibility_but_three_way_extinction():
    table = tuple(tuple(l != r for r in range(3)) for l in range(3))
    for r, s in product(range(3), repeat=2):
        assert enabled_locals(table, (r, s))
    assert not enabled_locals(table, (0, 1, 2))
    assert enabled_locals(table, (0, 1)) == (2,)

    flip = (1, 0)
    actions = (flip, flip, flip)
    old_step = tuple(first_action(table, (0, 1), actions, x)
                     for x in range(2))
    new_step = tuple(first_action(table, (0, 1, 2), actions, x)
                     for x in range(2))
    assert old_step == flip
    assert new_step == (0, 1)
    assert not has_embedding(old_step, new_step)


def test_every_three_by_three_support_matrix_with_capacity_two():
    # 2^9 support matrices: if every row supports at most two demands,
    # then the full three-demand load cannot be covered by any local.
    rows = tuple(product((False, True), repeat=3))
    for table in product(rows, repeat=3):
        if not all(sum(row) <= 2 for row in table):
            continue
        assert not enabled_locals(table, (0, 1, 2))
        for before in ((), (0,), (0, 1)):
            for after in (before, (0, 1, 2)):
                if set(before) <= set(after):
                    # Enlarging a demand set cannot help a specific local.
                    assert set(enabled_locals(table, after)) <= set(
                        enabled_locals(table, before))


def test_capacity_threshold_is_sharp_not_automatic_extinction():
    full = ((True, True, True), (False, False, False))
    assert enabled_locals(full, (0, 1, 2)) == (0,)
    # Growth from 2 to 3 demands alone does not force extinction.
    assert enabled_locals(full, (0, 1))
    assert enabled_locals(full, (0, 1, 2))


def test_noncommuting_finite_actions_can_remain_available():
    def swap01(x):
        return 1 if x == 0 else 0 if x == 1 else 2

    def swap12(x):
        return 2 if x == 1 else 1 if x == 2 else 0

    assert swap01(swap12(0)) != swap12(swap01(0))
    # Both local actions may be permanently available.
    table = ((True,), (True,))
    for t in range(10):
        assert enabled_locals(table, (0,)) == (0, 1)
        assert t >= 0
