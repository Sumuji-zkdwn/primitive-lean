"""Independent finite checks for the interval-preservation obstruction.

These checks are not Lean proofs; they test the exact three-state witnesses
and the role of all-local extinction versus one-local disappearance.
"""
from itertools import product

STATES = range(3)
OLD = lambda x: x
REPAIR = lambda x: 2 if x == 1 else x


def survivor(time, x, replaced=False):
    if replaced:
        return (time == 0 and x == 1) or (time == 1 and x == 1)
    return (time == 0 and x == 1) or (time == 1 and x == 2)


def interval_survives(word, start=1, replaced=False):
    x = start
    if not survivor(0, x, replaced):
        return False
    for time, action in enumerate(word, 1):
        x = OLD(x) if action == "o" else REPAIR(x)
        if not survivor(time, x, replaced):
            return False
    return True


def test_old_invariance_and_terminal_extinction():
    assert all(x != 2 or OLD(x) == 2 for x in STATES)
    assert all(OLD(1) == 1 for _ in range(20))
    assert all(not survivor(1, x) for x in STATES if x != 2)


def test_success_requires_a_new_symbol():
    for length in range(2):
        for word in product(("o", "n"), repeat=length):
            if length == 1 and interval_survives(word):
                assert "n" in word
    assert not interval_survives(("o",))
    assert interval_survives(("n",))


def test_repair_not_old_generated_and_strictly_refines_observation():
    assert REPAIR(1) == 2
    assert all(OLD(1) != REPAIR(1) for _ in range(30))
    observer = lambda x: 0 if x in (0, 1) else 1
    assert observer(0) == observer(1)
    assert observer(REPAIR(0)) != observer(REPAIR(1))


def test_one_local_extinction_without_forced_extension():
    def component(time, loc, x):
        return ((time == 0 and loc == 0 and x == 1)
                or (time == 1 and loc == 1 and x == 1))
    assert all(not component(1, 0, x) for x in STATES)
    assert component(0, 0, 1)
    assert component(1, 1, 1)
    assert interval_survives(("o",), replaced=True)
