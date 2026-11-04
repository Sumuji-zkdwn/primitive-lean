"""Independent finite oracle for bounded recursive operator reentry."""
from itertools import product


def frontier(children, known):
    return [x for p in known for x in children[p] if x not in known]


def learn(children, viable, known):
    return next((known + (x,) for x in frontier(children, known) if viable[x]), None)


def iterate(children, viable, known, n):
    for _ in range(n):
        nxt = learn(children, viable, known)
        if nxt is None:
            return known
        known = nxt
    return known


def patch(start, target, x):
    return target if x == start else x


def test_all_three_state_generation_tables():
    states = tuple(range(3))
    catalogs = tuple(tuple(x for x in states if m & (1 << x))
                     for m in range(8))
    for children in product(catalogs, repeat=3):
        for subset in range(8):
            known = tuple(x for x in states if subset & (1 << x))
            for mask in range(8):
                valid = tuple(bool(mask & (1 << x)) for x in states)
                choices = [x for x in frontier(children, known) if valid[x]]
                nxt = learn(children, valid, known)
                if not choices:
                    assert nxt is None
                    assert iterate(children, valid, known, 8) == known
                else:
                    assert nxt == known + (choices[0],)
                    assert len(nxt) == len(known) + 1
                    target = nxt[-1]
                    assert target not in known
                    for prior in known:
                        assert patch(0, target, 0) != patch(0, prior, 0)


def test_three_round_feedback_and_saturation():
    children = ((1,), (2,), (3,), ())
    valid = (True,) * 4
    assert learn(children, valid, (0,)) == (0, 1)
    assert learn(children, valid, (0, 1)) == (0, 1, 2)
    assert learn(children, valid, (0, 1, 2)) == (0, 1, 2, 3)
    assert learn(children, valid, (0, 1, 2, 3)) is None
    assert iterate(children, valid, (0,), 3) == (0, 1, 2, 3)
    assert iterate(children, valid, (0,), 100) == (0, 1, 2, 3)


def test_viability_blocks_a_later_round():
    children = ((1,), (2,), (3,), ())
    valid = (False, True, False, True)
    assert iterate(children, valid, (0,), 100) == (0, 1)


def test_reentry_repair_and_old_word_obstruction():
    children = ((1,), (2,), ())
    valid = (False, False, True)
    nxt = learn(children, valid, (1,))
    assert nxt == (1, 2)
    assert patch(1, nxt[-1], 1) == 2
    assert all(1 != patch(1, nxt[-1], 1) for _ in range(10))
