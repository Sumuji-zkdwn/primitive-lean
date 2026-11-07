"""Independent finite checks of the observable rigid-point hypotheses.

Not a Lean proof. This enumerates all idempotents on up to four labels and
checks every commuting ordered pair, plus explicit counterexamples.
"""
from itertools import product


def compose(f, g):
    return tuple(f[i] for i in g)


def idempotents(n):
    return [f for f in product(range(n), repeat=n) if compose(f, f) == f]


def test_all_commuting_pairs_up_to_four():
    expected = {2: (3, 7), 3: (10, 58), 4: (41, 601)}
    for n, (number, commuting_number) in expected.items():
        maps = idempotents(n)
        commuting = [(m, c) for m in maps for c in maps
                     if compose(m, c) == compose(c, m)]
        assert len(maps) == number
        assert len(commuting) == commuting_number
        for m, c in commuting:
            for x in range(n):
                q = m[c[x]]
                assert m[q] == q
                assert c[q] == q


def test_disjoint_fixed_idempotents():
    m, c = (0, 0), (1, 1)
    assert compose(m, m) == m
    assert compose(c, c) == c
    assert not any(m[x] == x and c[x] == x for x in range(2))


def test_hidden_order_and_projected_fixed():
    states = list(product((False, True), repeat=2))
    k = lambda x: (x[0], False)
    m = lambda x: (False, x[1])
    c = lambda x: (x[0], x[0])
    u = lambda x: k(m(x))
    v = lambda x: k(c(x))
    assert m(c((True, False))) == (False, True)
    assert c(m((True, False))) == (False, False)
    assert m(c((True, False))) != c(m((True, False)))
    assert k(m(c((True, False)))) == k(c(m((True, False))))
    for s in states:
        assert k(k(s)) == k(s)
        assert m(m(s)) == m(s)
        assert c(c(s)) == c(s)
        assert u(u(s)) == u(s)
        assert v(v(s)) == v(s)
        assert u(v(s)) == v(u(s))
        q = u(v(s))
        assert k(q) == q and u(q) == q and v(q) == q
