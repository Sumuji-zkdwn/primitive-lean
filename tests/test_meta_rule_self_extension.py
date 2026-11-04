"""Exhaustive finite meta-rule reentry oracle; no open-ended synthesis claim."""
from itertools import product


def frontier(known, edges):
    return [v for x in known for a, v in edges if a == x and v not in known]


def step(m, lift, valid):
    known, edges, meta = m
    target = next((x for x in frontier(known, edges) if valid[x]), None)
    if target is None:
        return None
    return (known + (target,),
            edges + tuple(edge for source, edge in meta if source == target),
            meta + tuple(lift[target]))


def iterate(m, lift, valid, n):
    for _ in range(n):
        nxt = step(m, lift, valid)
        if nxt is None:
            return m
        m = nxt
    return m


def test_concrete_three_rounds_and_frozen_control():
    lift = ((), ((2, (2, 3)),), (), ())
    valid = (True,) * 4
    seed = ((0,), ((0, 1),), ((1, (1, 2)),))
    s1 = ((0, 1), ((0, 1), (1, 2)), ((1, (1, 2)), (2, (2, 3))))
    s2 = ((0, 1, 2), ((0, 1), (1, 2), (2, 3)),
          ((1, (1, 2)), (2, (2, 3))))
    s3 = ((0, 1, 2, 3), s2[1], s2[2])
    frozen1 = (s1[0], s1[1], ((1, (1, 2)),))
    frozen2 = ((0, 1, 2), s1[1], frozen1[2])
    assert step(seed, lift, valid) == s1
    assert step(s1, lift, valid) == s2
    assert step(s2, lift, valid) == s3
    assert step(s3, lift, valid) is None
    assert iterate(seed, lift, valid, 3) == s3
    assert iterate(seed, lift, valid, 99) == s3
    assert frozen1[:2] == s1[:2] and frozen1[2] != s1[2]
    assert step(frozen1, lift, valid) == frozen2
    assert step(frozen2, lift, valid) is None
    assert step(frozen1, lift, valid)[1] != s2[1]


def test_all_small_rule_tables_with_sampled_meta_catalogs():
    states = range(3)
    edges_all = tuple(product(states, states))
    meta_choices = ((), ((1, (1, 2)),), ((2, (0, 1)),))
    lift = ((), ((2, (2, 0)),), ())
    for edge_mask in range(2 ** len(edges_all)):
        edges = tuple(e for i, e in enumerate(edges_all) if edge_mask & 1 << i)
        for known_mask in range(8):
            known = tuple(x for x in states if known_mask & 1 << x)
            for valid_mask in range(8):
                valid = tuple(bool(valid_mask & 1 << x) for x in states)
                for meta in meta_choices:
                    nxt = step((known, edges, meta), lift, valid)
                    choices = [x for x in frontier(known, edges) if valid[x]]
                    if not choices:
                        assert nxt is None
                    else:
                        target = choices[0]
                        assert nxt[0] == known + (target,)
                        assert nxt[1] == edges + tuple(e for source, e in meta
                                                         if source == target)
                        assert nxt[2] == meta + tuple(lift[target])


def test_failed_frontier_does_not_fabricate_solution():
    m = ((0,), ((0, 1),), ((1, (1, 2)),))
    lift = ((), ((2, (2, 0)),), ())
    assert iterate(m, lift, (False,) * 3, 99) == m
