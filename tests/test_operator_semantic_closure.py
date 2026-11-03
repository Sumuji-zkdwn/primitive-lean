"""Finite oracle for semantic versus syntactic operator closure.

This tests induced quotient operations on small labelled transition
systems. It is independent evidence, not a substitute for Lean proofs.
"""
from itertools import product


def canon(values):
    table = {}
    ans = []
    for v in values:
        if v not in table:
            table[v] = len(table)
        ans.append(table[v])
    return tuple(ans)


def predictive_partition(outputs, operators):
    cur = canon(outputs)
    while True:
        nxt = canon(tuple((cur[x], tuple(cur[t[x]] for t in operators))
                          for x in range(len(outputs))))
        if nxt == cur:
            return cur
        cur = nxt


def compatible(states, trans, partition):
    return all(partition[x] != partition[y] or
               partition[trans[x]] == partition[trans[y]]
               for x in range(states) for y in range(states))


def quotient_table(trans, partition):
    d = {}
    for x, cls in enumerate(partition):
        target = partition[trans[x]]
        if cls in d:
            assert d[cls] == target
        d[cls] = target
    return d


def compose(f, g):
    return tuple(g[f[x]] for x in range(len(f)))


def test_all_three_state_semantic_endomorphisms():
    n = 3
    candidates = tuple(product(range(n), repeat=n))
    old = tuple(product(range(n), repeat=n))
    for outputs in product(range(2), repeat=n):
        for op1 in old:
            part = predictive_partition(outputs, (op1,))
            assert compatible(n, op1, part)
            ids = [t for t in candidates if compatible(n, t, part)]
            for t in ids:
                table = quotient_table(t, part)
                assert all(table[part[x]] == part[t[x]] for x in range(n))
            for t in ids:
                for s in ids:
                    assert compatible(n, compose(t, s), part)


def test_conservative_but_nongenerated_new_operator():
    outputs = (0, 0, 1)
    identity = (0, 1, 2)
    constant_two = (2, 2, 2)
    old_part = predictive_partition(outputs, (identity,))
    extension = predictive_partition(outputs, (identity, constant_two))
    assert old_part == extension
    assert compatible(3, constant_two, old_part)
    assert quotient_table(identity, old_part) != quotient_table(constant_two, old_part)
    # Every word of an identity-only language is identity. Its quotient
    # maps therefore cannot equal the constant-to-two quotient action.
    assert compose(identity, identity) == identity


def test_semantically_compatible_may_be_noninjective():
    outputs = (0, 0, 1)
    identity = (0, 1, 2)
    constant_two = (2, 2, 2)
    part = predictive_partition(outputs, (identity,))
    qmap = quotient_table(constant_two, part)
    assert len(set(qmap.values())) == 1
    assert len(set(part)) == 2


def test_semantic_conservativity_is_stronger_than_one_step_readout_agreement():
    # Three states with immediate outputs [0,0,1].
    # The old identity action cannot distinguish states 0,1.
    outputs = (0, 0, 1)
    identity = (0, 1, 2)
    new_action = (0, 2, 2)
    old_part = predictive_partition(outputs, (identity,))
    assert not compatible(3, new_action, old_part)
    new_part = predictive_partition(outputs, (identity, new_action))
    assert len(set(new_part)) > len(set(old_part))
