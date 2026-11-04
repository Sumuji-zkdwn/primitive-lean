"""Reference interpreter and finite exhaustive checks for rule-table mutation.

The rule edges are mutable state. Only the higher-order compilation policy
remains fixed. Python tests complement, but never replace, Lean proof checks.
"""
from itertools import combinations, product


def child_candidates(known, edges):
    return [target for source in known
            for a, target in edges if a == source and target not in known]


def transition(machine, compile_edges, viable):
    known, edges = machine
    target = next((x for x in child_candidates(known, edges)
                   if viable[x]), None)
    if target is None:
        return None
    return (known + (target,), edges + tuple(compile_edges[target]))


def iterate(machine, compiler, viable, rounds):
    for _ in range(rounds):
        next_machine = transition(machine, compiler, viable)
        if next_machine is None:
            break
        machine = next_machine
    return machine


def test_ordinary_reentry_versus_rule_mutation():
    compiler = ((), ((1, 2),), ((2, 3),), ())
    viable = (True,) * 4
    seed = ((0,), ((0, 1),))
    m1 = transition(seed, compiler, viable)
    assert m1 == ((0, 1), ((0, 1), (1, 2)))
    m2 = transition(m1, compiler, viable)
    assert m2 == ((0, 1, 2), ((0, 1), (1, 2), (2, 3)))
    m3 = transition(m2, compiler, viable)
    assert m3 == ((0, 1, 2, 3), ((0, 1), (1, 2), (2, 3)))
    assert transition(m3, compiler, viable) is None
    assert iterate(seed, compiler, viable, 3) == m3
    assert iterate(seed, compiler, viable, 100) == m3

    # Same known catalogue, same viability and meta-compiler.
    frozen = ((0, 1), ((0, 1),))
    assert frozen[0] == m1[0]
    assert frozen[1] != m1[1]
    assert transition(frozen, compiler, viable) is None
    assert transition(m1, compiler, viable) == m2


def test_all_small_rule_graphs_preserve_invariants():
    states = range(3)
    edges_universe = tuple(product(states, states))
    compiler_options = (
        ((), (), ()),
        (((0, 1),), (), ()),
        ((), ((1, 2),), ()),
        ((), (), ((2, 0),)),
    )
    for mask in range(1 << len(edges_universe)):
        edges = tuple(e for i, e in enumerate(edges_universe)
                      if mask & (1 << i))
        for known_mask in range(8):
            known = tuple(i for i in states if known_mask & (1 << i))
            for valid_mask in range(8):
                viable = tuple(bool(valid_mask & (1 << i)) for i in states)
                for compiler in compiler_options:
                    nxt = transition((known, edges), compiler, viable)
                    eligible = [x for x in child_candidates(known, edges)
                                if viable[x]]
                    if not eligible:
                        assert nxt is None
                        continue
                    target = eligible[0]
                    assert nxt is not None
                    assert target not in known and viable[target]
                    assert nxt[0] == known + (target,)
                    assert nxt[1] == edges + tuple(compiler[target])
                    assert nxt[0][:len(known)] == known
                    assert nxt[1][:len(edges)] == edges


def test_no_viable_candidates_and_no_unearned_repair():
    machine = ((0,), ((0, 1),))
    compiler = ((), ((1, 2),), ())
    assert transition(machine, compiler, (False,) * 3) is None
    assert iterate(machine, compiler, (False,) * 3, 9) == machine


def test_one_step_interval_repair_is_conditional():
    # Old identity never leaves state 1; local 1 only accepts state 2 at t=1.
    known, edges = ((1,), ((1, 2),))
    compiler = ((), (), ())
    viable = (False, False, True)
    nxt = transition((known, edges), compiler, viable)
    assert nxt[0][-1] == 2
    patch = lambda x: 2 if x == 1 else x
    assert patch(1) == 2
    assert all(1 != patch(1) for _ in range(10))
