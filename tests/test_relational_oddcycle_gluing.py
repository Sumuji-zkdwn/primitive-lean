"""Independent exhaustive checks for relational feasibility and gluing.

Pairwise satisfiability of relational constraints is weaker than
overlap agreement of fixed partial assignments: each pair can use
a different full-state witness. No ontology or preservation axiom is assumed.
"""
from itertools import combinations, product


def feasible(nstates, constraints):
    return next((s for s in product((False, True), repeat=nstates)
                 if all(c(s) for c in constraints)), None)


def check_hierarchy(nstates, constraints):
    individually = all(feasible(nstates, [c]) is not None for c in constraints)
    pairwise = all(feasible(nstates, [a, b]) is not None
                   for a in constraints for b in constraints)
    global_ = feasible(nstates, constraints) is not None
    assert not global_ or pairwise
    assert not pairwise or individually
    return individually, pairwise, global_


def test_opposing_local_constraints_break_pairwise_feasibility():
    constraints = (lambda s: s[0] is True, lambda s: s[0] is False)
    assert check_hierarchy(1, constraints) == (True, False, False)


def test_odd_triangle_each_pair_but_not_all_constraints():
    edges = ((0, 1), (1, 2), (2, 0))
    constraints = tuple(lambda s, i=i, j=j: s[i] != s[j] for i, j in edges)
    assert check_hierarchy(3, constraints) == (True, True, False)
    # Exhaustively inspect every proper subset of constraints.
    for k in range(3):
        for indices in combinations(range(3), k):
            assert feasible(3, [constraints[i] for i in indices]) is not None
    assert feasible(3, constraints) is None


def test_even_cycle_is_globally_feasible():
    edges = ((0, 1), (1, 2), (2, 3), (3, 0))
    constraints = tuple(lambda s, i=i, j=j: s[i] != s[j] for i, j in edges)
    assert check_hierarchy(4, constraints) == (True, True, True)
    assert feasible(4, constraints) in (
        (False, True, False, True),
        (True, False, True, False),
    )


def test_fixed_patch_gluing_is_not_general_relational_satisfaction():
    # Two partial writes are compatible and have a unique common state
    # when all coordinates are covered.
    patches = ({0: True}, {1: True})
    compatible = all(p[i] == q[i]
                     for p in patches for q in patches
                     for i in set(p) & set(q))
    assert compatible
    realizations = [
        s for s in product((False, True), repeat=2)
        if all(s[i] == v for p in patches for i, v in p.items())
    ]
    assert realizations == [(True, True)]
    # This separate global relation is not satisfied by the glued state.
    assert not any(s[0] != s[1] for s in realizations)


def test_larger_cycle_parity_pattern():
    # General finite reference: odd cycles in Bool cannot be 2-coloured,
    # whereas even cycles can. Lean source only proves 3 and 4 instances.
    for n in range(3, 9):
        constraints = tuple(
            lambda s, j=j, n=n: s[j] != s[(j + 1) % n]
            for j in range(n)
        )
        is_feasible = feasible(n, constraints) is not None
        assert is_feasible == (n % 2 == 0)
