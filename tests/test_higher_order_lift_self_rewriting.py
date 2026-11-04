"""Finite internal higher-order lift rewriting regression."""
from itertools import product


def frontier(known, edges):
    return [
        target
        for source in known
        for edge_source, target in edges
        if edge_source == source and target not in known
    ]


def choose_target(known, edges, viable):
    return next((target for target in frontier(known, edges) if viable[target]), None)


def interpret_meta(meta_rules, target):
    return tuple(edge for trigger, edge in meta_rules if trigger == target)


def apply_lift_edits(lift_rules, lift_edits, learned):
    return lift_rules + tuple(
        installed for trigger, installed in lift_edits if trigger == learned
    )


def run_lift(lift_rules, learned):
    return tuple(meta_rule for trigger, meta_rule in lift_rules if trigger == learned)


def step_higher(state, viable):
    known, edges, meta_rules, lift_rules, lift_edits = state
    target = choose_target(known, edges, viable)
    if target is None:
        return None
    next_lift_rules = apply_lift_edits(lift_rules, lift_edits, target)
    next_meta_rules = meta_rules + run_lift(next_lift_rules, target)
    return (
        known + (target,),
        edges + interpret_meta(meta_rules, target),
        next_meta_rules,
        next_lift_rules,
        lift_edits,
    )


def step_pr64(state, external_lift, viable):
    known, edges, meta_rules = state
    target = choose_target(known, edges, viable)
    if target is None:
        return None
    return (
        known + (target,),
        edges + interpret_meta(meta_rules, target),
        meta_rules + tuple(external_lift.get(target, ())),
    )


def iterate(step, state, *args, limit=32):
    trace = [state]
    for _ in range(limit):
        next_state = step(state, *args)
        if next_state is None:
            return state, tuple(trace)
        state = next_state
        trace.append(state)
    raise AssertionError("finite machine failed to saturate within its bound")


def observation(state, operator):
    edges = state[1]
    return tuple(sorted({target for source, target in edges if source == operator}))


def behavior_classes(state):
    known = state[0]
    return {observation(state, operator) for operator in known}


def test_internal_lift_program_changes_and_reproduces_pr64_projection():
    m12 = (1, (1, 2))
    m23 = (2, (2, 3))
    edit = (1, (1, m23))
    seed = ((0,), ((0, 1),), (m12,), (), (edit,))
    first = step_higher(seed, (True,) * 4)

    pr64_seed = ((0,), ((0, 1),), (m12,))
    pr64_first = step_pr64(pr64_seed, {1: (m23,), 2: ()}, (True,) * 4)

    assert seed[3] == ()
    assert first[3] == ((1, m23),)
    assert first[3] != seed[3]
    assert first[:3] == pr64_first


def test_three_conditions_and_four_state_saturation():
    m12 = (1, (1, 2))
    m23 = (2, (2, 3))
    edit = (1, (1, m23))
    viable = (True,) * 4

    high_seed = ((0,), ((0, 1),), (m12,), (), (edit,))
    high_final, high_trace = iterate(step_higher, high_seed, viable)

    pr64_seed = ((0,), ((0, 1),), (m12,))
    pr64_final, pr64_trace = iterate(step_pr64, pr64_seed, {1: (m23,), 2: ()}, viable)

    frozen1 = ((0, 1), ((0, 1), (1, 2)), (m12,))
    fixed_final, fixed_trace = iterate(step_pr64, frozen1, {1: (m23,), 2: ()}, viable)

    assert [state[0] for state in high_trace] == [
        (0,), (0, 1), (0, 1, 2), (0, 1, 2, 3)
    ]
    assert [state[0] for state in pr64_trace] == [
        (0,), (0, 1), (0, 1, 2), (0, 1, 2, 3)
    ]
    assert fixed_final[0] == (0, 1, 2)
    assert high_final[0] == pr64_final[0] == (0, 1, 2, 3)
    assert step_higher(high_final, viable) is None


def test_rule_mutation_and_identification_capacity_are_separate():
    m12 = (1, (1, 2))
    m23 = (2, (2, 3))
    edit = (1, (1, m23))
    viable = (True,) * 4

    high_seed = ((0,), ((0, 1),), (m12,), (), (edit,))
    high_final, high_trace = iterate(step_higher, high_seed, viable)
    assert high_trace[1][3] != high_trace[0][3]

    frozen1 = ((0, 1), ((0, 1), (1, 2)), (m12,))
    fixed_final, _ = iterate(step_pr64, frozen1, {1: (m23,), 2: ()}, viable)
    pr64_seed = ((0,), ((0, 1),), (m12,))
    second_order_final, _ = iterate(step_pr64, pr64_seed, {1: (m23,), 2: ()}, viable)

    assert len(behavior_classes(fixed_final)) == 3
    assert len(behavior_classes(second_order_final)) == 4
    assert len(behavior_classes(high_final)) == 4
    assert len(behavior_classes(fixed_final)) < len(behavior_classes(high_final))


def test_stalled_finite_frontier_does_not_invent_targets():
    frozen = ((0, 1, 2), ((0, 1), (1, 2)), ((1, (1, 2)),), (), ())
    assert step_higher(frozen, (True,) * 4) is None


def test_newly_emitted_meta_rule_is_not_applied_in_the_same_transition():
    emitted = (1, (1, 2))
    edit = (1, (1, emitted))
    seed = ((0,), ((0, 1),), (), (), (edit,))

    next_state = step_higher(seed, (True,) * 3)

    assert next_state[2] == (emitted,)
    assert next_state[1] == seed[1]


def test_frontier_selection_is_first_viable_candidate():
    states = range(3)
    edges_all = tuple(product(states, states))
    for mask in range(1 << len(edges_all)):
        edges = tuple(edge for i, edge in enumerate(edges_all) if mask & (1 << i))
        known = (0,)
        viable = (False, True, True)
        candidates = [x for x in frontier(known, edges) if viable[x]]
        if candidates:
            assert choose_target(known, edges, viable) == candidates[0]
        else:
            assert choose_target(known, edges, viable) is None
