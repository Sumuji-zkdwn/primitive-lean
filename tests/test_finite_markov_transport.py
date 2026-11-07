"""Independent exact-Fraction checks for the finite Markov extension.

These enumerate every state/control in the model. They complement, and do
not replace, the universal Lean proofs in Research/FiniteMarkovTransport.lean.
"""
from fractions import Fraction as F
from itertools import product


POSITIONS = (0, 1)
HISTORIES = (0, 1)
CONTROLS = range(4)
OPERATIONS = (0, 1)  # relax/reset, prime
TARGET_MASS = F(1, 3)


def update_history(_old, operation):
    return operation


def observe(position, _history):
    return position


def stiffness(history):
    return F(1 if history == 0 else 3)


def control_value(control):
    return F(control, 6)


def endpoint_mass(history, first, second):
    return (control_value(first) + control_value(second)) / stiffness(history)


def kernel(history, first, second, source, target):
    mass = endpoint_mass(history, first, second)
    if source == 0:
        return mass if target == 1 else 1 - mass
    return F(1 if target == 1 else 0)


def action(first, second):
    return control_value(first) ** 2 + control_value(second) ** 2


def target_pairs(history):
    return [
        (a, b)
        for a, b in product(CONTROLS, repeat=2)
        if endpoint_mass(history, a, b) == TARGET_MASS
    ]


def canonical_plan(target_mass):
    return {
        (0, 0): 1 - target_mass,
        (0, 1): target_mass,
        (1, 0): F(0),
        (1, 1): F(0),
    }


def transport_cost(plan):
    # Unit-spaced two-point state space: squared move cost is one off-diagonal.
    return plan[(0, 1)] + plan[(1, 0)]


def coupling_marginals(plan):
    source = {x: plan[(x, 0)] + plan[(x, 1)] for x in POSITIONS}
    target = {y: plan[(0, y)] + plan[(1, y)] for y in POSITIONS}
    return source, target


def test_history_update_changes_hidden_state_not_observation():
    position, old_history = 0, 0
    states = [(position, update_history(old_history, op)) for op in OPERATIONS]
    assert states == [(0, 0), (0, 1)]
    assert observe(*states[0]) == observe(*states[1]) == 0


def test_every_controlled_transition_is_a_rational_probability_kernel():
    for h, a, b in product(HISTORIES, CONTROLS, CONTROLS):
        for x in POSITIONS:
            row = [kernel(h, a, b, x, y) for y in POSITIONS]
            assert all(p >= 0 for p in row)
            assert sum(row, F(0)) == 1


def test_finite_minimum_action_matches_existing_quadratic_costs():
    expected = {0: F(1, 18), 1: F(1, 2)}
    expected_minimizers = {0: (1, 1), 1: (3, 3)}
    for h in HISTORIES:
        feasible = target_pairs(h)
        assert feasible
        costs = [action(a, b) for a, b in feasible]
        assert min(costs) == expected[h]
        assert expected_minimizers[h] in feasible

        # The same stiffness gives PR #91's one-step requiredAction k²d²;
        # the two-control Gramian divides this effort by the horizon 2.
        required_input_action = (stiffness(h) * TARGET_MASS) ** 2
        assert min(costs) == required_input_action / 2


def test_finite_transport_cost_is_history_independent():
    plan = canonical_plan(TARGET_MASS)
    assert sum(plan[(0, y)] for y in POSITIONS) == 1
    assert sum(plan[(1, y)] for y in POSITIONS) == 0
    assert sum(plan[(x, 0)] for x in POSITIONS) == 1 - TARGET_MASS
    assert sum(plan[(x, 1)] for x in POSITIONS) == TARGET_MASS
    assert transport_cost(plan) == TARGET_MASS

    for h in HISTORIES:
        best = min(target_pairs(h), key=lambda pair: action(*pair))
        assert endpoint_mass(h, *best) == TARGET_MASS
        assert transport_cost(plan) == TARGET_MASS

    assert expected_ratio() == 9


def test_exact_rational_couplings_have_forced_transport_cost():
    expected = canonical_plan(TARGET_MASS)
    for denominator in (3, 6, 9, 12):
        grid = [F(i, denominator) for i in range(denominator + 1)]
        feasible = []
        for entries in product(grid, repeat=4):
            plan = dict(zip(((0, 0), (0, 1), (1, 0), (1, 1)), entries))
            source, target = coupling_marginals(plan)
            if source == {0: F(1), 1: F(0)} and target == {
                0: 1 - TARGET_MASS,
                1: TARGET_MASS,
            }:
                feasible.append(plan)
        assert feasible == [expected]
        assert transport_cost(feasible[0]) == TARGET_MASS


def expected_ratio():
    high = min(action(*pair) for pair in target_pairs(1))
    low = min(action(*pair) for pair in target_pairs(0))
    return high / low


if __name__ == "__main__":
    checks = [
        test_history_update_changes_hidden_state_not_observation,
        test_every_controlled_transition_is_a_rational_probability_kernel,
        test_finite_minimum_action_matches_existing_quadratic_costs,
        test_finite_transport_cost_is_history_independent,
        test_exact_rational_couplings_have_forced_transport_cost,
    ]
    for check in checks:
        check()
    print(f"{len(checks)} exact-Fraction checks passed")
