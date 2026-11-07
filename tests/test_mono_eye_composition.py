"""Independent exact finite-model audit for Mono-eye ME-3/T9 composition.

This test does not certify Lean proofs or physical Elastica gluing. It enumerates
all two-bit observation maps and boundary-controlled updates for two 2-state
components, checks predictor equivalence via fixed-point refinement, and
checks an inaccessible-boundary counterexample with a 3-state component.
"""
from itertools import product


def predictive_relation(states, actions, output, step):
    """Greatest output-respecting action-stable relation on finite states."""
    pairs = {(a, b) for a in states for b in states if output(a) == output(b)}
    while True:
        refined = {
            (a, b) for a, b in pairs
            if all((step(action, a), step(action, b)) in pairs for action in actions)
        }
        if refined == pairs:
            return pairs
        pairs = refined


def maps2():
    return [(0, 0), (0, 1), (1, 0), (1, 1)]


def audit_two_state_models():
    """4*4*16*16 = 4,096 complete controlled two-eye models."""
    states = [(a, b) for a in (0, 1) for b in (0, 1)]
    examined = 0
    for oa, ob, acode, bcode in product(maps2(), maps2(), product(maps2(), repeat=2), product(maps2(), repeat=2)):
        # acode[b][a] and bcode[a][b] are full input-controlled updates.
        local_a = predictive_relation((0, 1), (0, 1), lambda a: oa[a], lambda boundary, a: acode[boundary][a])
        local_b = predictive_relation((0, 1), (0, 1), lambda b: ob[b], lambda boundary, b: bcode[boundary][b])
        product_eq = {((a, b), (aa, bb)) for a, b in states for aa, bb in states
                      if (a, aa) in local_a and (b, bb) in local_b}
        readout = lambda p: (oa[p[0]], ob[p[1]])
        independent = predictive_relation(
            states, list(product((0, 1), repeat=2)), readout,
            lambda ij, p: (acode[ij[0]][p[0]], bcode[ij[1]][p[1]]))
        assert independent == product_eq, (oa, ob, acode, bcode, "independent")
        wired = predictive_relation(
            states, (None,), readout,
            lambda _i, p: (acode[ob[p[1]]][p[0]], bcode[oa[p[0]]][p[1]]))
        assert product_eq <= wired, (oa, ob, acode, bcode, "wired")
        examined += 1
    assert examined == 4096
    return examined


def test_exhaustive_eyes():
    assert audit_two_state_models() == 4096


def test_unreachable_boundary_counterexample():
    # The global right eye never produces boundary=True from either state.
    oa = lambda a: a == 2
    ob = lambda b: b
    left = lambda boundary, a: 2 if boundary and a == 1 else a
    right = lambda _boundary, _b: False
    states = list(product(range(3), (False, True)))
    output = lambda p: (oa(p[0]), ob(p[1]))
    step = lambda _i, p: (left(ob(p[1]), p[0]), right(oa(p[0]), p[1]))
    global_eq = predictive_relation(states, (None,), output, step)
    x, y = (0, False), (1, False)
    assert (x, y) in global_eq
    assert oa(left(True, x[0])) != oa(left(True, y[0]))


if __name__ == '__main__':
    n = audit_two_state_models()
    test_unreachable_boundary_counterexample()
    print(f'PASS: {n} exhaustive two-state eyes; open product iff; feedback soundness; strict boundary counterexample')
