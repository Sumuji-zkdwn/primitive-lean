from itertools import product

import pytest

from core import Certificate, Event, Model, Node, Policy, Step, VersionSpace, World
from core import distinguishing_word, quotient, solve, verify
from experiments import delayed_chain, doors, phantom_models, primitive, version_space


def test_each_model_solvable_does_not_supply_a_common_policy():
    models = [doors("m0", "left"), doors("m1", "right")]
    assert all(solve(version_space(m), 1).status == "solved" for m in models)
    assert solve(version_space(*models), 5).status == "infeasible-in-class"


def test_probe_then_observation_dependent_actions():
    space = version_space(doors("m0", "left", True), doors("m1", "right", True))
    result = solve(space, 2)
    assert result.status == "solved"
    cert = result.certificate
    assert cert and verify(space, cert)
    assert cert.policy.action == "inspect"
    assert {e.view.label: p.action for e, p in cert.policy.branches.items()} == {
        "left": "left", "right": "right"}
    assert solve(space, 1).status == "infeasible-in-class"


def test_indistinguishable_probe_does_not_leak_model_identity():
    space = version_space(doors("m0", "left", True, False), doors("m1", "right", True, False))
    assert solve(space, 3).status == "infeasible-in-class"


def test_probe_cost_is_counted():
    space = version_space(doors("m0", "left", True, probe_cost=2),
                          doors("m1", "right", True, probe_cost=2))
    assert solve(space, 2).status == "infeasible-in-class"
    result = solve(space, 3)
    assert result.certificate and verify(space, result.certificate)


def test_candidate_identity_cannot_switch_mid_trajectory():
    first, second = phantom_models()
    space = version_space(first, second)
    event = first.event(first.edges["s", "a"])
    space.observe("a", event)
    assert space.belief == frozenset({World("first", "m")})
    assert solve(space, 2).status == "infeasible-in-class"


def test_model_extension_invalidates_old_certificate():
    space = version_space(doors("m0", "left"))
    cert = solve(space, 1).certificate
    assert cert and verify(space, cert)
    assert space.add(doors("m1", "right"))
    assert not verify(space, cert)
    assert solve(space, 1).status == "infeasible-in-class"


def test_new_candidate_is_checked_against_full_history():
    model = doors("m0", "left", True)
    space = version_space(model)
    space.observe("inspect", model.event(model.edges["s", "inspect"]))
    assert not space.add(doors("m1", "right", True))
    assert space.add(doors("m2", "left", True))
    assert space.belief == frozenset({World("m0", "known"), World("m2", "known")})


def test_empty_candidate_set_is_not_declared_unsolvable():
    model = doors("m0", "left", True)
    actual = doors("m1", "right", True)
    space = version_space(model)
    space.observe("inspect", actual.event(actual.edges["s", "inspect"]))
    assert solve(space, 2).status == "no-model"
    assert space.add(actual)
    assert solve(space, 1).status == "solved"


def test_search_limit_is_not_an_impossibility_proof():
    space = version_space(doors("m0", "left", True), doors("m1", "right", True))
    assert solve(space, 2, max_nodes=1).status == "search-exhausted"
    assert solve(space, 2, max_nodes=50).status == "solved"


def test_long_cyclic_search_and_certificate_verification_are_stack_safe():
    model = Model(
        "two-state-loop",
        {"start": Node("start"), "win": Node("win", "win")},
        {
            ("start", "a-loop"): Step("start"),
            ("start", "b-win"): Step("win"),
        },
        frozenset({"start"}),
    )
    space = VersionSpace(model.view("start"))
    assert space.add(model)

    result = solve(space, 1000)

    assert result.status == "solved"
    assert result.expanded < 20000
    assert result.certificate and result.certificate.budget == 1000
    # Sorted DFS keeps exploring the cheaper-name self-loop before b-win.
    assert result.certificate.policy.action == "a-loop"
    assert verify(space, result.certificate)


def test_illegal_action_and_missing_observation_branch_fail_verification():
    space = version_space(doors("m0", "left", True), doors("m1", "right", True))
    cert = solve(space, 2).certificate
    assert cert
    bad = Certificate(cert.fingerprint, cert.budget, Policy("teleport", {}))
    assert not verify(space, bad)
    branches = dict(cert.policy.branches)
    branches.pop(next(iter(branches)))
    bad = Certificate(cert.fingerprint, cert.budget, Policy("inspect", branches))
    assert not verify(space, bad)


def test_forged_terminal_success_is_rejected():
    space = version_space(doors("m0", "left"))
    assert not verify(space, Certificate(space.fingerprint(), 0, Policy(None, {})))


def test_old_actions_composed_do_not_refine_but_new_operation_can():
    a, aa, ab = primitive(), primitive(add_composite=True), primitive(add_b=True)
    assert quotient(a)["0"] == quotient(a)["1"]
    assert quotient(aa)["0"] == quotient(aa)["1"]
    assert quotient(ab)["0"] != quotient(ab)["1"]
    assert distinguishing_word(a, "0", a, "1") is None
    assert distinguishing_word(ab, "0", ab, "1") == ("B",)


def test_finite_prefix_equivalence_can_break_arbitrarily_later():
    for delay in [1, 2, 5, 30]:
        yes, no = delayed_chain("yes", delay, True), delayed_chain("no", delay, False)
        assert distinguishing_word(yes, "0", no, "0") == ("continue",)*delay


def test_availability_and_cost_are_observable_distinctions():
    nodes = {"x": Node("same"), "y": Node("same")}
    partial = Model("partial", nodes, {("x", "a"): Step("x")}, frozenset({"x", "y"}))
    assert distinguishing_word(partial, "x", partial, "y") == ()
    cost = Model("cost", nodes, {("x", "a"): Step("x", 1),
                                ("y", "a"): Step("y", 2)}, frozenset({"x", "y"}))
    assert distinguishing_word(cost, "x", cost, "y") == ("a",)
    assert quotient(cost)["x"] != quotient(cost)["y"]


def test_renaming_has_no_effect_on_solvability():
    originals = [doors("m0", "left", True), doors("m1", "right", True)]
    transformed = []
    mapping = {"left": "op-z", "right": "op-y", "inspect": "op-x"}
    for model in originals:
        transformed.append(Model("renamed-"+model.name,
            {"state-"+s: Node("label-"+n.label, n.status) for s,n in model.nodes.items()},
            {("state-"+s, mapping[a]): Step("state-"+t.target, t.cost)
             for (s,a),t in model.edges.items()}, frozenset("state-"+s for s in model.starts)))
    space = version_space(*transformed)
    result = solve(space, 2)
    assert result.certificate and verify(space, result.certificate)
    assert result.certificate.policy.action == "op-x"


@pytest.mark.parametrize("targets", list(product(range(3), repeat=4)))
def test_partition_refinement_matches_independent_pair_search(targets):
    nodes = {"0": Node("same"), "1": Node("same"), "2": Node("goal", "win")}
    edges = {(s,a): Step(str(t)) for (s,a),t in zip(product(["0","1"], ["a","b"]), targets)}
    model = Model("finite", nodes, edges, frozenset({"0","1","2"}))
    blocks = quotient(model)
    for x,y in product(nodes, repeat=2):
        assert (blocks[x] == blocks[y]) == (distinguishing_word(model,x,model,y) is None)
