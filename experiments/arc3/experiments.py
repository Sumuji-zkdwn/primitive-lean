"""Counterexamples and checks; these are not ARC-AGI-3 benchmark tasks."""
from __future__ import annotations

import json
from collections import deque
from pathlib import Path

from core import Model, Node, Step, VersionSpace, solve, verify, quotient, distinguishing_word


def doors(name: str, correct: str, probe: bool = False, informative: bool = True,
          probe_cost: int = 1) -> Model:
    nodes = {"s": Node("door"), "known": Node(correct if informative else "same-signal"),
             "w": Node("success", "win"), "f": Node("failure", "fail")}
    edges = {(s, a): Step("w" if a == correct else "f")
             for s in ["s", "known"] for a in ["left", "right"]}
    if probe:
        edges["s", "inspect"] = Step("known", probe_cost)
    return Model(name, nodes, edges, frozenset({"s"}))


def version_space(*models: Model) -> VersionSpace:
    first = models[0]
    space = VersionSpace(first.view(sorted(first.starts)[0]))
    for model in models:
        assert space.add(model)
    return space


def primitive(add_b: bool = False, add_composite: bool = False) -> Model:
    nodes = {str(i): Node(str(int(i == 2))) for i in range(3)}
    edges = {(str(i), "A"): Step(str(j)) for i, j in enumerate([1, 0, 2])}
    if add_b:
        edges.update({(str(i), "B"): Step(str(j)) for i, j in enumerate([0, 2, 1])})
    if add_composite:
        edges.update({(str(i), "AA"): Step(str(i), 2) for i in range(3)})
    return Model("primitive", nodes, edges, frozenset({"0", "1", "2"}))


def delayed_chain(name: str, length: int, success: bool) -> Model:
    nodes = {str(i): Node("unchanged") for i in range(length)}
    nodes[str(length)] = Node("success" if success else "failure", "win" if success else "fail")
    edges = {(str(i), "continue"): Step(str(i+1)) for i in range(length)}
    return Model(name, nodes, edges, frozenset({"0"}))


def phantom_models() -> tuple[Model, Model]:
    nodes = {"s": Node("start"), "m": Node("middle"),
             "w": Node("success", "win"), "f": Node("failure", "fail")}
    first = Model("first", nodes, {
        ("s", "a"): Step("m"), ("s", "b"): Step("f"),
        ("m", "a"): Step("f"), ("m", "b"): Step("f")}, frozenset({"s"}))
    second = Model("second", nodes, {
        ("s", "a"): Step("f"), ("s", "b"): Step("m"),
        ("m", "a"): Step("f"), ("m", "b"): Step("w")}, frozenset({"s"}))
    return first, second


def lossy_union_reaches_goal(models: tuple[Model, ...]) -> bool:
    """Intentionally WRONG planner: forget candidate identity and latent state."""
    adjacency = {}
    for model in models:
        for (s, _), step in model.edges.items():
            adjacency.setdefault(model.nodes[s].label, set()).add(model.nodes[step.target].label)
    queue, seen = deque(["start"]), {"start"}
    while queue:
        label = queue.popleft()
        if label == "success":
            return True
        for target in adjacency.get(label, set()):
            if target not in seen:
                queue.append(target)
                seen.add(target)
    return False


def run() -> dict:
    from itertools import product
    from learner import Episode, synthesize
    blind = [doors("left-world", "left"), doors("right-world", "right")]
    observed = [doors("left-world", "left", True), doors("right-world", "right", True)]
    probes = version_space(*observed)
    informed = solve(probes, 2)
    initial = version_space(blind[0])
    old = solve(initial, 1).certificate
    assert old and verify(initial, old)
    initial.add(blind[1])
    a, ab, aa = primitive(), primitive(add_b=True), primitive(add_composite=True)
    phantom = phantom_models()
    result = {
        "scope": "Exact finite supplied hypotheses; not a learned ARC solver or benchmark score",
        "quantifier_gap": {
            "each_model_has_a_plan": [solve(version_space(m), 1).status for m in blind],
            "one_policy_for_both": solve(version_space(*blind), 1).status,
        },
        "observation_contingent_policy": {
            "budget_1": solve(probes, 1).status, "budget_2": informed.status,
            "first_action": informed.certificate.policy.action if informed.certificate else None,
            "verified": verify(probes, informed.certificate) if informed.certificate else False,
        },
        "uninformative_probe": solve(version_space(
            doors("left-world", "left", True, False),
            doors("right-world", "right", True, False)), 2).status,
        "shared_candidate_identity": {
            "lossy_union_claims_goal": lossy_union_reaches_goal(phantom),
            "actual_common_policy": solve(version_space(*phantom), 2).status,
        },
        "old_certificate_after_model_extension": verify(initial, old),
        "continuation_equivalence": {
            "A_blocks": quotient(a), "A_and_AA_blocks": quotient(aa),
            "A_and_B_blocks": quotient(ab),
            "separating_word_after_B": distinguishing_word(ab, "0", ab, "1"),
        },
        "finite_prefix_is_not_global_equivalence": {
            "shared_initial_view": delayed_chain("yes", 10, True).view("0") == delayed_chain("no", 10, False).view("0"),
            "first_separation_length": len(distinguishing_word(
                delayed_chain("yes", 10, True), "0", delayed_chain("no", 10, False), "0")),
        },
    }
    actual = primitive(add_b=True)

    def trace(word):
        state, events = "0", []
        for action in word:
            step = actual.edges[state, action]
            events.append((action, actual.event(step)))
            state = step.target
        return Episode(actual.view("0"), tuple(events))

    def observed_alphabet(data):
        return tuple(dict.fromkeys([e.initial for e in data] +
                                  [event.view for e in data for _,event in e.events]))

    sparse = (trace(("A","B")), trace(("B",)))
    fuller = tuple(trace(word) for length in range(1,5)
                   for word in product(("A","B"), repeat=length))
    small = synthesize(sparse, observed_alphabet(sparse), 2)
    learned = synthesize(sparse, observed_alphabet(sparse), 3)
    refined = synthesize(fuller, observed_alphabet(fuller), 3)
    result["automatic_candidate_generation"] = {
        "inputs": "Observed traces, observed interface alphabet, state bound; no hidden-state graph",
        "two_states": {"complete": small.complete_for_bound, "candidates": len(small.models)},
        "three_states_sparse": {"complete": learned.complete_for_bound,
            "candidates": len(learned.models), "minimum_states": learned.minimum_consistent_states},
        "three_states_more_interventions": {"complete": refined.complete_for_bound,
            "episodes": len(fuller), "candidates": len(refined.models),
            "all_survivors_continuation_equivalent_to_reference": all(
                distinguishing_word(m,"0",actual,"0") is None for m in refined.models)},
    }
    return result


if __name__ == "__main__":
    result = run()
    Path("results.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
