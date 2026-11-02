"""New decision-level experiment motivated by the user's three-lamp report.

Not a reproduction of the unavailable original package or of the quantum PR.
U is explicitly supplied as a legal abstract operation with cost one. The goal
requires restoration before declaring INITIAL parity. Unknown initial states
are represented as a belief, never supplied to the acting policy.
"""
from __future__ import annotations

import json
from pathlib import Path

from core import Model, Node, Step, VersionSpace, solve, verify


def transform(bits: int) -> int:
    """(x0,x1,x2) -> (x0 XOR x1 XOR x2,x1,x2), x0 is bit 0."""
    return bits ^ (((bits >> 1) ^ (bits >> 2)) & 1)


def build_model(name: str = "parity", allow_u: bool = True,
                identity_u: bool = False, full_state_goal: bool = False) -> Model:
    nodes = {"win": Node("success", "win"), "fail": Node("failure", "fail")}
    edges = {}
    for original in range(8):
        for current in range(8):
            state = f"{original}:{current}"
            nodes[state] = Node(str(current & 1))
            if allow_u:
                changed = current if identity_u else transform(current)
                edges[state, "U"] = Step(f"{original}:{changed}")
            answers = range(8) if full_state_goal else range(2)
            truth = original if full_state_goal else original.bit_count() % 2
            for answer in answers:
                # Original state restoration is part of the task, not an observation.
                won = current == original and answer == truth
                edges[state, f"declare-{answer}"] = Step("win" if won else "fail")
    return Model(name, nodes, edges, frozenset(f"{x}:{x}" for x in range(8)))


def initial_space(model: Model, visible_bit: int) -> VersionSpace:
    example = f"{visible_bit}:{visible_bit}"
    space = VersionSpace(model.view(example))
    assert space.add(model)
    return space


def simulate(model: Model, original: int, policy) -> dict:
    state = f"{original}:{original}"
    steps = []
    while policy.action is not None:
        action = policy.action
        step = model.edges[state, action]
        event = model.event(step)
        steps.append({"action": action, "observed": event.view.label, "cost": step.cost})
        state = step.target
        policy = policy.branches[event]
    return {"initial": original, "final_status": model.nodes[state].status,
            "abstract_cost": sum(s["cost"] for s in steps), "trace": steps}


def run() -> dict:
    model = build_model()
    plans = {visible: solve(initial_space(model, visible), 3) for visible in [0,1]}
    assert all(r.certificate for r in plans.values())
    trajectories = [simulate(model, x, plans[x & 1].certificate.policy) for x in range(8)]
    updates = []
    for visible in [0,1]:
        for original in [x for x in range(8) if x & 1 == visible][:2]:
            state = f"{original}:{original}"
            belief = initial_space(model, visible)
            before = len(belief.belief)
            first = model.edges[state, "U"]
            belief.observe("U", model.event(first))
            after_reveal = len(belief.belief)
            goal_values = sorted({int(w.state.split(":")[0]).bit_count() % 2 for w in belief.belief})
            second = model.edges[first.target, "U"]
            belief.observe("U", model.event(second))
            updates.append({"initial_visible_bit": visible, "actual_initial_for_audit_only": original,
                "candidates_before": before, "candidates_after_reveal": after_reveal,
                "possible_initial_parities": goal_values,
                "candidates_after_restore": len(belief.belief),
                "raw_view_restored": model.view(second.target) == belief.initial,
                "all_candidate_states_restored": all(w.state.split(":")[0] == w.state.split(":")[1]
                                                     for w in belief.belief)})
    no_u = build_model(allow_u=False)
    reconstruction = build_model(full_state_goal=True)
    uncertain_operation = initial_space(model, 0)
    assert uncertain_operation.add(build_model("identity-hypothesis", identity_u=True))
    return {
        "scope": "Decision-level extension of the user's report; new explicit model, not original-package replay or ARC score",
        "conditions": {"U_is_legal_and_known": True, "U_cost_in_abstract_calls": 1,
                       "initial_state_unknown": True, "success_requires_restoration": True},
        "verified_policy_by_initial_view": {str(v): verify(initial_space(model,v), r.certificate)
                                             for v,r in plans.items()},
        "budget_two_status": {str(v): solve(initial_space(model,v),2).status for v in [0,1]},
        "all_initial_states_win": all(r["final_status"] == "win" for r in trajectories),
        "worst_abstract_cost": max(r["abstract_cost"] for r in trajectories),
        "belief_updates": updates,
        "without_U_budget_three": solve(initial_space(no_u,0),3).status,
        "full_state_identification_budget_six": solve(initial_space(reconstruction,0),6).status,
        "if_U_might_be_identity_budget_six": solve(uncertain_operation,6).status,
        "trajectories": trajectories,
    }


if __name__ == "__main__":
    result = run()
    Path("parity_probe_results.json").write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({k:v for k,v in result.items() if k != "trajectories"}, indent=2))
