from core import solve, verify
from parity_probe import build_model, initial_space, simulate


def test_policy_extracts_goal_and_restores_without_knowing_full_state():
    model = build_model()
    for visible in [0,1]:
        space = initial_space(model, visible)
        result = solve(space,3)
        assert result.certificate and verify(space,result.certificate)
        assert result.certificate.policy.action == "U"
        assert solve(space,2).status == "infeasible-in-class"
        for original in range(visible,8,2):
            trace = simulate(model,original,result.certificate.policy)
            assert trace["final_status"] == "win"
            assert trace["abstract_cost"] <= 3


def test_uncompute_restores_screen_but_does_not_erase_learned_information():
    model = build_model()
    for original in range(8):
        space = initial_space(model,original & 1)
        assert len(space.belief) == 4
        state = f"{original}:{original}"
        for _ in range(2):
            step = model.edges[state,"U"]
            space.observe("U",model.event(step))
            state = step.target
        assert model.view(state) == space.initial
        assert len(space.belief) == 2
        possible = {int(w.state.split(":")[0]).bit_count() % 2 for w in space.belief}
        assert possible == {original.bit_count() % 2}


def test_invertibility_alone_does_not_supply_observability():
    model = build_model()
    space = initial_space(model,0)
    assert space.add(build_model("identity",identity_u=True))
    assert solve(space,6).status == "infeasible-in-class"


def test_planner_cannot_invent_the_required_external_operation():
    model = build_model(allow_u=False)
    assert solve(initial_space(model,0),3).status == "infeasible-in-class"


def test_goal_information_does_not_imply_complete_identification():
    model = build_model(full_state_goal=True)
    assert solve(initial_space(model,0),6).status == "infeasible-in-class"
