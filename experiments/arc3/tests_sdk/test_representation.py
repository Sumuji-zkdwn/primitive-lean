from arc3.agent import WorldModelAgent
from arc3.perception import Action, Observation
from arc3.representation import CounterRepresentation


def frame(t, *, terminal=False, oscillating=False):
    fill = t if not oscillating else t % 2
    grid = ((1,)*fill + (0,)*(64-fill),) + ((0,)*64,)*63
    return Observation(grid, (1,2,3), 0, "GAME_OVER" if terminal else "NOT_FINISHED")


def test_monotonic_counter_is_detected_and_status_preserved():
    rep = CounterRepresentation()
    for t in range(32):
        changed = rep.update(frame(t), Action(1+t%3))
    assert changed
    assert rep.rows_by_level == {0: {0}}
    assert rep.transform(frame(31)).key == rep.transform(frame(2)).key
    assert rep.transform(frame(31, terminal=True)).key != rep.transform(frame(31)).key


def test_oscillating_border_is_not_removed():
    rep = CounterRepresentation()
    for t in range(32):
        rep.update(frame(t, oscillating=True), Action(1+t%3))
    assert rep.rows_by_level == {}


def test_static_label_beside_counter_does_not_block_detection():
    rep = CounterRepresentation()
    for t in range(32):
        row = (1,)*t + (0,)*(40-t) + (2,3)*12
        obs = Observation((row,) + ((0,)*64,)*63, (1,2,3))
        rep.update(obs, Action(1+t%3))
    assert rep.rows_by_level == {0: {0}}


def test_abstraction_rebuild_preserves_all_real_transitions():
    agent = WorldModelAgent()
    for t in range(32):
        agent.observe(frame(t))
        if t < 31:
            agent.act()
    assert agent.representation_rebuilds == 1
    assert sum(edge.count for aa in agent.model.edges.values() for edge in aa.values()) == 31
    assert len(agent.model.visits) == 1
    assert agent.predictions == 0  # Replay is not a live predictive test.
