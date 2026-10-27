from types import SimpleNamespace

import pytest

from arc3.agent import WorldModelAgent
from arc3.model import WorldModel
from arc3.perception import Action, Observation, candidate_actions, components
from arc3.synthetic import Maze


def obs(value=0, levels=0, status="NOT_FINISHED", available=(1,2)):
    return Observation(((value, 0), (0, 0)), available, levels, status)


def test_transition_counts_and_checkpoint_roundtrip(tmp_path):
    model = WorldModel()
    a = Action(1)
    model.observe("a", [a])
    model.update("a", a, "b", 1, False, "1")
    model.update("a", a, "c", 0, True, "1")
    path = tmp_path / "model.json"
    model.save(path)
    restored = WorldModel.load(path)
    edge = restored.edges["a"][a]
    assert dict(edge.outcomes) == {"b": 1, "c": 1}
    assert edge.entropy == 1
    assert edge.failures == 1
    assert restored.frontier("a") == [a]
    assert restored.families == model.families


def test_bfs_uses_experienced_route_to_unexplored_action():
    agent = WorldModelAgent()
    agent.model.observe("a", [Action(1), Action(2)])
    agent.model.observe("b", [Action(1)])
    agent.model.update("a", Action(1), "a", 0, False, "1")
    agent.model.update("a", Action(2), "b", 0, False, "2")
    assert agent._plan("a") == Action(2)


def test_bfs_does_not_route_through_conflicting_or_failed_edge():
    agent = WorldModelAgent()
    for key in ["a", "b", "c"]:
        agent.model.observe(key, [Action(1)])
    agent.model.update("a", Action(1), "b", 0, False, "1")
    agent.model.update("a", Action(1), "c", 0, False, "1")
    assert agent._plan("a") is None


def test_known_progress_is_exploited_before_more_experiments():
    agent = WorldModelAgent()
    start = obs()
    agent.observe(start)
    agent.model.observe("b", [Action(1)])
    agent.model.observe("win", [], terminal=True)
    agent.model.update(start.key, Action(2), "b", 0, False, "2")
    agent.model.update("b", Action(1), "win", 1, False, "1")
    assert agent.act() == Action(2)
    assert agent.reason == "route-to-known-progress"


def test_reset_does_not_create_spurious_transition():
    agent = WorldModelAgent()
    agent.observe(obs())
    agent.act()
    agent.after_reset(obs(2))
    assert not agent.model.edges
    assert agent.previous is None


def test_win_and_level_change_do_not_alias_same_pixels():
    assert len({obs().key, obs(levels=1).key, obs(status="WIN").key,
                obs(available=(1,)).key}) == 4


def test_actions_are_legal_and_clicks_are_in_bounds():
    frame = Observation(((0,1,0), (0,1,0), (0,0,0)), (0,6,7))
    actions = candidate_actions(frame)
    assert Action(7) in actions
    assert Action(6,1,0) in actions or Action(6,1,1) in actions
    assert all(a.code in (6,7) for a in actions)
    assert all(0 <= a.x < 3 and 0 <= a.y < 3 for a in actions if a.code == 6)
    agent = WorldModelAgent()
    for _ in range(100):
        agent.observe(frame)
        action = agent.act()
        assert action.code in (6,7)
        if action.code == 6:
            assert 0 <= action.x < 3 and 0 <= action.y < 3


def test_component_center_is_inside_concave_object():
    grid = ((1,1,1),(1,0,0),(1,1,1))
    comp = next(c for c in components(grid) if c.color == 1)
    x,y = comp.center
    assert grid[y][x] == 1


def test_sdk_uses_last_animation_frame_and_validates():
    raw = SimpleNamespace(frame=[[[0]], [[3]]], available_actions=[1],
                          levels_completed=0, state=SimpleNamespace(name="NOT_FINISHED"))
    assert Observation.from_sdk(raw).grid == ((3,),)
    with pytest.raises(ValueError):
        Observation((), (1,))
    with pytest.raises(ValueError):
        Action(6, 64, 0)


def test_terminal_and_double_action_are_rejected():
    agent = WorldModelAgent()
    agent.observe(obs(status="WIN"))
    with pytest.raises(RuntimeError):
        agent.act()
    agent.observe(obs())
    agent.act()
    with pytest.raises(RuntimeError):
        agent.act()


@pytest.mark.parametrize("seed", range(10))
def test_generated_maze_with_unknown_controls(seed):
    maze = Maze(seed, size=7)
    agent = WorldModelAgent(seed)
    frame = maze.observation()
    agent.observe(frame)
    for _ in range(500):
        if frame.terminal:
            break
        frame = maze.step(agent.act())
        agent.observe(frame)
    assert frame.status == "WIN"
