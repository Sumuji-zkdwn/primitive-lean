"""Regression evidence from run 40745980582; no SDK/network required."""
import json
from pathlib import Path

import pytest

from arc3.perception import Observation
from explore_agent import (AdapterGraphExplorer, ExploreAgent,
                           GraphTransitionConflict)

CASES = json.loads((Path(__file__).parent / 'fixtures/ft09_reset_paths.json')
                   .read_text(encoding='utf-8'))['cases']


def observation(row):
    return Observation(tuple(map(tuple, row['grid'])), tuple(row['available']),
                       row['levels'], row['status'], row['animation_count'])


@pytest.mark.parametrize('case', CASES, ids=lambda c: f'seed-{c["seed"]}')
def test_ft09_recorded_first_transition_after_game_over_reset(case, monkeypatch):
    agent = ExploreAgent(case['seed'])
    agent.observe(observation(case['terminal']))
    assert agent.policy.last_transition_suspicious
    agent.after_reset(observation(case['reset']))
    assert not agent.policy.last_transition_suspicious
    # Select the recorded segment. Pixels in that segment are randomized by
    # upstream; this tests transition bookkeeping, not an environment replay.
    graph = agent.policy.graph_explorer
    def choose(node, return_reasoning=False):
        return (case['edge'], 'recorded regression segment')
    monkeypatch.setattr(graph, 'choose_edge', choose)
    agent.act()
    source = agent.policy.last_hashed_frame
    agent.observe(observation(case['result']))
    agent.act()
    edge = graph.edge_info(source, case['edge'])
    assert edge['result'] == 1
    assert str(edge['target']) in graph._nodes
    assert (case['edge'], str(edge['target'])) in graph._G[source]
    assert (case['edge'], source) in graph._G_rev[str(edge['target'])]
    assert agent.metrics()['policy_recoveries'] == {}
    assert not graph.suspicious_transitions
    # RESET was not added to the gameplay evidence monitor.
    assert len(agent.monitor.records) == 1


def graph():
    g = AdapterGraphExplorer(n_groups=1)
    g.initialize('A', 2, group2remaining_candidate_ids=[{0, 1}])
    return g


@pytest.mark.parametrize('success', [0, 1])
def test_repeated_test_is_idempotent_on_open_and_closed_nodes(success):
    g = graph()
    kwargs = dict(target_node='B', target_num_candidates=2,
                  group2remaining_candidate_ids=[{0, 1}]) if success else {}
    g.record_test('A', 0, success, **kwargs)
    for closed in (False, True):
        if closed:
            g.record_test('A', 1, 0)
        before = (g._nodes['A'].edge_data.tobytes(),
                  [set(x) for x in g._nodes['A'].group2remaining_candidate_ids],
                  {n: set(e) for n, e in g._G.items()},
                  {n: set(e) for n, e in g._G_rev.items()},
                  set(g._frontier), dict(g._dist), dict(g._next))
        g.record_test('A', 0, success, **kwargs)
        after = (g._nodes['A'].edge_data.tobytes(),
                 g._nodes['A'].group2remaining_candidate_ids,
                 dict(g._G), dict(g._G_rev),
                 g._frontier, g._dist, g._next)
        assert before == after
    assert g.replays == 2


@pytest.mark.parametrize('first,second,target', [(0, 1, 'B'), (1, 0, 'A'), (1, 1, 'C')])
def test_conflicting_replay_does_not_overwrite_or_leave_stale_reverse_edges(first, second, target):
    g = graph()
    g.record_test('A', 0, first, 'B', target_num_candidates=2,
                  group2remaining_candidate_ids=[{0, 1}])
    before = (g._nodes['A'].edge_data.tobytes(), dict(g._dist),
              {n: set(e) for n, e in g._G.items()},
              {n: set(e) for n, e in g._G_rev.items()})
    with pytest.raises(GraphTransitionConflict):
        g.record_test('A', 0, second, target, target_num_candidates=2,
                      group2remaining_candidate_ids=[{0, 1}])
    assert before == (g._nodes['A'].edge_data.tobytes(), g._dist, dict(g._G), dict(g._G_rev))
    assert g.conflicts == 1


def test_unexpected_untested_edge_corruption_still_raises_assertion():
    g = graph()
    g._nodes['A'].edge_data['distance'][0] = 1
    with pytest.raises(AssertionError, match='must be untested'):
        g.record_test('A', 0, 0)


def test_policy_recovery_clears_all_dependent_state_and_reinitializes(monkeypatch):
    agent = ExploreAgent(0)
    obs = observation(CASES[0]['reset'])
    agent.observe(obs)
    agent.act()
    agent.observe(obs)
    original = agent.policy.choose_action
    def conflict(*args):
        raise GraphTransitionConflict('regression conflict')
    monkeypatch.setattr(agent.policy, 'choose_action', conflict)
    agent.act()
    assert agent.policy.graph_explorer.empty
    assert agent.policy.hashed_frame2action_results == {}
    assert agent.policy.hashed_frame2transitions == {}
    assert agent.policy.last_hashed_frame is None
    assert agent.policy.last_action is None
    assert agent.policy.status_bar_mask is None
    agent.observe(obs)
    assert agent.policy.level_up  # observe must not cancel the pending restart.
    monkeypatch.setattr(agent.policy, 'choose_action', original)
    agent.act()
    assert not agent.policy.graph_explorer.empty
    assert agent.metrics()['policy_recoveries'] == {'GraphTransitionConflict': 1}


def test_level_change_reset_rebuilds_graph_without_connecting_episodes():
    agent = ExploreAgent(0)
    obs = observation(CASES[0]['reset'])
    agent.observe(obs)
    agent.act()
    new = Observation(obs.grid, obs.available, obs.levels + 1)
    agent.after_reset(new)
    agent.act()
    assert len(agent.policy.graph_explorer._nodes) == 1
    assert not any(agent.policy.graph_explorer._G.values())
    assert len(agent.monitor.records) == 0
