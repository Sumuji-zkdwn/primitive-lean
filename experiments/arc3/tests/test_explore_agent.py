from pathlib import Path
import hashlib
import json
import random

from arc3.perception import Observation
from explore_agent import ExploreAgent
from vendor.explore.compat import GameAction


def observation(level=0):
    grid = tuple(tuple((x//8+y//8)%2 for x in range(64)) for y in range(64))
    return Observation(grid, (1, 2, 3, 4), level)


def test_upstream_policy_is_seeded_and_does_not_change_global_rng():
    before = random.getstate()
    a, b = ExploreAgent(3), ExploreAgent(3)
    a.observe(observation())
    b.observe(observation())
    assert a.act() == b.act()
    assert random.getstate() == before


def test_retry_behavior_from_upstream_main_is_counted(monkeypatch):
    a = ExploreAgent(3)
    a.observe(observation())
    a.policy.last_action_object = GameAction.ACTION2
    def fail(*args):
        raise KeyError('unregistered frame after suspicious transition')
    monkeypatch.setattr(a.policy, 'choose_action', fail)
    assert a.act().code == 2
    assert a.metrics()['policy_recoveries'] == {'KeyError': 1}
    a.observe(observation())
    assert len(a.monitor.records) == 1


def test_reset_is_not_a_gameplay_transition_and_level_change_refreshes_policy():
    a = ExploreAgent(3)
    a.observe(observation())
    a.act()
    a.after_reset(observation(1))
    assert len(a.monitor.records) == 0
    assert a.policy.last_hashed_frame is None
    assert a.policy.level_up and a.policy.status_bar_mask is None


def test_vendored_files_match_attributed_hashes():
    root = Path(__file__).resolve().parents[1]/'vendor/explore'
    p = json.loads((root/'provenance.json').read_text())
    for name, record in p['files'].items():
        assert hashlib.sha256((root/Path(name).name).read_bytes()).hexdigest() == record['vendored_sha256']
    assert 'Evgenii Rudakov' in (root/'LICENSE').read_text()
