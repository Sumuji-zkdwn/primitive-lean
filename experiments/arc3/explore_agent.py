"""Existing MIT exploration policy plus our opaque-token evidence monitor."""
from contextlib import contextmanager, redirect_stdout
from io import StringIO
import random
from collections import Counter

from arc3.perception import Action
from online import InteractionModel
from vendor.explore.compat import FrameData, GameState
from vendor.explore.heuristic_agent import HeuristicAgent


class ExploreAgent:
    def __init__(self, seed=0):
        self.random_state = random.Random(seed).getstate()
        with self.local_random(), redirect_stdout(StringIO()):
            self.policy = HeuristicAgent(seed=seed)
        self.policy.minimal_step_time = 0  # Disable old online rate limiting.
        self.monitor = InteractionModel(seed)
        self.pending = None
        self.current = None
        self.frames = []
        self.reason = 'upstream-explore-policy'
        self.recoveries = Counter()

    @contextmanager
    def local_random(self):
        old = random.getstate()
        random.setstate(self.random_state)
        try:
            yield
        finally:
            self.random_state = random.getstate()
            random.setstate(old)

    def observe(self, obs):
        if self.pending is None:
            self.monitor.start((obs.grid, obs.available))
        else:
            feedback = float(obs.levels > self.current.levels)
            self.monitor.update(self.pending, (obs.grid, obs.available), feedback)
        if self.current is not None:
            # Move the score/level bookkeeping from upstream's HTTP main loop.
            if obs.levels != self.current.levels:
                self.policy.level_up = True
                self.policy.status_bar_mask = None
            elif self.policy.status_bar_mask is not None:
                self.policy.level_up = False
        self.current = obs
        self.pending = None
        if obs.status == 'GAME_OVER':
            self.policy.last_transition_suspicious = True
        # The policy uses only the last animation frame and the frame count.
        frame = [list(row) for row in obs.grid]
        self.frames.append(FrameData([frame]*obs.animation_count, list(obs.available),
                                     GameState[obs.status], obs.levels))

    def after_reset(self, obs):
        self.pending = None
        self.policy.last_hashed_frame = None
        self.policy.last_action = None
        self.observe(obs)

    def act(self):
        if self.pending is not None:
            raise RuntimeError('Observe the preceding result first')
        with self.local_random(), redirect_stdout(StringIO()):
            try:
                action = self.policy.choose_action(self.frames, self.frames[-1])
                self.reason = 'upstream-explore-policy'
            except (KeyError, ValueError, IndexError) as exc:
                # Upstream main() retries the previous action after policy errors.
                # Retain that behavior and expose it in the evaluation record.
                self.recoveries[type(exc).__name__] += 1
                self.policy.failed = True
                self.policy.level_up = True
                action = self.policy.last_action_object
                self.reason = 'upstream-retry-'+type(exc).__name__
        self.policy.action_counter += 1
        if action.value == 6:
            result = Action(6, int(action.data['x']), int(action.data['y']))
        else:
            result = Action(action.value)
        if result.code not in self.current.available or result.code == 0:
            raise RuntimeError('Upstream policy selected an unavailable action')
        self.pending = result
        return result

    def metrics(self):
        return {'policy_source': 'dolphin-in-a-coma/arc-agi-3-just-explore',
                'policy_ref': 'c2d98318ecca38c8ee9fb49b5af159e51770bad7',
                'upstream_graph_nodes': len(self.policy.graph_explorer._nodes),
                'policy_recoveries': dict(self.recoveries),
                'evidence_monitor': self.monitor.metrics()}
