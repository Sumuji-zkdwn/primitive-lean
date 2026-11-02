"""Existing MIT exploration policy plus our opaque-token evidence monitor."""
from contextlib import contextmanager, redirect_stdout
from io import StringIO
import random
from collections import Counter

from arc3.perception import Action
from online import InteractionModel
from vendor.explore.compat import FrameData, GameState
from vendor.explore.heuristic_agent import HeuristicAgent
from vendor.explore.graph_explorer import GraphExplorer


class GraphTransitionConflict(ValueError):
    """The masked frame/segment abstraction produced contradictory evidence."""


class AdapterGraphExplorer(GraphExplorer):
    """Separate traversal of a known edge from a first upstream probe.

    Keep NodeInfo.record_test's untested-edge invariant intact. A matching
    replay does not change graph topology, groups, or frontier distances.
    A conflicting replay requires a fresh graph, never an edge overwrite.
    """

    def __init__(self, **kwargs):
        self.replays = 0
        self.conflicts = 0
        super().__init__(**kwargs)

    def record_test(self, node, edge_idx, success, target_node=None, **kwargs):
        if node in self._nodes:
            edge = self.edge_info(node, edge_idx)
            result = int(edge['result'])
            if result != 0:
                matches = ((result == 1 and success == 1 and
                            str(target_node) == edge['target']) or
                           (result == -1 and success == 0))
                if matches:
                    self.replays += 1
                    return
                self.conflicts += 1
                raise GraphTransitionConflict(
                    f'Conflicting replay of {node}/{edge_idx}: '
                    f'{result}/{edge["target"]} -> {success}/{target_node}')
        return super().record_test(node, edge_idx, success, target_node, **kwargs)


class ExploreAgent:
    def __init__(self, seed=0):
        self.random_state = random.Random(seed).getstate()
        with self.local_random(), redirect_stdout(StringIO()):
            self.policy = HeuristicAgent(seed=seed)
        self.policy.minimal_step_time = 0  # Disable old online rate limiting.
        self.policy.graph_explorer = AdapterGraphExplorer(
            verbose_level=self.policy.verbose_level, n_groups=self.policy.N_GROUPS)
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
        # GAME_OVER taints the preceding gameplay transition, which the runner
        # already ended. RESET is external to choose_action; its result must
        # not taint the first real gameplay action of the new episode.
        self.policy.last_transition_suspicious = False
        self.observe(obs)

    def restart_policy_graph(self):
        # choose_action may have changed its per-frame caches before raising.
        # Reset every dependent structure together; keep monitor evidence.
        self.policy.graph_explorer.reset()
        self.policy.hashed_frame2action_results = {}
        self.policy.hashed_frame2transitions = {}
        self.policy.last_hashed_frame = None
        self.policy.last_action = None
        self.policy.last_transition_suspicious = False
        self.policy.status_bar_mask = None
        self.policy.level_up = True

    def act(self):
        if self.pending is not None:
            raise RuntimeError('Observe the preceding result first')
        with self.local_random(), redirect_stdout(StringIO()):
            try:
                action = self.policy.choose_action(self.frames, self.frames[-1])
                self.reason = 'upstream-explore-policy'
            except (KeyError, ValueError, IndexError) as exc:
                # Preserve the upstream physical retry, but do not attribute
                # its result to an old source node/action. Reinitialize all
                # policy caches together on the following decision.
                self.recoveries[type(exc).__name__] += 1
                action = self.policy.last_action_object
                self.restart_policy_graph()
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
                'graph_matching_replays': self.policy.graph_explorer.replays,
                'graph_conflicting_replays': self.policy.graph_explorer.conflicts,
                'policy_recoveries': dict(self.recoveries),
                'evidence_monitor': self.monitor.metrics()}
