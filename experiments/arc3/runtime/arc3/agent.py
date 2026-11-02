from __future__ import annotations

import math
import random
from collections import deque

from .model import WorldModel
from .perception import Action, Observation, action_family, candidate_actions
from .representation import CounterRepresentation


class WorldModelAgent:
    """Closed-loop frontier planning on a learned observation transition graph."""

    def __init__(self, seed: int = 0, planning_nodes: int = 2048,
                 abstract_counters: bool = True) -> None:
        self.rng = random.Random(seed)
        self.model = WorldModel()
        self.planning_nodes = planning_nodes
        self.previous: tuple[Observation, Action] | None = None
        self.current: Observation | None = None
        self.reason = "initial"
        self.predictions = 0
        self.correct_predictions = 0
        self.last_effective: Action | None = None
        self.representation = CounterRepresentation(abstract_counters)
        self.history: list[tuple[Observation, Action | None]] = []
        self.representation_rebuilds = 0

    def observe(self, obs: Observation) -> None:
        action = self.previous[1] if self.previous else None
        self.history.append((obs, action))
        if self.representation.update(obs, action):
            # Re-encode all actual experience; never invent transitions when merging states.
            self.representation_rebuilds += 1
            self.model = WorldModel()
            self.current = None
            for raw, taken in self.history:
                self.previous = (self.current, taken) if self.current and taken else None
                self._observe(self.representation.transform(raw), count_prediction=False)
        else:
            self._observe(self.representation.transform(obs))

    def _observe(self, obs: Observation, count_prediction: bool = True) -> None:
        key = obs.key
        if self.previous is not None:
            before, action = self.previous
            old = self.model.edges.get(before.key, {}).get(action)
            if old is not None and count_prediction:
                self.predictions += 1
                self.correct_predictions += int(old.mode[0] == key)
            reward = max(0, obs.levels - before.levels) + int(obs.status == "WIN")
            failed = obs.status == "GAME_OVER"
            self.model.update(before.key, action, key, reward, failed,
                              action_family(before, action))
            self.last_effective = action if key != before.key and not failed else None
        self.previous = None
        self.current = obs
        self.model.observe(key, [] if obs.terminal else candidate_actions(obs), obs.terminal)

    def after_reset(self, obs: Observation) -> None:
        # A reset is not the result of the previous gameplay action. Keep experience,
        # but break temporal credit assignment across episodes.
        self.previous = None
        self.last_effective = None
        self.observe(obs)

    def _rank(self, obs: Observation, action: Action) -> float:
        trials, changes, failures = self.model.families.get(action_family(obs, action), [0, 0, 0])
        effectiveness = (changes + 1)/(trials + 2)
        risk = failures/(trials + 2)
        exploration = 0.6*math.sqrt(math.log(2+len(self.history))/(1+trials))
        # A mild persistence prior helps explore movement without assuming action directions.
        persistence = 0.25 if action == self.last_effective and action.code != 6 else 0.0
        return effectiveness + exploration - 2*risk + persistence + self.rng.random()*0.3

    def _plan(self, source: str, seek_reward: bool = False) -> Action | None:
        queue: deque[tuple[str, Action | None]] = deque([(source, None)])
        seen = {source}
        expanded = 0
        while queue and expanded < self.planning_nodes:
            state, first = queue.popleft()
            expanded += 1
            if not seek_reward and state != source and self.model.frontier(state):
                return first
            edges = list(self.model.edges.get(state, {}).items())
            self.rng.shuffle(edges)
            for action, edge in edges:
                target, confidence = edge.mode
                if seek_reward and edge.reward_sum > 0 and not edge.failures and confidence >= 0.8:
                    return action if first is None else first
                if (confidence < 0.8 or edge.failures or target in seen
                        or target in self.model.terminals):
                    continue
                seen.add(target)
                queue.append((target, action if first is None else first))
        return None

    def act(self) -> Action:
        obs = self.current
        if obs is None:
            raise RuntimeError("Observe a frame before acting")
        if obs.terminal:
            raise RuntimeError("Do not act on a terminal frame")
        if self.previous is not None:
            raise RuntimeError("Observe the result before requesting another action")
        actions = self.model.actions[obs.key]
        if not actions:
            raise RuntimeError("No legal gameplay action is available")
        known_progress = self._plan(obs.key, seek_reward=True)
        if known_progress is not None:
            self.reason = "route-to-known-progress"
            self.previous = (obs, known_progress)
            return known_progress
        # Preserve eventual coverage of pixels that are absent from object/lattice proposals.
        if 6 in obs.available and self.rng.random() < 0.08:
            action = Action(6, self.rng.randrange(len(obs.grid[0])), self.rng.randrange(len(obs.grid)))
            self.reason = "pixel-coverage"
        else:
            frontier = self.model.frontier(obs.key)
            if frontier:
                action = max(frontier, key=lambda a: self._rank(obs, a))
                self.reason = "experiment"
            else:
                action = self._plan(obs.key)
                self.reason = "route-to-experiment"
                if action is None:
                    known = self.model.edges.get(obs.key, {})

                    def score(a: Action) -> float:
                        t = known.get(a)
                        if t is None:
                            return 2.0 + self._rank(obs, a)
                        progress = t.reward_sum/t.count
                        novelty = sum(n/math.sqrt(1+self.model.visits[s])
                                      for s, n in t.outcomes.items()) / t.count
                        return (4*progress + novelty + 1/math.sqrt(1+t.count)
                                - 2*t.failures/t.count + 0.05*self._rank(obs, a))

                    action = max(actions, key=score)
                    self.reason = "revisit"
        self.previous = (obs, action)
        return action

    def metrics(self) -> dict:
        return {
            "states": len(self.model.visits),
            "state_action_pairs": sum(len(aa) for aa in self.model.edges.values()),
            "repeated_transition_predictions": self.predictions,
            "prediction_accuracy": (self.correct_predictions/self.predictions
                                    if self.predictions else None),
            "ambiguous_state_action_pairs": sum(len(t.outcomes) > 1
                for aa in self.model.edges.values() for t in aa.values()),
            "representation_rebuilds": self.representation_rebuilds,
            "excluded_border_rows": {str(level): sorted(rows)
                                     for level, rows in self.representation.rows_by_level.items()},
        }
