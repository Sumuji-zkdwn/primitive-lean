"""Empirical interaction model over opaque hashable tokens.

Finite-history refinement is an empirical hypothesis, not a certificate of
continuation equivalence. Numerical feedback is provided by an outer task.
No affine observation law or physical interpretation is assumed.
"""
from collections import Counter, defaultdict
from dataclasses import dataclass, field
import math
import random


@dataclass
class Edge:
    outcomes: Counter = field(default_factory=Counter)
    feedback: float = 0.0

    @property
    def count(self):
        return sum(self.outcomes.values())


class InteractionModel:
    def __init__(self, seed=0, max_depth=4):
        if max_depth < 0:
            raise ValueError("max_depth must be nonnegative")
        self.rng = random.Random(seed)
        self.max_depth = max_depth
        self.depth = 0
        self.records = []
        self.episodes = []
        self.edges = {}
        self.visits = Counter()
        self.predictions = self.correct = self.refinements = 0

    @staticmethod
    def state(history, depth):
        # Include the current observation and at most depth prior action/results.
        return (history[0], tuple(history[1:])) if len(history)-1 <= depth else (
            history[-depth-1][1], tuple(history[-depth:])) if depth else (
                history[-1][1], ())

    def start(self, observation):
        hash(observation)
        self.history = [observation]
        self.episodes.append(self.history)
        self.visits[observation] += 1

    def _rebuild(self):
        self.edges = {}
        for history, action, outcome, feedback in self.records:
            key = (self.state(history, self.depth), action)
            edge = self.edges.setdefault(key, Edge())
            edge.outcomes[outcome] += 1
            edge.feedback += feedback

    def update(self, action, outcome, feedback=0.0):
        if not math.isfinite(feedback):
            raise ValueError("Feedback must be finite")
        hash((action, outcome))
        before = tuple(self.history)
        key = (self.state(before, self.depth), action)
        edge = self.edges.get(key)
        if edge:
            self.predictions += 1
            maximum = max(edge.outcomes.values())
            # Ties have no token-name dependent preferred outcome.
            self.correct += int(edge.outcomes.get(outcome, 0) == maximum)
        self.records.append((before, action, outcome, feedback))
        self.history.append((action, outcome))
        self.visits[outcome] += 1
        if edge is None:
            edge = self.edges.setdefault(key, Edge())
        edge.outcomes[outcome] += 1
        edge.feedback += feedback
        # Revisit all evidence after a refinement; never erase conflicting data.
        if len(edge.outcomes) > 1:
            while self.depth < self.max_depth:
                self.depth += 1
                self.refinements += 1
                self._rebuild()
                if all(len(e.outcomes) <= 1 for e in self.edges.values()):
                    break

    def choose(self, actions):
        actions = tuple(dict.fromkeys(actions))
        if not actions:
            raise ValueError("Supply at least one available action")
        state = self.state(self.history, self.depth)
        untried = [a for a in actions if (state, a) not in self.edges]
        known = [a for a in actions if (state, a) in self.edges]
        # Repeat experiments even when the action space cannot be exhausted.
        if untried and (not known or self.rng.random() < 0.5):
            return self.rng.choice(untried)
        def score(action):
            e = self.edges[state, action]
            novelty = sum(n / math.sqrt(self.visits[o])
                          for o, n in e.outcomes.items()) / e.count
            return e.feedback/e.count + novelty + math.sqrt(
                2 * math.log(2 + len(self.records)) / e.count)
        actions = known
        scores = [score(a) for a in actions]
        best = max(scores)
        return self.rng.choice([a for a, s in zip(actions, scores) if s == best])

    def known_actions(self):
        state = self.state(self.history, self.depth)
        return tuple(a for (s, a) in self.edges if s == state)

    def metrics(self):
        return {"history_depth": self.depth, "refinements": self.refinements,
                "records": len(self.records), "observation_tokens": len(self.visits),
                "state_action_pairs": len(self.edges),
                "unresolved_conflicts": sum(len(e.outcomes)>1 for e in self.edges.values()),
                "prediction_trials": self.predictions,
                "prediction_accuracy_including_ties": self.correct/self.predictions
                    if self.predictions else None}
