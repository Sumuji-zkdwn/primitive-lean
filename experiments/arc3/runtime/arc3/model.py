from __future__ import annotations

import json
import math
from collections import Counter
from dataclasses import dataclass, field
from pathlib import Path

from .perception import Action


@dataclass
class Transition:
    outcomes: Counter[str] = field(default_factory=Counter)
    reward_sum: float = 0.0
    failures: int = 0

    @property
    def count(self) -> int:
        return self.outcomes.total()

    @property
    def entropy(self) -> float:
        return -sum((n/self.count)*math.log2(n/self.count) for n in self.outcomes.values())

    @property
    def mode(self) -> tuple[str, float]:
        target, n = self.outcomes.most_common(1)[0]
        return target, n/self.count


class WorldModel:
    """Empirical P(next observation | observation, action).

    Multiple outcomes remain explicit: a rendered frame need not be Markov.
    The model never queries a simulator, game source, or hidden state.
    """

    def __init__(self) -> None:
        self.edges: dict[str, dict[Action, Transition]] = {}
        self.actions: dict[str, list[Action]] = {}
        self.visits: Counter[str] = Counter()
        self.terminals: set[str] = set()
        self.families: dict[str, list[int]] = {}  # trials, changes, failures

    def observe(self, key: str, actions: list[Action], terminal: bool = False) -> None:
        self.visits[key] += 1
        self.actions[key] = actions
        if terminal:
            self.terminals.add(key)

    def update(self, source: str, action: Action, target: str, reward: float,
               failed: bool, family: str) -> None:
        edge = self.edges.setdefault(source, {}).setdefault(action, Transition())
        edge.outcomes[target] += 1
        edge.reward_sum += reward
        edge.failures += int(failed)
        stats = self.families.setdefault(family, [0, 0, 0])
        stats[0] += 1
        stats[1] += int(source != target)
        stats[2] += int(failed)

    def frontier(self, key: str) -> list[Action]:
        if key in self.terminals:
            return []
        known = self.edges.get(key, {})
        # Re-sample conflicting transitions, but do not treat entropy as endless novelty.
        return [a for a in self.actions.get(key, [])
                if a not in known or (len(known[a].outcomes) > 1 and known[a].count < 4)]

    def save(self, path: str | Path) -> None:
        data = {
            "format": 1,
            "visits": dict(self.visits),
            "terminals": sorted(self.terminals),
            "actions": {s: [a.token() for a in aa] for s, aa in self.actions.items()},
            "families": self.families,
            "edges": {s: {a.token(): {"outcomes": dict(t.outcomes),
                                      "reward_sum": t.reward_sum, "failures": t.failures}
                           for a, t in aa.items()} for s, aa in self.edges.items()},
        }
        Path(path).write_text(json.dumps(data, sort_keys=True), encoding="utf-8")

    @classmethod
    def load(cls, path: str | Path) -> WorldModel:
        data = json.loads(Path(path).read_text(encoding="utf-8"))
        if data["format"] != 1:
            raise ValueError("Unsupported world model format")
        model = cls()
        model.visits = Counter(data["visits"])
        model.terminals = set(data["terminals"])
        model.actions = {s: [Action.parse(a) for a in aa] for s, aa in data["actions"].items()}
        model.families = data["families"]
        model.edges = {s: {Action.parse(a): Transition(Counter(t["outcomes"]),
                          t["reward_sum"], t["failures"]) for a, t in aa.items()}
                       for s, aa in data["edges"].items()}
        return model
