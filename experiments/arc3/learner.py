"""Bounded finite-state hypothesis synthesis from observable traces.

Enumerates deterministic machines, not a catalogue of puzzle rules. Completeness
is ONLY relative to the supplied observation/cost alphabets and state bound.
This is deliberately an exact small reference, not a scalable ARC synthesizer.
"""
from __future__ import annotations

from dataclasses import dataclass
from itertools import product

from core import Event, Model, Node, Step, View


@dataclass(frozen=True)
class Episode:
    initial: View
    events: tuple[tuple[str, Event], ...]


@dataclass(frozen=True)
class Synthesis:
    models: tuple[Model, ...]
    checked_tables: int
    complete_for_bound: bool
    max_states: int
    minimum_consistent_states: int | None


def synthesize(episodes: tuple[Episode, ...], views: tuple[View, ...], max_states: int,
               costs: tuple[int, ...] = (1,), max_tables: int = 100000,
               max_models: int = 10000) -> Synthesis:
    if not episodes or max_states < 1 or max_tables < 1 or max_models < 1:
        raise ValueError("Supply evidence and positive synthesis limits")
    initial = episodes[0].initial
    if any(e.initial != initial for e in episodes):
        raise ValueError("This reference assumes a fixed reset observation/state")
    views = tuple(dict.fromkeys(views))
    costs = tuple(sorted(set(costs)))
    if not costs or any(not isinstance(c, int) or c < 1 for c in costs):
        raise ValueError("Positive integer cost alphabet required")
    for view in views:
        if view.status not in {"active", "win", "fail"}:
            raise ValueError("Unknown terminal status")
        if view.actions != tuple(sorted(set(view.actions))):
            raise ValueError("Canonical action sets required")
        if view.status != "active" and view.actions:
            raise ValueError("Terminal views cannot have actions")
    observed = {initial} | {event.view for episode in episodes for _,event in episode.events}
    if not observed <= set(views):
        raise ValueError("Observation alphabet omits recorded evidence")
    if any(event.cost not in costs for e in episodes for _,event in e.events):
        raise ValueError("Cost alphabet omits recorded evidence")
    models, seen = [], set()
    checked = 0
    minimum = None

    def result(complete: bool) -> Synthesis:
        return Synthesis(tuple(models), checked, complete, max_states, minimum)

    for n in range(1, max_states+1):
        for tail in product(views, repeat=n-1):
            labels = (initial,) + tail
            if not observed <= set(labels):
                continue
            slots = [(s,a) for s in range(n) for a in labels[s].actions]
            choices = tuple(product(range(n), costs))
            for targets in product(choices, repeat=len(slots)):
                if checked >= max_tables:
                    return result(False)
                checked += 1
                edges = dict(zip(slots, targets))
                consistent = True
                for episode in episodes:
                    state = 0
                    for action, event in episode.events:
                        step = edges.get((state, action))
                        if step is None or step[1] != event.cost or labels[step[0]] != event.view:
                            consistent = False
                            break
                        state = step[0]
                    if not consistent:
                        break
                if not consistent:
                    continue
                # Canonical reachable-state numbering removes mere state renamings.
                order = [0]
                ids = {0: 0}
                for state in order:
                    for action in labels[state].actions:
                        target, _ = edges[state, action]
                        if target not in ids:
                            ids[target] = len(order)
                            order.append(target)
                if len(order) != n:
                    continue  # An equivalent smaller reachable machine is enumerated separately.
                key = tuple((labels[s], tuple((a, ids[edges[s,a][0]], edges[s,a][1])
                                             for a in labels[s].actions)) for s in order)
                if key in seen:
                    continue
                if len(models) >= max_models:
                    return result(False)
                seen.add(key)
                if minimum is None:
                    minimum = n
                model = Model(f"inferred-{n}-{len(models)}",
                    {str(ids[s]): Node(labels[s].label, labels[s].status) for s in order},
                    {(str(ids[s]), a): Step(str(ids[t]), cost)
                     for (s,a),(t,cost) in edges.items()}, frozenset({"0"}))
                models.append(model)
    return result(True)
