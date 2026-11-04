"""Exact finite hypothesis core: continuation equivalence and shared-policy search.

No pixel, object, color, direction, or game-specific semantics are assumed.
The candidate models are supplied, NOT discovered by this module. Certificates
are conditional on these finite deterministic models and their observation API.
"""
from __future__ import annotations

from collections import defaultdict, deque
from dataclasses import dataclass
from hashlib import sha256
import json
from types import MappingProxyType
from typing import Mapping


@dataclass(frozen=True)
class Node:
    label: str
    status: str = "active"

    def __post_init__(self):
        if self.status not in {"active", "win", "fail"}:
            raise ValueError("Invalid terminal status")


@dataclass(frozen=True)
class Step:
    target: str
    cost: int = 1

    def __post_init__(self):
        if not isinstance(self.cost, int) or self.cost < 1:
            raise ValueError("Costs must be positive integers")


@dataclass(frozen=True)
class View:
    label: str
    actions: tuple[str, ...]
    status: str


@dataclass(frozen=True)
class Event:
    view: View
    cost: int


@dataclass(frozen=True)
class Model:
    name: str
    nodes: Mapping[str, Node]
    edges: Mapping[tuple[str, str], Step]
    starts: frozenset[str]

    def __post_init__(self):
        object.__setattr__(self, "nodes", MappingProxyType(dict(self.nodes)))
        object.__setattr__(self, "edges", MappingProxyType(dict(self.edges)))
        object.__setattr__(self, "starts", frozenset(self.starts))
        if not self.starts or not self.starts <= self.nodes.keys():
            raise ValueError("Every start must be a known state")
        for (source, _), step in self.edges.items():
            if source not in self.nodes or step.target not in self.nodes:
                raise ValueError("An edge references an unknown state")
            if self.nodes[source].status != "active":
                raise ValueError("Terminal states cannot have outgoing actions")

    def view(self, state: str) -> View:
        n = self.nodes[state]
        actions = tuple(sorted(a for s, a in self.edges if s == state))
        return View(n.label, actions, n.status)

    def event(self, step: Step) -> Event:
        return Event(self.view(step.target), step.cost)

    def description(self) -> dict:
        return {
            "name": self.name,
            "nodes": sorted((s, n.label, n.status) for s, n in self.nodes.items()),
            "edges": sorted((s, a, t.target, t.cost) for (s, a), t in self.edges.items()),
            "starts": sorted(self.starts),
        }


@dataclass(frozen=True, order=True)
class World:
    model: str
    state: str


Belief = frozenset[World]


def successors(models: Mapping[str, Model], belief: Belief,
               action: str) -> dict[Event, Belief]:
    groups: dict[Event, set[World]] = defaultdict(set)
    for world in belief:
        model = models[world.model]
        step = model.edges.get((world.state, action))
        if step is not None:
            # Retain the SAME candidate identity across all stages of a trajectory.
            groups[model.event(step)].add(World(world.model, step.target))
    return {event: frozenset(worlds) for event, worlds in groups.items()}


class VersionSpace:
    """Candidate insertion always replays the complete observed history."""

    def __init__(self, initial: View):
        self.initial = initial
        self.models: dict[str, Model] = {}
        self.belief: Belief = frozenset()
        self.history: list[tuple[str, Event]] = []

    def add(self, model: Model) -> bool:
        if model.name in self.models:
            raise ValueError("Candidate names must be unique")
        states = {s for s in model.starts if model.view(s) == self.initial}
        for action, event in self.history:
            states = {step.target for s in states
                      if (step := model.edges.get((s, action))) is not None
                      and model.event(step) == event}
        if not states:
            return False
        self.models[model.name] = model
        self.belief |= frozenset(World(model.name, s) for s in states)
        return True

    def observe(self, action: str, event: Event) -> None:
        self.belief = successors(self.models, self.belief, action).get(event, frozenset())
        self.history.append((action, event))
        # An empty belief signals model-class mismatch, not environmental impossibility.

    def fingerprint(self) -> str:
        data = {
            "models": [self.models[n].description() for n in sorted(self.models)],
            "belief": [(w.model, w.state) for w in sorted(self.belief)],
            "initial": repr(self.initial),
            "history": [(a, repr(e)) for a, e in self.history],
        }
        return sha256(json.dumps(data, sort_keys=True).encode()).hexdigest()


def quotient(model: Model) -> dict[str, int]:
    """Greatest deterministic continuation equivalence for the declared interface.

    Availability, terminal status, and observed transition costs are preserved.
    This computes equivalence in a supplied finite model; it does not infer it
    from a finite sample of an unrestricted unknown environment.
    """
    def assign(signatures):
        ids = {}
        return {state: ids.setdefault(signature, len(ids))
                for state, signature in signatures}

    states = sorted(model.nodes)
    blocks = assign((s, model.view(s)) for s in states)
    while True:
        refined = assign((s, (model.view(s), tuple(
            (a, model.edges[s, a].cost, blocks[model.edges[s, a].target])
            for a in model.view(s).actions))) for s in states)
        if refined == blocks:
            return refined
        blocks = refined


def distinguishing_word(left: Model, x: str, right: Model, y: str) -> tuple[str, ...] | None:
    """Shortest common executable word distinguishing views or observed costs.

    () means the current interfaces already differ. None means exact finite
    continuation equivalence, including action availability and terminal status.
    """
    queue = deque([(x, y, ())])
    seen = {(x, y)}
    while queue:
        x, y, word = queue.popleft()
        if left.view(x) != right.view(y):
            return word
        for action in left.view(x).actions:
            u, v = left.edges[x, action], right.edges[y, action]
            next_word = word + (action,)
            if u.cost != v.cost or left.view(u.target) != right.view(v.target):
                return next_word
            pair = (u.target, v.target)
            if pair not in seen:
                seen.add(pair)
                queue.append((*pair, next_word))
    return None


@dataclass(frozen=True)
class Policy:
    action: str | None
    branches: Mapping[Event, Policy]

    def __post_init__(self):
        object.__setattr__(self, "branches", MappingProxyType(dict(self.branches)))


@dataclass(frozen=True)
class Certificate:
    fingerprint: str
    budget: int
    policy: Policy


@dataclass(frozen=True)
class Result:
    status: str  # solved, infeasible-in-class, search-exhausted, no-model
    expanded: int
    certificate: Certificate | None = None


class _Limit(Exception):
    pass


def solve(space: VersionSpace, budget: int, max_nodes: int = 20000) -> Result:
    """Find one observation-contingent policy winning in every surviving world.

    Searches the given finite deterministic class exactly unless max_nodes is hit.
    Positive action costs make the budget-limited search well founded. No model can be
    chosen separately for each branch or each action. The first feasible policy
    is returned; this is not an optimal-cost or probabilistic-risk solver.
    """
    if budget < 0 or max_nodes < 1:
        raise ValueError("Invalid planning limits")
    if not space.belief:
        return Result("no-model", 0)
    memo: dict[tuple[Belief, int], Policy | None] = {}
    expanded = 0

    def visit(belief: Belief, remaining: int) -> Policy | None:
        nonlocal expanded
        key = (belief, remaining)
        if key in memo:
            return memo[key]
        if expanded >= max_nodes:
            raise _Limit
        expanded += 1
        statuses = {space.models[w.model].nodes[w.state].status for w in belief}
        if statuses == {"win"}:
            return Policy(None, {})
        if "fail" in statuses or remaining <= 0:
            return None
        legal = set.intersection(*(set(space.models[w.model].view(w.state).actions)
                                   for w in belief))
        for action in sorted(legal):
            branches = {}
            for event, next_belief in successors(space.models, belief, action).items():
                if event.cost > remaining:
                    break
                policy = yield (next_belief, remaining-event.cost)
                if policy is None:
                    break
                branches[event] = policy
            else:
                policy = Policy(action, branches)
                memo[key] = policy
                return policy
        memo[key] = None
        return None

    # Drive the same depth-first traversal explicitly: each generator holds one
    # search frame, without consuming a Python call stack frame per action.
    try:
        stack = [visit(space.belief, budget)]
        policy = None
        while stack:
            try:
                belief, remaining = stack[-1].send(policy)
                policy = None
            except StopIteration as finished:
                stack.pop()
                policy = finished.value
                continue
            key = (belief, remaining)
            if key in memo:
                policy = memo[key]
            else:
                stack.append(visit(belief, remaining))
    except _Limit:
        return Result("search-exhausted", expanded)
    if policy is None:
        return Result("infeasible-in-class", expanded)
    cert = Certificate(space.fingerprint(), budget, policy)
    return Result("solved", expanded, cert)


def verify(space: VersionSpace, certificate: Certificate) -> bool:
    """Independent traversal of the policy on every represented candidate world."""
    if not space.belief or certificate.fingerprint != space.fingerprint():
        return False

    stack = [(space.belief, certificate.budget, certificate.policy)]
    while stack:
        belief, remaining, policy = stack.pop()
        if not belief or remaining < 0:
            return False
        if policy.action is None:
            if policy.branches or not all(
                space.models[w.model].nodes[w.state].status == "win" for w in belief
            ):
                return False
            continue
        if any((w.state, policy.action) not in space.models[w.model].edges for w in belief):
            return False
        branches = successors(space.models, belief, policy.action)
        if branches.keys() != policy.branches.keys():
            return False
        stack.extend((next_belief, remaining-event.cost, policy.branches[event])
                     for event, next_belief in branches.items())
    return True
