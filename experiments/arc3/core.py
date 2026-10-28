"""Exact finite hypothesis core: continuation equivalence and shared-policy search.

No pixel, object, color, direction, or game-specific semantics are assumed.
The candidate models are supplied, NOT discovered by this module. Certificates
are conditional on these finite deterministic models and their observation API.
"""
from __future__ import annotations

from collections import defaultdict, deque
from dataclasses import dataclass, field
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


@dataclass
class _SearchFrame:
    belief: Belief
    remaining: int
    entered: bool = False
    key: tuple[Belief, int] | None = None
    legal: tuple[str, ...] = ()
    action_index: int = 0
    action: str | None = None
    events: tuple[tuple[Event, Belief], ...] = ()
    branch_index: int = 0
    branches: dict[Event, Policy] = field(default_factory=dict)
    child_ready: bool = False
    child_result: Policy | None = None


def solve(space: VersionSpace, budget: int, max_nodes: int = 20000) -> Result:
    """Find one observation-contingent policy winning in every surviving world.

    Searches the given finite deterministic class exactly unless max_nodes is hit.
    Positive action costs make the budget decrease along every branch. An
    explicit stack keeps that search independent of Python's call-stack limit.
    No model can be chosen separately for each branch or each action. The first
    feasible policy is returned; this is not an optimal-cost or probabilistic-risk
    solver.
    """
    if budget < 0 or max_nodes < 1:
        raise ValueError("Invalid planning limits")
    if not space.belief:
        return Result("no-model", 0)
    memo: dict[tuple[Belief, int], Policy | None] = {}
    expanded = 0

    stack = [_SearchFrame(space.belief, budget)]
    root_policy: Policy | None = None

    def complete(policy: Policy | None) -> None:
        """Return one frame's result to its parent without recursive calls."""
        nonlocal root_policy
        stack.pop()
        if stack:
            parent = stack[-1]
            parent.child_result = policy
            parent.child_ready = True
        else:
            root_policy = policy

    try:
        while stack:
            frame = stack[-1]

            if not frame.entered:
                frame.key = (frame.belief, frame.remaining)
                if frame.key in memo:
                    complete(memo[frame.key])
                    continue
                if expanded >= max_nodes:
                    raise _Limit
                expanded += 1
                statuses = {space.models[w.model].nodes[w.state].status
                            for w in frame.belief}
                if statuses == {"win"}:
                    complete(Policy(None, {}))
                    continue
                if "fail" in statuses or frame.remaining <= 0:
                    complete(None)
                    continue
                legal = set.intersection(*(
                    set(space.models[w.model].view(w.state).actions)
                    for w in frame.belief
                ))
                frame.legal = tuple(sorted(legal))
                frame.entered = True
                continue

            if frame.child_ready:
                child_policy = frame.child_result
                frame.child_ready = False
                frame.child_result = None
                if child_policy is None:
                    # Match the recursive DFS: a failed observation branch
                    # rejects this action before trying the next sorted action.
                    frame.action_index += 1
                    frame.action = None
                    frame.events = ()
                    frame.branch_index = 0
                    frame.branches.clear()
                    continue

                event, _ = frame.events[frame.branch_index]
                frame.branches[event] = child_policy
                frame.branch_index += 1
                if frame.branch_index == len(frame.events):
                    assert frame.key is not None and frame.action is not None
                    policy = Policy(frame.action, frame.branches)
                    memo[frame.key] = policy
                    complete(policy)
                continue

            if frame.action is None:
                if frame.action_index >= len(frame.legal):
                    assert frame.key is not None
                    memo[frame.key] = None
                    complete(None)
                    continue
                frame.action = frame.legal[frame.action_index]
                frame.events = tuple(successors(
                    space.models, frame.belief, frame.action
                ).items())
                frame.branch_index = 0
                frame.branches = {}
                if not frame.events:
                    # Preserve the recursive for/else behavior for an action
                    # with no observation branches.
                    assert frame.key is not None
                    policy = Policy(frame.action, {})
                    memo[frame.key] = policy
                    complete(policy)
                    continue

            event, next_belief = frame.events[frame.branch_index]
            if event.cost > frame.remaining:
                frame.action_index += 1
                frame.action = None
                frame.events = ()
                frame.branch_index = 0
                frame.branches.clear()
                continue

            stack.append(_SearchFrame(next_belief, frame.remaining - event.cost))
    except _Limit:
        return Result("search-exhausted", expanded)

    policy = root_policy
    if policy is None:
        return Result("infeasible-in-class", expanded)
    cert = Certificate(space.fingerprint(), budget, policy)
    return Result("solved", expanded, cert)


def verify(space: VersionSpace, certificate: Certificate) -> bool:
    """Independent traversal of the policy on every represented candidate world."""
    if not space.belief or certificate.fingerprint != space.fingerprint():
        return False

    pending = [(space.belief, certificate.budget, certificate.policy)]
    while pending:
        belief, remaining, policy = pending.pop()
        if not belief or remaining < 0:
            return False
        if policy.action is None:
            if (policy.branches or
                    not all(space.models[w.model].nodes[w.state].status == "win"
                            for w in belief)):
                return False
            continue
        if any((w.state, policy.action) not in space.models[w.model].edges for w in belief):
            return False
        branches = successors(space.models, belief, policy.action)
        if branches.keys() != policy.branches.keys():
            return False
        pending.extend((next_belief, remaining-event.cost, policy.branches[event])
                       for event, next_belief in branches.items())

    return True
