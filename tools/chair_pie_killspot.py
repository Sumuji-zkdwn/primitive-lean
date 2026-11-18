#!/usr/bin/env python3
"""椅子とパイ / kill-spot: minimal external enablers and blockers.

Pure Python, deterministic finite-state reachability. No third-party packages.
The model proves nothing about actual market demand: an external event being
*possible* is not a claim that it will occur or can be commanded by an agent.

Run: python tools/chair_pie_killspot.py
"""
from __future__ import annotations
from collections import deque
from dataclasses import dataclass
from itertools import combinations
from typing import Iterable


@dataclass(frozen=True)
class State:
    capability: int
    unlocked: frozenset[str]
    paid: bool = False


@dataclass(frozen=True)
class Economy:
    label: str
    gates: tuple[str, ...]
    sales_channels: tuple[tuple[str, ...], ...]
    threshold: int = 3
    internal_unlocks: tuple[str, ...] = ()

    def __post_init__(self):
        assert self.threshold >= 0
        assert len(set(self.gates)) == len(self.gates)
        assert set(self.internal_unlocks) <= set(self.gates)
        assert all(set(c) <= set(self.gates) for c in self.sales_channels)


def subsets(elements: Iterable[str]):
    xs = tuple(sorted(elements))
    for k in range(len(xs) + 1):
        for sub in combinations(xs, k):
            yield frozenset(sub)


def successors(economy: Economy, s: State, available_external: frozenset[str]):
    if s.capability < economy.threshold:
        yield 'grow', State(s.capability + 1, s.unlocked, s.paid)
    for gate in sorted(available_external - s.unlocked):
        yield f'external:{gate}', State(s.capability, s.unlocked | {gate}, s.paid)
    if s.capability == economy.threshold:
        for gate in sorted(set(economy.internal_unlocks) - s.unlocked):
            yield f'internal:make-{gate}', State(s.capability, s.unlocked | {gate}, s.paid)
    if not s.paid and s.capability == economy.threshold:
        for idx, required in enumerate(economy.sales_channels, start=1):
            if frozenset(required) <= s.unlocked:
                yield f'sale:channel-{idx}', State(s.capability, s.unlocked, True)


def shortest_revenue_path(economy: Economy, available_external: frozenset[str]):
    initial = State(0, frozenset())
    parent: dict[State, tuple[State, str] | None] = {initial: None}
    queue = deque([initial])
    while queue:
        state = queue.popleft()
        if state.paid:
            path = []
            while parent[state] is not None:
                prior, action = parent[state]
                path.append(action)
                state = prior
            return list(reversed(path)), len(parent)
        for action, new_state in successors(economy, state, available_external):
            if new_state not in parent:
                parent[new_state] = (state, action)
                queue.append(new_state)
    return None, len(parent)


def revenue_possible(economy: Economy, available_external: frozenset[str]):
    return shortest_revenue_path(economy, available_external)[0] is not None


def inclusion_minimal(family: Iterable[frozenset[str]]):
    sets = list(set(family))
    return tuple(sorted(
        (x for x in sets if not any(y < x for y in sets)),
        key=lambda x: (len(x), tuple(sorted(x))),
    ))


def enabling_sets(economy: Economy):
    return inclusion_minimal(
        available for available in subsets(economy.gates)
        if revenue_possible(economy, available)
    )


def blocking_sets(economy: Economy):
    all_gates = frozenset(economy.gates)
    return inclusion_minimal(
        removed for removed in subsets(economy.gates)
        if not revenue_possible(economy, all_gates - removed)
    )


def show_set(f: frozenset[str]):
    return '{' + ', '.join(sorted(f)) + '}'


def verify(economy: Economy):
    all_gates = frozenset(economy.gates)
    possible = {A: revenue_possible(economy, A) for A in subsets(all_gates)}
    # Independent closed-form oracle: enough internal growth is always possible,
    # and payment is enabled exactly when some channel's gates are available.
    for A, got in possible.items():
        oracle = any(frozenset(required) <= A | set(economy.internal_unlocks)
                     for required in economy.sales_channels)
        assert got == oracle, (economy.label, A, got, oracle)
        for B in possible:
            if A <= B and got:
                assert possible[B], (economy.label, 'monotonicity', A, B)
    enabling = enabling_sets(economy)
    blocking = blocking_sets(economy)
    # Hypergraph duality: for every subset K of external gates,
    # blocking all revenue paths is equivalent to hitting every minimal
    # enabling certificate.
    for K in subsets(all_gates):
        blocked = not possible[all_gates - K]
        hits_every_certificate = all(bool(K & M) for M in enabling)
        assert blocked == hits_every_certificate, (economy.label, K)
    # For the fully available external event set, return and replay a
    # shortest witness, checking each transition against the model.
    witness, visited = shortest_revenue_path(economy, all_gates)
    if witness is not None:
        state = State(0, frozenset())
        for act in witness:
            transitions = dict(successors(economy, state, all_gates))
            assert act in transitions
            state = transitions[act]
        assert state.paid
    no_external_path, internal_states = shortest_revenue_path(economy, frozenset())
    assert (no_external_path is not None) == possible[frozenset()]
    if not economy.internal_unlocks and no_external_path is None:
        assert internal_states == economy.threshold + 1
    return enabling, blocking, witness, visited, internal_states


def verify_all_monotone_boolean_functions(n: int = 4):
    """Independent finite check of the hitting-set theorem for *all* monotone
    Boolean functions on n external permissions (n=4 gives 168 cases).
    Uses no Economy or graph/reachability definitions.
    """
    assert n <= 4
    universe = (1 << n) - 1
    candidate_subsets = range(1 << n)
    monotone_count = 0
    for truth_bits in range(1 << (1 << n)):
        def f(A):
            return bool((truth_bits >> A) & 1)
        if any(f(A) and not f(B) for A in candidate_subsets
               for B in candidate_subsets if A & B == A):
            continue
        monotone_count += 1
        minimal_witnesses = [A for A in candidate_subsets if f(A) and not any(
            f(B) for B in candidate_subsets if B != A and B & A == B)]
        for cut in candidate_subsets:
            blocked = not f(universe ^ cut)
            hits_every = all(bool(cut & w) for w in minimal_witnesses)
            assert blocked == hits_every, (n, truth_bits, cut)
    return monotone_count


MODELS = (
    Economy('one channel', ('chair', 'demand'), (('chair', 'demand'),)),
    Economy('independent channels', ('chairA', 'demandA', 'chairB', 'demandB'),
            (('chairA', 'demandA'), ('chairB', 'demandB'))),
    Economy('two chairs / shared buyer', ('chairA', 'chairB', 'buyer'),
            (('chairA', 'buyer'), ('chairB', 'buyer'))),
    Economy('self-made chair', ('chair', 'demand'),
            (('chair', 'demand'),), internal_unlocks=('chair',)),
)


if __name__ == '__main__':
    for econ in MODELS:
        en, blockers, path, visited, internal = verify(econ)
        print(f'[{econ.label}] threshold={econ.threshold}')
        print('  minimal enabling sets:', '; '.join(map(show_set, en)))
        print('  minimal blocking sets:', '; '.join(map(show_set, blockers)))
        witness_for_minimal, _ = shortest_revenue_path(econ, en[0]) if en else (None, 0)
        print('  shortest witness using a minimal enabler:', ' -> '.join(witness_for_minimal) if witness_for_minimal else '(none)')
        print(f'  reachable internal-only states: {internal}; revenue possible internally = {revenue_possible(econ, frozenset())}')
        print(f'  explored states with all external events available: {visited}')
    for n in (0, 1, 3, 8, 30):
        econ = Economy('threshold sweep', ('chair', 'buyer'), (('chair', 'buyer'),), n)
        en, blockers, path, _, _ = verify(econ)
        assert len(path) == n + 3
        print(f'threshold={n}: minimum path length={len(path)}, external prerequisites={len(en[0])}')
    for econ in (Economy('no sales channel', ('chair',), ()),
                 Economy('unconditional channel', ('chair',), ((),))):
        en, blockers, path, visited, internal = verify(econ)
        print(f'[{econ.label}] enablers={list(map(show_set, en))}, blockers={list(map(show_set, blockers))}')
    count = verify_all_monotone_boolean_functions(4)
    assert count == 168
    print(f'all monotone Boolean permission systems on 4 inputs: {count} verified')
    print('PASS: exhaustive subset-oracle, monotonicity, blocker/enabler duality, replay, edge cases, and threshold checks')