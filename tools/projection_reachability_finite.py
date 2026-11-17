#!/usr/bin/env python3
"""Independent exhaustive finite checks. Standard library only.

Lean proofs are universal; these finite checks are not their substitute.
The existing Economy source is read from tools/; source hashes are recorded by the Lean verifier.
"""
from __future__ import annotations
from collections import deque
from itertools import product
from pathlib import Path
import importlib.util
import json
import sys

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'verification/projection-reachability'


def closure(n, functions, start):
    seen = {start}
    queue = deque([start])
    while queue:
        x = queue.popleft()
        for f in functions:
            y = f[x]
            if y not in seen:
                seen.add(y)
                queue.append(y)
    return seen


def exhaustive_projection(nx, ny):
    systems = starts = simulations = gains = nonsimulation_without_gain = 0
    for old in product(range(nx), repeat=nx):
        ro = [closure(nx, (old,), x) for x in range(nx)]
        for new in product(range(ny), repeat=ny):
            rn = [closure(ny, (new,), y) for y in range(ny)]
            for pi in product(range(nx), repeat=ny):
                systems += 1
                sim = all(pi[new[y]] in ro[pi[y]] for y in range(ny))
                all_pairs = all(pi[z] in ro[pi[y]]
                                for y in range(ny) for z in rn[y])
                assert sim == all_pairs
                simulations += sim
                for s in range(ny):
                    starts += 1
                    gain = any(pi[z] not in ro[pi[s]] for z in rn[s])
                    escape = any(pi[y] in ro[pi[s]] and
                                 pi[new[y]] not in ro[pi[s]] for y in rn[s])
                    assert gain == escape
                    assert not (sim and gain)
                    gains += gain
                    nonsimulation_without_gain += not sim and not gain
    return dict(old_states=nx, new_states=ny, systems=systems, starts=starts,
                simulations=simulations, gain_starts=gains,
                nonsimulation_without_gain=nonsimulation_without_gain)


def small_witnesses():
    old = ((0, 1),)
    new2 = ((0, 1), (1, 1))
    new3 = ((0, 1, 2), (1, 2, 2))
    pi3 = (0, 0, 1)
    r0 = closure(2, old, 0)
    r2 = closure(2, new2, 0)
    r3 = closure(3, new3, 0)
    assert r0 == {0} and r2 == {0, 1} and r3 == {0, 1, 2}
    assert {pi3[y] for y in r3} == {0, 1}
    assert new3[1][new3[1][0]] == 2
    # The old action sets false -> true; a new reset breaks local simulation
    # at reachable true, but the old start already reaches both states.
    forward, reset = (1, 1), (0, 0)
    assert 0 not in closure(2, (forward,), 1)
    assert closure(2, (forward,), 0) == closure(2, (forward, reset), 0)
    # Pointwise simulation need not give a fixed word per operation.
    # Powers of Boolean flip are only id and flip, never constant true.
    flip, const_true = (1, 0), (1, 1)
    assert all(const_true[x] in closure(2, (flip,), x) for x in range(2))
    assert const_true not in {(0, 1), flip}
    return dict(old_reachable=sorted(r0), same_carrier_new=sorted(r2),
                proper_extension_new=sorted(r3), proper_projection=[0, 0, 1],
                proper_projection_reachable=[0, 1],
                reset_failure_without_gain=True,
                state_dependent_simulation_without_uniform_compiler=True)


def import_upstream():
    p = ROOT / 'tools/chair_pie_killspot.py'
    spec = importlib.util.spec_from_file_location('pinned_chair_pie', p)
    m = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = m
    spec.loader.exec_module(m)
    return m


# This independent total transition table follows ChairInternalGeneration.inc.
def total_step(s, action):
    cap, chair, demand, paid = s
    if action == 'grow':
        return (min(3, cap + 1), chair, demand, paid)
    if action == 'external:chair':
        return (cap, True, demand, paid)
    if action == 'external:demand':
        return (cap, chair, True, paid)
    if action == 'internal:make-chair':
        return (cap, chair or cap == 3, demand, paid)
    if action == 'sale:channel-1':
        return (cap, chair, demand, paid or (cap == 3 and chair and demand))
    raise ValueError(action)


def chair_checks():
    m = import_upstream()
    states = list(product(range(4), (False, True), (False, True), (False, True)))
    assert len(states) == 32
    checked_rows = 0
    table = []
    for internal in (False, True):
        econ = m.Economy('one channel', ('chair', 'demand'), (('chair', 'demand'),),
                         internal_unlocks=('chair',) if internal else ())
        for A in m.subsets(econ.gates):
            labels = ['grow', 'sale:channel-1']
            labels += ['external:' + g for g in sorted(A)]
            if internal:
                labels += ['internal:make-chair']
            for s in states:
                cap, chair, demand, paid = s
                unlocked = frozenset(g for g, bit in [('chair', chair), ('demand', demand)] if bit)
                upstream = m.State(cap, unlocked, paid)
                expected = {(a, (t.capability, 'chair' in t.unlocked,
                                 'demand' in t.unlocked, t.paid))
                            for a, t in m.successors(econ, upstream, A)}
                actual = {(a, total_step(s, a)) for a in labels if total_step(s, a) != s}
                assert actual == expected, (internal, A, s, actual, expected)
                checked_rows += 1
            indexes = {s: i for i, s in enumerate(states)}
            functions = tuple(tuple(indexes[total_step(s, a)] for s in states) for a in labels)
            reach = closure(32, functions, indexes[(0, False, False, False)])
            paid = any(states[i][3] for i in reach)
            upstream_paid = m.revenue_possible(econ, A)
            oracle = 'demand' in A and (internal or 'chair' in A)
            assert paid == upstream_paid == oracle
            witness, _ = m.shortest_revenue_path(econ, A)
            table.append(dict(internal_chair=internal, permissions=sorted(A),
                              reachable_states=len(reach), goal_reachable=paid,
                              shortest_word=witness))
    # Use the exact original tests/oracles for all four source models too.
    models = []
    for e in m.MODELS:
        enablers, blockers, _, _, _ = m.verify(e)
        models.append(dict(model=e.label,
                           minimal_enablers=[sorted(a) for a in enablers],
                           minimal_blockers=[sorted(a) for a in blockers]))
    n = m.verify_all_monotone_boolean_functions(4)
    assert n == 168
    return dict(state_count=32, transition_contexts=checked_rows,
                permission_cases=table, original_models=models,
                original_monotone_functions=n)


def check_lean_export():
    log = OUT / 'lean430.log'
    if not log.exists():
        return dict(status='NOT_RUN', reason='Run Lean and save verification/lean430.log first')
    labels = ['grow', 'sale:channel-1', 'external:chair', 'external:demand',
              'internal:make-chair']
    states = list(product(range(4), (False, True), (False, True), (False, True)))
    indexes = {s: i for i, s in enumerate(states)}
    rows = {}
    for line in log.read_text().splitlines():
        if not line.startswith('TRANS '):
            continue
        _, system, s, action, target = line.split()
        key = (system, int(s), int(action))
        assert key not in rows, ('duplicate Lean transition', key)
        rows[key] = int(target)
    expected = {(system, i, a): indexes[total_step(s, labels[a])]
                for system, n in [('old', 4), ('new', 5)]
                for i, s in enumerate(states) for a in range(n)}
    assert rows == expected, ('Lean/Python transition mismatch', len(rows), len(expected))
    assert len(rows) == 288
    return dict(status='PASS', total_transitions=len(rows),
                method='Lean #eval output compared with independent Python total table; its non-self edges match pinned Economy in all 256 state/permission contexts')


def main():
    results = dict(
        exhaustive=[exhaustive_projection(2, 2), exhaustive_projection(2, 3)],
        witnesses=small_witnesses(), chair=chair_checks(), lean_export=check_lean_export(),
        status='PASS',
        boundary='Finite checks and model reachability only; no real demand or payment claim.')
    out = OUT / 'python_results.json'
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(results, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps(results, ensure_ascii=False, indent=2))


if __name__ == '__main__':
    main()
