"""Bounded finite-state reasoning. Exact enumeration, not a Lean certificate."""
from collections import deque


def validate(actions, observations):
    n = len(observations)
    if not 1 <= n <= 256 or not 1 <= len(actions) <= 64:
        raise ValueError('1..256 states and 1..64 actions required')
    if any(len(t) != n or any(type(x) is not int or not 0 <= x < n for x in t) for t in actions):
        raise ValueError('invalid transition table')
    return n


def classify(keys):
    ids = {}
    return tuple(ids.setdefault(k, len(ids)) for k in keys)


def quotient(actions, observations):
    """Coarsest stable refinement of observation equality for every action."""
    n = validate(actions, observations)
    cls = classify(observations)
    rounds = 0
    while True:
        nxt = classify((cls[x], *(cls[t[x]] for t in actions)) for x in range(n))
        if nxt == cls:
            break
        cls = nxt
        rounds += 1
        assert rounds < n
    groups = tuple(tuple(x for x in range(n) if cls[x] == c) for c in range(max(cls) + 1))
    transitions = tuple(tuple(cls[t[g[0]]] for g in groups) for t in actions)
    # Check quotient homomorphism independently for every state and action.
    assert all(cls[t[x]] == transitions[a][cls[x]] for a, t in enumerate(actions) for x in range(n))
    assert all(observations[x] == observations[g[0]] for g in groups for x in g)
    return {'classes': groups, 'class_of': cls, 'transitions': transitions, 'rounds': rounds}


def distinguish(actions, observations, left, right):
    """Shortest distinguishing operation word, or None for equivalent states."""
    n = validate(actions, observations)
    if not 0 <= left < n or not 0 <= right < n:
        raise ValueError('invalid state')
    start = (left, right)
    todo = deque([start])
    parents = {start: None}
    while todo:
        p = todo.popleft()
        if observations[p[0]] != observations[p[1]]:
            end = p
            word = []
            while parents[p] is not None:
                p, a = parents[p]
                word.append(a)
            word.reverse()
            x, y = start
            for a in word:
                x, y = actions[a][x], actions[a][y]
            assert (x, y) == end and observations[x] != observations[y]
            return {'word': tuple(word), 'end': end, 'observations': (observations[x], observations[y])}
        for a, t in enumerate(actions):
            q = (t[p[0]], t[p[1]])
            if q not in parents:
                parents[q] = (p, a)
                todo.append(q)
    return None


def synthesize(actions, target, max_depth=5, max_nodes=4096):
    """Find a shortest word realizing target, within explicit search limits.

    complete=True on failure means the entire generated monoid was exhausted;
    otherwise failure is inconclusive. Word order is application order.
    """
    n = len(target)
    validate(actions, tuple(range(n)))
    validate([target], tuple(range(n)))
    if not 0 <= max_depth <= 12 or not 1 <= max_nodes <= 4096:
        raise ValueError('invalid search bound')
    ident, target = tuple(range(n)), tuple(target)
    todo = deque([(ident, ())])
    visited = {ident}
    truncated = False
    while todo:
        table, word = todo.popleft()
        if table == target:
            replay = ident
            for a in word:
                replay = tuple(actions[a][x] for x in replay)
            assert replay == target
            return {'word': word, 'complete': True, 'visited': len(visited)}
        for a, t in enumerate(actions):
            nxt = tuple(t[x] for x in table)
            if nxt in visited:
                continue
            if len(word) == max_depth or len(visited) >= max_nodes:
                truncated = True
                continue
            visited.add(nxt)
            todo.append((nxt, word + (a,)))
    return {'word': None, 'complete': not truncated, 'visited': len(visited)}
