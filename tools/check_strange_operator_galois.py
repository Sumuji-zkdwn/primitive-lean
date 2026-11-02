"""Independent finite tests for the F0-derived operator polarity and conjugacy.

Runs over all endomaps on 2, 3 and 4 states. The actual arbitrary-type
closure theorem is proved separately in StrangeOperatorConjugacy.inc.
"""
from itertools import product, permutations
import json


def spike(n, c, a):
    return tuple(a if x == c else x for x in range(n))


def stops(t, s):
    n = len(t)
    return any(s[x] != x and s[t[x]] == t[x] for x in range(n))


def breaks_fiber(k, t):
    return any(k[x] == k[y] and k[t[x]] != k[t[y]]
               for x in range(len(k)) for y in range(len(k)))


def conjugate(p, s):
    inverse = tuple(p.index(x) for x in range(len(p)))
    return tuple(p[s[inverse[x]]] for x in range(len(p)))


def polar_pair(n, seed):
    ops = tuple(product(range(n), repeat=n))
    actors = frozenset(t for t in ops if all(stops(t, s) for s in seed))
    closed = frozenset(s for s in ops if all(stops(t, s) for t in actors))
    return ops, actors, closed


def main():
    record = {}
    for n in (2, 3, 4):
        c, a = 1, 0
        k = spike(n, c, a)
        ops, actors, closed = polar_pair(n, (k,))
        expected_actors = frozenset(t for t in ops if t[c] != c)
        expected_closure = frozenset(spike(n, c, b) for b in range(n) if b != c)
        stabilizer = [p for p in permutations(range(n)) if p[c] == c]
        conjugacy_orbit = frozenset(conjugate(p, k) for p in stabilizer)
        assert actors == expected_actors
        assert closed == expected_closure
        assert closed == conjugacy_orbit
        assert stops(k, k)

        record[n] = {
            "endomaps": len(ops),
            "polar": len(actors),
            "closure": sorted(closed),
            "stabilizer_orbit": len(conjugacy_orbit),
        }

    n = 3
    ops, actors, closed = polar_pair(n, (spike(n, 1, 0),))
    k = spike(n, 1, 0)
    kp = spike(n, 1, 2)
    bad = (0, 2, 0)
    assert k == (0, 0, 2)
    assert kp == (0, 2, 2)
    assert breaks_fiber(k, bad)
    assert not breaks_fiber(k, k)
    assert closed == frozenset((k, kp))
    assert conjugate((2, 1, 0), k) == kp
    assert all(
        stops(t, s) == stops(conjugate(p, t), conjugate(p, s))
        for p in permutations(range(3))
        for t in ops for s in ops
    )
    assert frozenset(s for s in ops if all(stops(t, s) for t in actors)) == closed
    empty_closure = polar_pair(3, tuple())[2]
    assert not empty_closure
    assert not {t for t in ops if all(stops(t, s) for s in actors)}
    assert all(
        a_set <= polar_pair(3, a_set)[2]
        for a_set in (frozenset(), *(frozenset((x,)) for x in ops))
    )
    print(json.dumps({
        "passed": True,
        "checked_n": [2, 3, 4],
        "results": record,
        "three_state_conjugacy_invariance": True,
        "scope": "exact exhaustive Python enumeration, with separate general Lean proofs",
    }, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
