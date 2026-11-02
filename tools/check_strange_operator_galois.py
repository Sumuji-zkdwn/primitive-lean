"""Exhaustive three-state check of F0-derived strange-operator polarity.

This is an independent FINITE COMPUTATION, not a substitute for the Lean
proofs in StrangeOperatorGalois.inc. Each map is represented by its three
output values at inputs 0, 1, and 2.
"""
from itertools import product
import json

OPS = tuple(product(range(3), repeat=3))
K = (0, 0, 2)  # LinearInputF0.exampleK
K_PRIME = (0, 2, 2)
BAD_S = (0, 2, 0)  # LinearInputF0.exampleBadS x 0
IDENTITY = (0, 1, 2)


def stops(t, s):
    return any(s[x] != x and s[t[x]] == t[x] for x in range(3))


def breaks_fiber(k, t):
    return any(
        k[x] == k[y] and k[t[x]] != k[t[y]]
        for x in range(3) for y in range(3)
    )


def left_polar(a):
    return frozenset(t for t in OPS if all(stops(t, s) for s in a))


def right_polar(b):
    return frozenset(s for s in OPS if all(stops(t, s) for t in b))


def close(a):
    return right_polar(left_polar(a))


def main():
    assert len(OPS) == 27
    assert K != IDENTITY and stops(K, K)
    assert not stops(IDENTITY, K)
    assert breaks_fiber(K, BAD_S)
    assert not breaks_fiber(K, K)
    seed = frozenset((K,))
    actors = left_polar(seed)
    fixed = close(seed)
    assert len(actors) == 18
    assert fixed == frozenset((K, K_PRIME))
    assert left_polar(fixed) == actors
    assert close(fixed) == fixed
    assert close(frozenset()) == frozenset()
    assert close(frozenset((IDENTITY,))) == frozenset(OPS)
    # Check all 1- and 2-generated closed families.
    for a in [frozenset(), *(frozenset((x,)) for x in OPS),
              *(frozenset((x, y)) for x in OPS for y in OPS)]:
        assert a.issubset(close(a))
        assert close(close(a)) == close(a)
    print(json.dumps({
        "checked": True,
        "all_endomaps": len(OPS),
        "seed": K,
        "left_polar_seed_size": len(actors),
        "closed_family": sorted(fixed),
        "self_stops": stops(K, K),
        "bad_update_breaks_fiber": breaks_fiber(K, BAD_S),
        "self_does_not_break_fiber": not breaks_fiber(K, K),
        "checked_singletons_and_pairs": True,
        "scope": "three-state exhaustive enumeration, not Lean proof"
    }, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
