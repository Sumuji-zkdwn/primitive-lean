"""Independent exhaustive oracle tests for the reusable finite kernel."""
from itertools import product
from random import Random
from forge_finite import quotient, distinguish, synthesize


def test():
    rng = Random(805)
    machines = pairs = 0
    for n in range(1, 8):
        for _ in range(36):
            actions = [tuple(rng.randrange(n) for _ in range(n)) for _ in range(1 + rng.randrange(3))]
            obs = [rng.randrange(2) for _ in range(n)]
            r = quotient(actions, obs)
            machines += 1
            for x in range(n):
                for y in range(n):
                    # Independent fixed-point of reachable paired states.
                    reach = {(x,y)}
                    while True:
                        more = reach | {(t[a],t[b]) for a,b in reach for t in actions}
                        if more == reach: break
                        reach = more
                    same = all(obs[a] == obs[b] for a,b in reach)
                    assert same == (r['class_of'][x] == r['class_of'][y])
                    w = distinguish(actions, obs, x, y)
                    assert same == (w is None)
                    if w is not None:
                        # Independent layer-by-layer frontier, excluding longer words.
                        layer = {(x,y)}
                        for _ in w['word']:
                            assert all(obs[a] == obs[b] for a,b in layer)
                            layer = {(t[a],t[b]) for a,b in layer for t in actions}
                        assert any(obs[a] != obs[b] for a,b in layer)
                    pairs += 1
    a = [(1,0,2),(0,2,1)]
    for depth in range(4):
        for word in product(range(len(a)), repeat=depth):
            target = tuple(range(3))
            for k in word: target = tuple(a[k][x] for x in target)
            r = synthesize(a, target, max_depth=depth)
            assert r['word'] is not None and len(r['word']) <= depth
    assert synthesize(a,(0,0,0))['complete']
    assert not synthesize(a,(2,0,1),max_depth=0)['complete']
    print(f'PASS: {machines} finite machines, {pairs} state pairs, shortest distinguishing words and bounded synthesis')
    return machines, pairs

if __name__ == '__main__':
    test()
