"""Finite crosschecks for operator-context, policy, product, and reachability results.

The tests compare exhaustive finite semantics, not the Lean proof validity.
"""
from collections import deque
from itertools import product
import random


def labels(values):
    mapping = {}
    result = []
    for v in values:
        if v not in mapping:
            mapping[v] = len(mapping)
        result.append(mapping[v])
    return tuple(result)


def quotient(out, steps):
    prev = labels(out)
    while True:
        nxt = labels(tuple((prev[x], tuple(prev[s[x]] for s in steps))
                           for x in range(len(out))))
        if nxt == prev:
            return prev
        prev = nxt


def apply_word(steps, word, x):
    for i in word:
        x = steps[i][x]
    return x


def words(length, alphabet):
    for n in range(length + 1):
        yield from product(range(alphabet), repeat=n)


def reachable(steps, x):
    seen = {x}
    queue = deque([x])
    while queue:
        a = queue.popleft()
        for op in steps:
            b = op[a]
            if b not in seen:
                seen.add(b)
                queue.append(b)
    return seen


def compatible(q, T):
    return all(q[x] != q[y] or q[T[x]] == q[T[y]]
               for x in range(len(q)) for y in range(len(q)))


def compose(a, b):
    return tuple(b[a[x]] for x in range(len(a)))


def test_contextual_word_equivalence_is_two_sided_congruence():
    rng = random.Random(114204)
    for n in (3, 4):
        for _ in range(150):
            obs = tuple(rng.randrange(3) for _ in range(n))
            steps = tuple(tuple(rng.randrange(n) for _ in range(n)) for _ in range(2))
            q = quotient(obs, steps)
            ws = tuple(words(3, len(steps)))
            def ctx(w, v):
                return all(q[apply_word(steps,w,x)] == q[apply_word(steps,v,x)]
                           for x in range(n))
            for w in ws[:6]:
                for v in ws[:6]:
                    if not ctx(w,v):
                        continue
                    for prefix in ws[:5]:
                        for suffix in ws[:5]:
                            assert ctx(prefix+w+suffix,prefix+v+suffix)


def test_adaptive_feedback_can_split_fixed_word_kernel():
    obs=(0,0,1)
    identity=(0,1,2)
    constant=(2,2,2)
    old=(identity,constant)
    q=quotient(obs,old)
    policy=(0,1,0)
    feedback=tuple(old[policy[x]][x] for x in range(3))
    assert q[0] == q[1]
    assert not compatible(q,feedback)
    assert obs[feedback[0]] != obs[feedback[1]]
    assert len(set(quotient(obs,old+(feedback,))))==3


def test_quotient_stable_policies_cannot_refine_prediction():
    rng=random.Random(4125)
    for n in (3,4,5):
        for _ in range(200):
            obs=tuple(rng.randrange(3) for _ in range(n))
            steps=tuple(tuple(rng.randrange(n) for _ in range(n))
                        for _ in range(3))
            q=quotient(obs,steps)
            decisions={c:rng.randrange(len(steps)) for c in set(q)}
            policy=tuple(decisions[q[x]] for x in range(n))
            adaptive=tuple(steps[policy[x]][x] for x in range(n))
            assert compatible(q,adaptive)
            assert quotient(obs,steps+(adaptive,))==q
            x,y=rng.randrange(n),rng.randrange(n)
            if q[x] == q[y]:
                xx,yy=x,y
                for _ in range(10):
                    xx,yy=adaptive[xx],adaptive[yy]
                    assert q[xx]==q[yy]


def test_product_interleavings_have_product_prediction_kernel():
    left_out=(0,0,1)
    right_out=(0,1)
    left_steps=((1,2,2),(0,0,2))
    right_steps=((1,1),)
    qL=quotient(left_out,left_steps)
    qR=quotient(right_out,right_steps)
    states=tuple(product(range(3),range(2)))
    to_id={p:i for i,p in enumerate(states)}
    prod_out=tuple((left_out[x],right_out[y]) for x,y in states)
    prod_steps=[]
    for step in left_steps:
        prod_steps.append(tuple(to_id[(step[x],y)] for x,y in states))
    for step in right_steps:
        prod_steps.append(tuple(to_id[(x,step[y])] for x,y in states))
    qProd=quotient(prod_out,prod_steps)
    for i,(x,y) in enumerate(states):
        for j,(x2,y2) in enumerate(states):
            assert (qProd[i]==qProd[j])==(
                qL[x]==qL[x2] and qR[y]==qR[y2])


def test_generated_words_preserve_reachability():
    rng=random.Random(7114)
    for n in (3,4,5):
        for _ in range(100):
            old=tuple(tuple(rng.randrange(n) for _ in range(n)) for _ in range(2))
            code=((0,1,1),(0,),(),(1,0,1,0))
            generated=tuple(tuple(apply_word(old,w,x) for x in range(n))
                            for w in code)
            for x in range(n):
                assert reachable(generated,x)<=reachable(old,x)
                assert reachable(old+generated,x)==reachable(old,x)


def test_primitive_invariants_equal_reachability_closed_sets():
    rng=random.Random(883)
    for n in (3,4):
        for _ in range(50):
            steps=tuple(tuple(rng.randrange(n) for _ in range(n)) for _ in range(2))
            for P in product((False,True),repeat=n):
                primitive=all(not P[x] or P[s[x]] for s in steps for x in range(n))
                all_reachable=all(not P[x] or all(P[y] for y in reachable(steps,x))
                                  for x in range(n))
                assert primitive==all_reachable


def test_joint_sensors_intersection_of_kernels():
    rng=random.Random(9009)
    for n in (3,4,5):
        for _ in range(100):
            K=tuple(rng.randrange(3) for _ in range(n))
            L=tuple(rng.randrange(3) for _ in range(n))
            steps=tuple(tuple(rng.randrange(n) for _ in range(n)) for _ in range(2))
            left=quotient(K,steps)
            right=quotient(L,steps)
            bundle=quotient(tuple(zip(K,L)),steps)
            assert all((bundle[x]==bundle[y])==
                       ((left[x]==left[y]) and (right[x]==right[y]))
                       for x in range(n) for y in range(n))
