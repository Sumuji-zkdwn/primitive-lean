"""Independent finite oracle for deterministic future-observation minimal states.

This checks a finite selection of examples and is NOT a Lean proof.
Exhaustive at N<=4 (including every update and every observation map).
"""
from itertools import product


def signature(update, output, x, depth):
    result = []
    for _ in range(depth + 1):
        result.append(output[x])
        x = update[x]
    return tuple(result)


def partitions(update, output, depth):
    return tuple(signature(update, output, x, depth) for x in range(len(update)))


def kernel(sig):
    return {(i, j) for i in range(len(sig))
            for j in range(len(sig)) if sig[i] == sig[j]}


def verify():
    counts = {}
    for n in range(1, 5):
        cases = 0
        for update in product(range(n), repeat=n):
            for output in product(range(n), repeat=n):
                r = len(set(output))
                assert r > 0
                cutoff = n - r
                fast = kernel(partitions(update, output, cutoff))
                # The state pair evolution can visit at most N**2 pairs.
                long = kernel(partitions(update, output, n * n + 1))
                assert fast == long, (n, update, output, cutoff, fast, long)
                # The kernel is forward-stable, so the quotient transition
                # and output are both unambiguous.
                for x, y in fast:
                    assert output[x] == output[y]
                    assert (update[x], update[y]) in fast
                # Distinct equivalence classes yield distinct quotient states.
                classes = set(fast)
                assert len(classes) >= n
                cases += 1
        counts[n] = cases
    assert counts == {1: 1, 2: 16, 3: 729, 4: 65536}
    print("Finite future-observation rank bound: PASS")
    print("Exhaustive deterministic models checked:", counts)


if __name__ == "__main__":
    verify()
