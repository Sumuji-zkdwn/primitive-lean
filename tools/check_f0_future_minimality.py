"""Independent finite check of the F0 descent / predictive-kernel bridge.

All idempotent K and deterministic U on one through four states are checked.
This finite calculation supplements, and does not replace, the general Lean proof.
"""
from itertools import product


def future_equal(k, u, x, y):
    seen = set()
    while (x, y) not in seen:
        if k[x] != k[y]:
            return False
        seen.add((x, y))
        x, y = u[x], u[y]
    return True


def check():
    counts = {}
    descending = {}
    for n in range(1, 5):
        maps = list(product(range(n), repeat=n))
        idempotents = [k for k in maps if all(k[k[x]] == k[x] for x in range(n))]
        count = stable = 0
        for k in idempotents:
            for u in maps:
                descends = all(k[u[k[x]]] == k[u[x]] for x in range(n))
                respects = all(k[x] != k[y] or k[u[x]] == k[u[y]]
                               for x in range(n) for y in range(n))
                complete = all(future_equal(k, u, x, y) == (k[x] == k[y])
                               for x in range(n) for y in range(n))
                assert descends == respects == complete, (n, k, u)
                if descends:
                    assert all(future_equal(k, u, k[x], x) for x in range(n))
                    stable += 1
                count += 1
        counts[n], descending[n] = count, stable
    k, u = (0, 0, 2), (0, 2, 2)
    assert k[0] == k[1] and not future_equal(k, u, 0, 1)
    return counts, descending


if __name__ == '__main__':
    counts, descending = check()
    print('F0 descent iff future-kernel equality: PASS')
    print('All idempotent/update pairs:', counts)
    print('Descending pairs:', descending)
    print('General arbitrary-type Lean statement is verified separately.')
