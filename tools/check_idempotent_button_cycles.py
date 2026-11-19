"""Enumerate all ordered pairs of deterministic idempotent buttons on 1–6 labels.

Run with Python 3.8 or later. No third-party packages are needed.
"""

from itertools import permutations, product


def idempotents(n):
    """Filter every total self-map, so the search assumes no front/back split."""
    for f in product(range(n), repeat=n):
        if all(f[f[x]] == f[x] for x in range(n)):
            yield f


def has_three_cycle(step):
    for x, y in enumerate(step):
        z = step[y]
        if len({x, y, z}) == 3 and step[z] == x:
            return True
    return False


def labeled_standard_models(k):
    """Relabel the two faces of a k-cycle in every possible way."""
    models = set()
    for labels in permutations(range(2 * k)):
        front, back = labels[:k], labels[k:]
        a = list(range(2 * k))
        b = list(range(2 * k))
        for i in range(k):
            a[front[i]] = back[i]
            b[back[i]] = front[(i + 1) % k]
        models.add((tuple(a), tuple(b)))
    return models


def main():
    print("states  idempotents  ordered_pairs  pairs_with_3_cycle")
    for n in range(1, 7):
        buttons = list(idempotents(n))
        with_cycle = set()
        for a, b in product(buttons, repeat=2):
            step = tuple(b[y] for y in a)
            if has_three_cycle(step):
                with_cycle.add((a, b))
        print(f"{n:6}  {len(buttons):11}  {len(buttons)**2:13}  {len(with_cycle):18}")
        if n < 6:
            assert not with_cycle
        else:
            assert with_cycle == labeled_standard_models(3)
            assert len(with_cycle) == 240
    print("All six-state solutions are relabelings of the displayed model.")


if __name__ == "__main__":
    main()
