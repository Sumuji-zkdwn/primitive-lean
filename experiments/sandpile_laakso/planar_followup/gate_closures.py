"""Exact finite checks of three dyadic sheet-gluing rules. Run with Python 3."""

from collections import deque
from fractions import Fraction
import json


def condition(test, description):
    if not test:
        raise AssertionError(description)


def generators(depth, rule):
    """Leaf permutations: global bit flips or swaps of the two children of each node."""
    count = 1 << depth
    permutations = []
    for level in range(1, depth + 1):
        bit = 1 << (depth - level)
        if rule == "xor":
            permutations.append([s ^ bit for s in range(count)])
        elif rule == "full":
            for prefix in range(1 << (level - 1)):
                permutations.append([
                    s ^ bit if s // (2 * bit) == prefix else s for s in range(count)
                ])
    return permutations


def gate_partition(depth, level, prefix, rule, permutations):
    count = 1 << depth
    bit = 1 << (depth - level)
    start = prefix * (2 * bit)
    pairs = {(s, s + bit) for s in range(start, start + bit)}
    queue = deque(pairs)
    while queue:
        a, b = queue.popleft()
        for perm in permutations:
            x, y = perm[a], perm[b]
            pair = (x, y) if x < y else (y, x)
            if pair not in pairs:
                pairs.add(pair)
                queue.append(pair)

    # Connected components give the equivalence closure of the permuted pairs.
    neighbors = [[] for _ in range(count)]
    for a, b in pairs:
        neighbors[a].append(b)
        neighbors[b].append(a)
    reps = [-1] * count
    for root in range(count):
        if reps[root] != -1:
            continue
        reps[root] = root
        stack = [root]
        while stack:
            for v in neighbors[stack.pop()]:
                if reps[v] == -1:
                    reps[v] = root
                    stack.append(v)

    for s, actual in enumerate(reps):
        gated_prefix = s // (2 * bit)
        if rule == "full":
            expected = gated_prefix * (2 * bit)
        elif rule == "xor" or gated_prefix == prefix:
            expected = s & ~bit
        else:
            expected = s
        condition(actual == expected, (depth, rule, level, prefix, s))
    return reps


def graph(depth, rule):
    """One mesh step has length 1/N, each physical open edge has mass 1/N²."""
    n = 1 << depth
    perms = generators(depth, rule)
    rows = [list(range(n))]
    root_class_size = None
    for j in range(1, n):
        low_bit = j & -j
        level = depth - (low_bit.bit_length() - 1)
        prefix = (j // low_bit - 1) // 2
        reps = gate_partition(depth, level, prefix, rule, perms)
        if j == n // 2:
            root_class_size = reps.count(reps[0])
        rows.append([j * n + s for s in reps])
    rows.append([n * n + s for s in range(n)])

    neighbors = {}
    edges = []
    for left, right in zip(rows, rows[1:]):
        for a, b in zip(left, right):
            neighbors.setdefault(a, []).append(b)
            neighbors.setdefault(b, []).append(a)
            edges.append((a, b))
    return rows, neighbors, edges, root_class_size


def distances(neighbors, source):
    result = {source: 0}
    queue = deque([source])
    while queue:
        a = queue.popleft()
        for b in neighbors[a]:
            if b not in result:
                result[b] = result[a] + 1
                queue.append(b)
    condition(len(result) == len(neighbors), "disconnected quotient")
    return result


def stage(depth):
    n = 1 << depth
    report = {"depth": depth, "sheets": n, "edge_count_each": n * n, "rules": {}}
    for rule in ("prefix", "xor", "full"):
        rows, neighbors, edges, root_size = graph(depth, rule)
        result = {"vertices": len(neighbors), "root_gate_class_size": root_size}
        report["rules"][rule] = result
        if rule == "prefix":
            endpoints = rows[0][n // 2:]
            min_distance = n * n
            for pos, source in enumerate(endpoints[:-1]):
                dist = distances(neighbors, source)
                min_distance = min(min_distance, min(dist[t] for t in endpoints[pos + 1:]))
            condition(min_distance >= n, "prefix packing bound")
            from_base = distances(neighbors, rows[0][0])
            # An entire edge lies in the closed physical radius-one ball if both
            # ends have distance at most N-1, or one is N and the other N-1.
            # Edge-interior maximum in mesh units is (dist[a]+dist[b]+1)/2.
            twice_radius = max(from_base[a] + from_base[b] + 1 for a, b in edges)
            condition(twice_radius <= 2 * n, "prefix base radius")
            result.update(boundary_packing_size=len(endpoints),
                          minimum_boundary_distance=str(Fraction(min_distance, n)),
                          maximum_distance_from_base=str(Fraction(twice_radius, 2 * n)))
        if rule == "full" and depth >= 3:
            # r=2/N, t=1/2+3/N. Radii 2 and 4 in mesh units are integers.
            r = Fraction(2, n)
            center = rows[n // 2 + 3][0]
            dist = distances(neighbors, center)
            # Each open edge is inside the ball up to endpoints if at least
            # one endpoint has distance strictly less than the integer radius.
            small = Fraction(sum(min(dist[a], dist[b]) < 2 for a, b in edges), n * n)
            large = Fraction(sum(min(dist[a], dist[b]) < 4 for a, b in edges), n * n)
            condition(0 < small <= 8 * r * r and large >= r, "full-tree mass bounds")
            result.update(radius=str(r), center_height=str(Fraction(n // 2 + 3, n)),
                          mass_at_radius=str(small), mass_at_double_radius=str(large),
                          doubling_ratio=str(large / small))
    return report


if __name__ == "__main__":
    print(json.dumps({"stages": [stage(d) for d in range(2, 7)]}, indent=2))
