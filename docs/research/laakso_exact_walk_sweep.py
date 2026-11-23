"""Independent exact-rational audit of finite Laakso gate-walk distance.

For depths m=1,2,3 and each of three strictly increasing rational height
coordinates, compare Dijkstra shortest path length against the minimum over
all admissible sweeping intervals, for every pair of heights and bit XORs.

A simultaneous XOR of all bits is an exact graph automorphism, so checking
start sheet zero covers every ordered vertex pair. This is a FINITE check;
it does not certify the compact infinite inverse limit.
"""
from fractions import Fraction as Q
from heapq import heappush, heappop


def standard(x):
    return x


def calibrated_good(x):
    return x / 2 if x <= Q(1, 3) else Q(1, 6) + Q(5, 4) * (x - Q(1, 3))


def power2(x):
    return x * x


def finite_graph(depth, coordinate):
    cells = 3 ** depth
    sheets = 2 ** depth
    heights = [coordinate(Q(j, cells)) for j in range(cells + 1)]
    adj = [[] for _ in range((cells + 1) * sheets)]
    gate_bits = [0 for _ in range(cells + 1)]

    def edge(a, b, cost):
        adj[a].append((b, cost))
        adj[b].append((a, cost))

    for j in range(cells):
        length = heights[j + 1] - heights[j]
        assert length > 0
        for sheet in range(sheets):
            edge(j * sheets + sheet, (j + 1) * sheets + sheet, length)

    for j in range(1, cells):
        k, p = j, 0
        while k % 3 == 0:
            k //= 3
            p += 1
        flip_mask = 1 << p
        gate_bits[j] = flip_mask
        for sheet in range(sheets):
            if sheet & flip_mask == 0:
                edge(j * sheets + sheet, j * sheets + (sheet ^ flip_mask), Q(0))

    return adj, heights, gate_bits


def shortest_paths(adj, source):
    distances = [None] * len(adj)
    distances[source] = Q(0)
    heap = [(Q(0), source)]
    while heap:
        dist, v = heappop(heap)
        if dist != distances[v]:
            continue
        for w, length in adj[v]:
            candidate = dist + length
            if distances[w] is None or candidate < distances[w]:
                distances[w] = candidate
                heappush(heap, (candidate, w))
    return distances


def audit_one(depth, coordinate):
    adj, z, gate_bits = finite_graph(depth, coordinate)
    cells, sheets = 3 ** depth, 2 ** depth
    available = {}
    for low in range(cells + 1):
        flags = 0
        for high in range(low, cells + 1):
            flags |= gate_bits[high]
            available[low, high] = flags

    # By XOR symmetry, only sheet 0 as the source is needed.
    representative_pairs = 0
    for i in range(cells + 1):
        shortest = shortest_paths(adj, i * sheets)
        for j in range(cells + 1):
            low, high = min(i, j), max(i, j)
            base = abs(z[i] - z[j])
            for difference_mask in range(sheets):
                candidates = (
                    2 * (z[b] - z[a]) - base
                    for a in range(low + 1)
                    for b in range(high, cells + 1)
                    if available[a, b] & difference_mask == difference_mask
                )
                sweep_distance = min(candidates)
                actual = shortest[j * sheets + difference_mask]
                assert actual == sweep_distance, (
                    depth, i, j, difference_mask, actual, sweep_distance
                )
                representative_pairs += 1

    assert representative_pairs == (cells + 1) ** 2 * sheets
    return representative_pairs, representative_pairs * sheets


def main():
    representative_total = 0
    actual_pair_total = 0
    for label, coordinate in (
        ("standard", standard),
        ("piecewise_good", calibrated_good),
        ("power2", power2),
    ):
        for depth in (1, 2, 3):
            count, total = audit_one(depth, coordinate)
            representative_total += count
            actual_pair_total += total
            print(f"{label} depth={depth}: {count} XOR classes, "
                  f"{total} ordered vertex pairs")
    assert representative_total == 20_112
    assert actual_pair_total == 155_520
    print("PASS: exact finite shortest-path/sweep identity; "
          "infinite-distance identification remains unproved.")


if __name__ == "__main__":
    main()
