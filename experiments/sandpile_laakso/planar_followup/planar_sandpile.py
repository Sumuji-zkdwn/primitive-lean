"""Central-drive Abelian sandpile on the square lattice. Run with Python and NumPy.

The sparse legal-firing queue lives on Z^2. An independent parallel update
uses a finite wired box, reports its flux and checks its empty boundary.
Print deterministic JSON; e.g. python -B planar_sandpile.py > planar_results.json.
"""

from collections import Counter, deque
import json
from math import isqrt

import numpy as np


ORIGIN = (0, 0)
STEPS = ((1, 0), (-1, 0), (0, 1), (0, -1))


def drive(heights, grains, *, lifo, source=ORIGIN):
    """Add at one site, legally stabilize in place, return this avalanche."""
    heights[source] += grains
    pending = deque([source]) if heights[source] >= 4 else deque()
    fired = Counter()
    while pending:
        x, y = point = pending.pop() if lifo else pending.popleft()
        count, heights[point] = divmod(heights[point], 4)
        assert count > 0
        fired[point] += count
        for dx, dy in STEPS:
            neighbor = (x + dx, y + dy)
            old = heights[neighbor]
            heights[neighbor] += count
            if old < 4 <= heights[neighbor]:
                pending.append(neighbor)
    return fired


def parallel(mass):
    return parallel_sources({ORIGIN: mass})


def parallel_sources(deposits):
    mass = sum(deposits.values())
    radius = max(max(abs(x), abs(y)) for x, y in deposits) + isqrt(mass) + 3
    heights = np.zeros((2 * radius + 1,) * 2, dtype=np.int64)
    for (x, y), grains in deposits.items():
        heights[radius + x, radius + y] = grains
    odometer = np.zeros_like(heights)
    flux = 0
    rounds = 0
    while True:
        fires = heights // 4
        if not fires.any():
            break
        rounds += 1
        odometer += fires
        flux += int(fires[0].sum() + fires[-1].sum() + fires[:, 0].sum() + fires[:, -1].sum())
        heights -= 4 * fires
        heights[1:] += fires[:-1]
        heights[:-1] += fires[1:]
        heights[:, 1:] += fires[:, :-1]
        heights[:, :-1] += fires[:, 1:]
    assert flux == 0 and int(heights.sum()) == mass
    assert not any((a[0].any() or a[-1].any() or a[:, 0].any() or a[:, -1].any())
                   for a in (heights, odometer))
    assert heights.min() >= 0 and heights.max() <= 3
    # Check the final-state Laplacian identity independently by padding.
    padded = np.pad(odometer, 1)
    reconstructed = (padded[2:, 1:-1] + padded[:-2, 1:-1] +
                     padded[1:-1, 2:] + padded[1:-1, :-2] - 4 * odometer)
    for (x, y), grains in deposits.items():
        reconstructed[radius + x, radius + y] += grains
    assert np.array_equal(reconstructed, heights)
    return heights, odometer, rounds, flux


def as_counter(array):
    radius = array.shape[0] // 2
    return Counter({(int(i - radius), int(j - radius)): int(array[i, j])
                    for i, j in np.argwhere(array)})


def components(points):
    remaining = set(points)
    sizes = []
    while remaining:
        pending = [remaining.pop()]
        size = 0
        while pending:
            x, y = pending.pop()
            size += 1
            for dx, dy in STEPS:
                neighbor = (x + dx, y + dy)
                if neighbor in remaining:
                    remaining.remove(neighbor)
                    pending.append(neighbor)
        sizes.append(size)
    return sorted(sizes, reverse=True)


def summarize(mass):
    heights, u, rounds, flux = parallel(mass)
    reference = Counter()
    firing = drive(reference, mass, lifo=True)
    assert firing == as_counter(u) and reference == as_counter(heights)
    radius = u.shape[0] // 2
    assert np.array_equal(u, u[::-1]) and np.array_equal(u, u.T)
    assert (np.diff(u[radius:, :], axis=0) <= 0).all()
    # All positive excursion levels at once, by discrete coarea on the empty-padded boundary.
    total_perimeter = int(np.abs(np.diff(u, axis=0)).sum() + np.abs(np.diff(u, axis=1)).sum())
    assert total_perimeter == 4 * int(u.max(axis=1).sum())
    mask = u > 0
    extent = max(max(abs(x), abs(y)) for x, y in firing)
    perimeter = int(np.abs(np.diff(mask.astype(int), axis=0)).sum() +
                    np.abs(np.diff(mask.astype(int), axis=1)).sum())
    assert perimeter == 4 * (2 * extent + 1)
    color_components = components(point for point, value in reference.items() if value == 3)
    return {
        "mass": mass, "wired_box_radius": radius, "boundary_flux": flux,
        "parallel_rounds": rounds, "mass_after": int(heights.sum()),
        "total_topplings": int(u.sum()), "origin_topplings": int(u[radius, radius]),
        "toppled_sites": int(mask.sum()), "toppled_linf_radius": extent,
        "toppled_polyomino_perimeter": perimeter,
        "perimeters_summed_over_all_positive_integer_superlevels": total_perimeter,
        "height_3_sites": sum(color_components), "height_3_components": len(color_components),
        "largest_height_3_component": max(color_components, default=0),
    }


def first_collisions(max_mass=247):
    heights, u = Counter(), Counter()
    answers = {}
    for mass in range(max_mass + 1):
        prior = heights.copy()
        inc = drive(heights, 1, lifo=False)
        if inc:
            seen = {}
            for x, y in sorted(point for point in u if 0 <= point[0] <= point[1]):
                p = (x, y)
                observations = {
                    "odometer": (u[p],),
                    "odometer_height": (u[p], prior[p]),
                    "odometer_height_squared_radius": (u[p], prior[p], x*x + y*y),
                }
                for name, value in observations.items():
                    if name in answers:
                        continue
                    key = name, value
                    if key not in seen:
                        seen[key] = p
                        continue
                    q = seen[key]
                    if inc[p] != inc[q]:
                        answers[name] = {
                            "mass_before": mass, "observation": value,
                            "sites": [q, p], "site_topplings_next_grain": [inc[q], inc[p]],
                        }
        u.update(inc)
    assert len(answers) == 3
    for name, entry in answers.items():
        m = entry["mass_before"]
        h0, u0, _, _ = parallel(m)
        h1, u1, _, _ = parallel(m + 1)
        before, after = as_counter(u0), as_counter(u1)
        stable = as_counter(h0)
        for site, count in zip(entry["sites"], entry["site_topplings_next_grain"]):
            obs = (before[site], stable[site], sum(a*a for a in site))
            assert obs[:len(entry["observation"])] == entry["observation"]
            assert after[site] - before[site] == count
        assert int(h1.sum()) == m + 1
    return answers


def source_partition(odometer, level, sources):
    """Components of an excursion set with their source IDs, by graph traversal."""
    remaining = {p for p, v in odometer.items() if v >= level}
    groups = []
    while remaining:
        stack = [remaining.pop()]
        group = []
        while stack:
            x, y = point = stack.pop()
            if point in sources:
                group.append(sources[point])
            for dx, dy in STEPS:
                neighbor = (x + dx, y + dy)
                if neighbor in remaining:
                    remaining.remove(neighbor)
                    stack.append(neighbor)
        assert group, "excursion component missing every source"
        groups.append("".join(sorted(group)))
    return sorted(groups)


def merge_example(positions):
    deposits = {(x, 0): 256 for x in positions}
    ids = {p: chr(ord("A") + i) for i, p in enumerate(deposits)}
    stable, firing, rounds, flux = parallel_sources(deposits)
    heights, u = Counter(), Counter()
    # Sequential source additions in reverse order give a separate stabilization.
    for site, mass in reversed(list(deposits.items())):
        u.update(drive(heights, mass, lifo=True, source=site))
    assert u == as_counter(firing) and heights == as_counter(stable)
    radius = firing.shape[0] // 2
    assert np.array_equal(firing, firing[:, ::-1])
    assert (np.diff(firing[:, radius:], axis=1) <= 0).all()
    events, previous = [], []
    merge_levels = {}
    for level in range(max(u.values()), 0, -1):
        groups = source_partition(u, level, ids)
        if groups != previous:
            events.append({"level": level, "groups": groups})
            previous = groups
        for group in groups:
            for i, a in enumerate(group):
                for b in group[i+1:]:
                    merge_levels.setdefault(a + b, level)
    barriers = []
    for left, right in zip(positions, positions[1:]):
        columns = range(left, right + 1)
        threshold = min(u[x, 0] for x in columns)
        pair = ids[left, 0] + ids[right, 0]
        assert threshold == merge_levels[pair]
        barriers.append({"pair": pair, "merge_level": threshold,
                         "minimizing_columns": [x for x in columns if u[x, 0] == threshold]})
    return {
        "source_x_at_y_zero": positions, "grains_per_source": 256, "boundary_flux": flux,
        "parallel_rounds": rounds, "highest_positive_level": max(u.values()),
        "source_odometers": [u[x, 0] for x in positions],
        "partition_changes_in_descending_positive_levels": events,
        "pair_merge_levels": merge_levels, "adjacent_pair_barriers": barriers,
    }


def main():
    mass_series = [16, 64, 256, 1024, 4096, 8192]
    print(json.dumps({
        "model": "square lattice, threshold 4, empty substrate, origin source, nearest-neighbor toppling",
        "checks": ["independent parallel wired-box and sparse Z2 LIFO relaxation for each series entry",
                   "zero boundary flux and empty outer ring, mass conservation, Laplacian, stability",
                   "D4 symmetry of odometer, coordinate monotonicity, excursion coarea and perimeter",
                   "sequential single-grain FIFO search over positive odometers, direct parallel replay"],
        "mass_series": [summarize(m) for m in mass_series],
        "collision_search": {"mass_before_inclusive": [0, 247],
                             "sites": "previously toppled; one representative per D4 orbit (0<=x<=y)",
                             "first_collisions": first_collisions()},
        "collinear_multiple_sources": {
            "checks": ["simultaneous parallel vs sequential reversed-source LIFO stabilization",
                       "Laplacian, stability, zero flux and empty box boundary",
                       "all excursion components by graph search at every positive level",
                       "matching adjacent joins with axis minima and cross-column upper bounds"],
            "two_sources": merge_example([-4, 4]),
            "four_sources": merge_example([-7, -4, 3, 7]),
            "eight_sources": merge_example([-17, -15, -9, -7, 7, 9, 15, 17]),
        },
    }, indent=2))


if __name__ == "__main__":
    main()
