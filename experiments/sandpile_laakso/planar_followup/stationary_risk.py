"""Estimate the conditional variance of total sandpile firings under uniform recurrent starts.

Run python -B stationary_risk.py --m 2 --pairs 4096 --seed 20261121.
The observation consists of the initial mass, the square clock and its binary
switches, and all M² fair corner choices. Each choice adds two grains.
"""

import argparse
from collections import defaultdict, deque
from fractions import Fraction
from itertools import product
import json
from math import comb, sqrt
from random import Random
from statistics import mean, stdev

from square_clock import burns, instruments, observe


class Square:
    def __init__(self, m):
        self.modulus, self.inside, self.clock, self.masks = instruments(m)
        n = self.modulus - 1
        self.side = n
        self.sink = s = n * n
        # Wilson and the burning bijection both distinguish parallel sink edges.
        # Give the four outgoing edges the fixed order up, right, down, left.
        self.edges = [
            (v - n if v >= n else s, v + 1 if v % n < n - 1 else s,
             v + n if v < s - n else s, v - 1 if v % n else s)
            for v in range(s)
        ]

    def class_key(self, state):
        return (sum(state), *observe(state, self.modulus, self.clock, self.masks))

    def heights(self, distance, parent_edge):
        """Invert the burning bijection given tree distances to the sink and parent edges."""
        heights = []
        for v, neighbours in enumerate(self.edges):
            depth = distance[v]
            earlier = rank = 0
            for edge, u in enumerate(neighbours):
                earlier += distance[u] < depth
                rank += edge < parent_edge[v] and distance[u] == depth - 1
            heights.append(4 - earlier + rank)
        return tuple(heights)

    def sample(self, rng):
        """Wilson's loop-erased walks give one uniform rooted spanning tree."""
        parent = [-1] * self.sink
        distance = [-1] * self.sink + [0]
        for start in range(self.sink):
            v = start
            while distance[v] < 0:
                edge = rng.getrandbits(2)
                parent[v] = edge
                v = self.edges[v][edge]
            # The last edge chosen at each visited site erases every loop.
            v = start
            path = []
            while distance[v] < 0:
                path.append(v)
                v = self.edges[v][parent[v]]
            depth = distance[v]
            for v in reversed(path):
                depth += 1
                distance[v] = depth
        return self.heights(distance, parent)

    def firings(self, state, left, right):
        """Stabilize a complete input in bulk. Abelianity preserves all firing counts."""
        heights = list(state)
        heights[0] += 2 * left
        heights[self.side - 1] += 2 * right
        queue = deque([0, self.side - 1])
        total = 0
        while queue:
            v = queue.popleft()
            fires, heights[v] = divmod(heights[v], 4)
            total += fires
            for u in self.inside[v]:
                old = heights[u]
                heights[u] += fires
                if old < 4 <= heights[u]:
                    queue.append(u)
        return total


def exact_small():
    """Enumerate every tree, recurrent state, and input multiplicity on the 2x2."""
    graph = Square(1)
    sink = graph.sink
    tree_images = []
    for parent in product(range(4), repeat=sink):
        distance = [0] * (sink + 1)
        for start in range(sink):
            path = set()
            v = start
            while v != sink and v not in path:
                path.add(v)
                v = graph.edges[v][parent[v]]
            if v != sink:
                break
            distance[start] = len(path)
        else:
            tree_images.append(graph.heights(distance, parent))
    recurrent = {h for h in product(range(4), repeat=sink) if burns(h, graph.inside)}
    assert len(tree_images) == len(recurrent) == 192 and set(tree_images) == recurrent

    fibres = defaultdict(list)
    for state in recurrent:
        fibres[graph.class_key(state)].append(state)
    risk = Fraction(0)
    for left in range(10):
        weight = Fraction(comb(9, left), len(recurrent) * 2**9)
        for fibre in fibres.values():
            counts = [graph.firings(h, left, 9 - left) for h in fibre]
            # Size of this class times its population variance.
            risk += weight * (sum(x*x for x in counts) - Fraction(sum(counts)**2, len(fibre)))
    return dict(population=len(recurrent), fibres=len(fibres), exact=str(risk), decimal=float(risk))


def experiment(m, count, seed):
    if m < 1 or count < 2:
        raise ValueError("m must be at least 1 and pairs must be at least 2")
    graph = Square(m)
    # Domain-separated, reproducible random streams for each part of the experiment.
    ref_rng, mate_rng, drive_rng = (
        Random(f"laakso-burn-v1/{seed}/{m}/{name}")
        for name in ("reference", "independent-rejection", "fair-drive")
    )
    references = [graph.sample(ref_rng) for _ in range(count)]
    pending = defaultdict(deque)
    for i, state in enumerate(references):
        pending[graph.class_key(state)].append(i)
    classes = len(pending)
    mates = [None] * count
    offers = 0
    while pending:
        state = graph.sample(mate_rng)
        offers += 1
        key = graph.class_key(state)
        if key in pending:
            mates[pending[key].popleft()] = state
            if not pending[key]:
                del pending[key]

    steps = graph.modulus**2
    scores = []
    max_gap = 0
    for a, b in zip(references, mates):
        assert b is not None and graph.class_key(a) == graph.class_key(b)
        left = drive_rng.getrandbits(steps).bit_count()
        gap = graph.firings(a, left, steps - left) - graph.firings(b, left, steps - left)
        scores.append(gap**2 / 2)
        max_gap = max(max_gap, abs(gap))

    ordered = sorted(scores, reverse=True)
    total = sum(scores)
    average = mean(scores)
    tail_size = (count + 99) // 100
    tail_sum = sum(ordered[:tail_size])
    blocks = min(4, count)
    return dict(
        side=graph.side, N=steps, seed=seed, pairs=count, matched_pairs=len(scores),
        distinct_reference_classes=classes, candidate_offers=offers,
        mean_square_error=average, mc_standard_error=stdev(scores) / sqrt(count),
        normalized_rms=sqrt(average) / graph.modulus,
        max_abs_gap=max_gap, max_score=ordered[0], top_one_percent_number=tail_size,
        top_one_percent_share=tail_sum / total if total else None,
        mean_omit_one_largest=(total - ordered[0]) / (count - 1),
        mean_omit_top_one_percent=(total - tail_sum) / (count - tail_size),
        quartile_batch_means=[
            mean(scores[j*count//blocks:(j+1)*count//blocks]) for j in range(blocks)
        ],
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--m", type=int, default=2)
    parser.add_argument("--pairs", type=int, default=4096)
    parser.add_argument("--seed", type=int, default=20261121)
    args = parser.parse_args()
    if args.m < 1 or args.pairs < 2:
        parser.error("m must be at least 1 and pairs must be at least 2")
    print(json.dumps(dict(exact_2x2=exact_small(), estimate=experiment(args.m, args.pairs, args.seed)),
                     indent=2, allow_nan=False))
