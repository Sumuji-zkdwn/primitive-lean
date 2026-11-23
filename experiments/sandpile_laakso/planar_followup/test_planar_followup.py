"""Replay saved research outputs and check the distance cost of grain inputs."""

import heapq
import json
from math import gcd
from pathlib import Path
import subprocess
import sys
import unittest


HERE = Path(__file__).resolve().parent


def switch_distances(levels, start, grain_cost):
    """Use integer units of 1/M horizontally. Each switch needs its return period in grains."""
    modulus = 3**levels
    labels = 2**levels
    period_bit = {3**k: 1 << (k - 1) for k in range(1, levels + 1)}
    distance = {start: 0}
    queue = [(0, start)]
    while queue:
        cost, vertex = heapq.heappop(queue)
        if cost != distance[vertex]:
            continue
        height, bits = divmod(vertex, labels)
        steps = []
        if height:
            steps.append((vertex - labels, 1))
        if height < modulus:
            steps.append((vertex + labels, 1))
        if 0 < height < modulus:
            period = modulus // gcd(height, modulus)
            steps.append((height * labels + (bits ^ period_bit[period]), period * grain_cost))
        for other, length in steps:
            candidate = cost + length
            if other not in distance or candidate < distance[other]:
                distance[other] = candidate
                heapq.heappush(queue, (candidate, other))
    return distance


class PlanarSandpileTests(unittest.TestCase):
    def check_replay(self, script, snapshot):
        expected = json.loads((HERE / snapshot).read_text(encoding="utf-8"))
        output = subprocess.check_output(
            [sys.executable, "-B", str(HERE / script)], cwd=HERE, timeout=180
        )
        self.assertEqual(json.loads(output), expected)

    def test_planar_firings_and_merge_levels(self):
        self.check_replay("planar_sandpile.py", "planar_results.json")

    def test_translated_sibling_responses(self):
        self.check_replay("local_response.py", "local_response.json")

    def test_square_return_periods(self):
        self.check_replay("square_clock.py", "square_clock_results.json")

    def test_gate_closure_graphs(self):
        self.check_replay("gate_closures.py", "gate_closures_results.json")

    def test_distance_charged_for_every_grain(self):
        for levels in (1, 2, 3):
            labels = 2**levels
            vertices = (3**levels + 1) * labels
            for start in range(vertices):
                free = switch_distances(levels, start, 0)
                paid = switch_distances(levels, start, 1)
                self.assertEqual(len(free), vertices)
                for end, length in free.items():
                    differing = (start % labels) ^ (end % labels)
                    extra = sum(
                        3**(k + 1) for k in range(levels) if differing & (1 << k)
                    )
                    self.assertEqual(paid[end] - length, extra)


if __name__ == "__main__":
    unittest.main()
