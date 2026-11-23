"""Independent checks for the same-square construction. Python standard library only.

From gemini-notebook-laakso run
    python -B -m unittest discover -s formalization -p test_single_square.py
Coordinates are one-based in the mathematics. Arrays below use row-major indices.
"""

from collections import Counter, deque
from functools import lru_cache
from heapq import heappop, heappush
from itertools import product
from math import gcd
import unittest


def period_bit(j, modulus):
    period = modulus // gcd(modulus, j)
    power, bit = 3, 1
    while power < period:
        power *= 3
        bit <<= 1
    assert power == period
    return period, bit


class Square:
    def __init__(self, m):
        self.modulus = 3**m
        self.n = self.modulus - 1
        self.size = self.n**2
        self.adjacent = []
        self.clock = []
        for i, j in product(range(self.n), repeat=2):
            self.adjacent.append(tuple(x * self.n + y for x, y in
                                       ((i-1, j), (i+1, j), (i, j-1), (i, j+1))
                                       if 0 <= x < self.n and 0 <= y < self.n))
            self.clock.append((i + 1) * (j + 1))
        self.masks = self.solve_harmonic_fields()

    def solve_harmonic_fields(self):
        # Solve the full mod-two system by row reduction, independently of the
        # row-to-row recurrence in square_clock.py. Store all m right sides together.
        system = [[sum(1 << v for v in neighbors), 0] for neighbors in self.adjacent]
        system.extend([1 << column, period_bit(column + 1, self.modulus)[1]]
                      for column in range(self.n))
        for column in range(self.size):
            pivot = next(i for i in range(column, len(system))
                         if (system[i][0] >> column) & 1)
            system[column], system[pivot] = system[pivot], system[column]
            for i, row in enumerate(system):
                if i != column and (row[0] >> column) & 1:
                    row[0] ^= system[column][0]
                    row[1] ^= system[column][1]
        assert all(row == [0, 0] for row in system[self.size:])
        return tuple(system[i][1] for i in range(self.size))

    def observe(self, heights):
        phase = sum(c * h for c, h in zip(self.clock, heights)) % self.modulus
        angle = (pow(2, -1, self.modulus) * phase) % self.modulus
        bits = 0
        for h, mask in zip(heights, self.masks):
            if h % 2:
                bits ^= mask
        return angle, bits

    def drive(self, heights, j, grains):
        # Parallel waves with wired sink, independent of the previous sequential replay.
        h = list(heights)
        h[j - 1] += grains
        lost = 0
        while True:
            active = [(v, count // 4) for v, count in enumerate(h) if count >= 4]
            if not active:
                break
            for v, times in active:
                h[v] -= 4 * times
                for target in self.adjacent[v]:
                    h[target] += times
                lost += (4 - len(self.adjacent[v])) * times
        assert sum(h) + lost == sum(heights) + grains
        return tuple(h)

    def recurrent(self, state):
        unburnt = set(range(self.size))
        while unburnt:
            burning = {i for i in unburnt
                       if state[i] >= sum(v in unburnt for v in self.adjacent[i])}
            if not burning:
                return False
            unburnt -= burning
        return True

    def sample(self, m):
        if m == 1:
            states = [s for s in product(range(4), repeat=self.size) if self.recurrent(s)]
            counts = Counter(self.observe(s) for s in states)
            assert len(states) == 192 and len(counts) == 6 and set(counts.values()) == {32}
            return states
        initial = (3,) * self.size
        representatives = {self.observe(initial): initial}
        queue = deque([initial])
        while queue:
            state = queue.popleft()
            for j in range(1, self.modulus):
                new = self.drive(state, j, 1)
                observation = self.observe(new)
                if observation not in representatives:
                    representatives[observation] = new
                    queue.append(new)
        assert len(representatives) == self.modulus * 2**m
        assert all(self.recurrent(s) for s in representatives.values())
        return list(representatives.values())


def horizontal_coordinates(modulus, b):
    # 4 M^2 is the length unit denominator. For b=1 the primitive of
    # |2t-1| is (1 + (2t-1)|2t-1|)/4, including the edge crossing 1/2.
    if b == 0:
        return tuple(4 * modulus * j for j in range(modulus + 1))
    assert b == 1
    return tuple(modulus**2 + (2*j-modulus) * abs(2*j-modulus)
                 for j in range(modulus + 1))


def height_sweep(coords, a, b, differing):
    # On a line the height range of a path is an interval. It must contain
    # at least one eligible gate for each changed bit. Both endpoint orders
    # around that interval can be attained with each necessary switch once.
    modulus = len(coords) - 1
    best = None
    for left in range(min(a, b) + 1):
        gates = 0
        for right in range(left, modulus + 1):
            if 0 < right < modulus:
                gates |= period_bit(right, modulus)[1]
            if right < max(a, b) or differing & ~gates:
                continue
            traverse = coords[right] - coords[left]
            enter_exit = min(coords[a] - coords[left] + coords[right] - coords[b],
                             coords[right] - coords[a] + coords[b] - coords[left])
            cost = traverse + enter_exit
            best = cost if best is None else min(best, cost)
    assert best is not None
    return best


def observed_product_graph(m, coords):
    modulus = 3**m
    graph = {}
    # Work in raw clock phase; the theoretical angular distance below is
    # computed in the separately recoded angle coordinate.
    for j, bits, phase in product(range(modulus+1), range(2**m), range(modulus)):
        adjacent = [((j, bits, (phase+s) % modulus), 4*modulus) for s in (-2, 2)]
        for k in (j-1, j+1):
            if 0 <= k <= modulus:
                adjacent.append(((k, bits, phase), abs(coords[k]-coords[j])))
        if 0 < j < modulus:
            adjacent.append(((j, bits ^ period_bit(j, modulus)[1], phase), 0))
        graph[(j, bits, phase)] = adjacent
    return graph


def distances(graph, start):
    known = {start: 0}
    queue = [(0, start)]
    while queue:
        current, v = heappop(queue)
        if current != known[v]:
            continue
        for w, fee in graph[v]:
            candidate = current + fee
            if w not in known or candidate < known[w]:
                known[w] = candidate
                heappush(queue, (candidate, w))
    return known


class SingleSquareTests(unittest.TestCase):
    def test_actual_angular_steps_and_commuting_returns(self):
        counts = []
        for m in (1, 2):
            square = Square(m)
            modulus = square.modulus
            trials = 0
            for state in square.sample(m):
                r, bits = square.observe(state)
                turn = square.drive(state, 1, 2)
                self.assertEqual(turn, square.drive(square.drive(state, 1, 1), 1, 1))
                self.assertEqual(square.observe(turn), ((r+1) % modulus, bits))
                back = square.drive(state, modulus-1, 2)
                self.assertEqual(square.observe(back), ((r-1) % modulus, bits))
                self.assertEqual(square.observe(square.drive(turn, modulus-1, 2)),
                                 (r, bits))
                if m == 2:
                    # Three finer turns implement one coarse angular edge.
                    # These two drives agree on observations, not necessarily heights.
                    self.assertEqual(square.observe(square.drive(state, 1, 6)),
                                     square.observe(square.drive(state, 3, 2)))
                for j in range(1, modulus):
                    period, bit = period_bit(j, modulus)
                    running = state
                    for k in range(1, period+1):
                        running = square.drive(running, j, 1)
                        angle, label = square.observe(running)
                        self.assertEqual(angle == r, k == period)
                        self.assertEqual(label, bits ^ (bit if k % 2 else 0))
                    gate = square.drive(state, j, period)
                    self.assertEqual(running, gate)
                    self.assertEqual(square.observe(gate), (r, bits ^ bit))
                    # Commutation holds even on the complete stabilized configuration.
                    turn_gate = square.drive(turn, j, period)
                    self.assertEqual(turn_gate, square.drive(gate, 1, 2))
                    self.assertEqual(square.observe(turn_gate), ((r+1) % modulus, bits ^ bit))
                    trials += 1
            counts.append(trials)
        self.assertEqual(counts, [384, 288])

    def test_refinement_of_phases_bits_and_lengths(self):
        for m in range(1, 6):
            coarse = 3**m
            fine = 3*coarse
            for j in range(1, fine):
                period, bit = period_bit(j, fine)
                if j % 3:
                    self.assertEqual((period, bit), (fine, 1 << m))
                else:
                    self.assertEqual((period, bit), period_bit(j//3, coarse))
            for phase in range(coarse):
                theta = (pow(2, -1, coarse) * phase) % coarse
                fine_theta = (pow(2, -1, fine) * (3 * phase)) % fine
                self.assertEqual(fine_theta, 3 * theta)
                self.assertEqual((fine_theta + 3) % fine, 3 * ((theta + 1) % coarse))
            for b in (0, 1):
                a = horizontal_coordinates(coarse, b)
                f = horizontal_coordinates(fine, b)
                self.assertEqual(tuple(f[3*j] for j in range(coarse+1)),
                                 tuple(9*x for x in a))

    def test_all_pairs_weighted_product_distance(self):
        for m in (1, 2):
            modulus = 3**m
            inv = pow(2, -1, modulus)
            for b in (0, 1):
                coords = horizontal_coordinates(modulus, b)
                graph = observed_product_graph(m, coords)
                sweep = lru_cache(maxsize=None)(height_sweep)
                for start in graph:
                    found = distances(graph, start)
                    self.assertEqual(len(found), len(graph))
                    j, bits, phase = start
                    for (k, label, other), d in found.items():
                        delta = ((phase-other)*inv) % modulus
                        angular = 4*modulus * min(delta, modulus-delta)
                        self.assertEqual(d, sweep(coords, j, k, bits ^ label) + angular)


if __name__ == "__main__":
    unittest.main()
