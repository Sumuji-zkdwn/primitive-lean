"""Exact independent checks for the finite two-metric sandpile model.

Uses standard Python only. A chip sent to the sink is lost; each site has one
sink edge in addition to all internal graph edges of length <= 1.
"""
from itertools import product
import unittest


def metric(a, b, c):
    """Pair distances (0,1)=a, (1,2)=b, (0,2)=c."""
    return ((0, a, c), (a, 0, b), (c, b, 0))


OUT = metric(1, 1, 2)
INSIDE = metric(1, 3, 4)
HIDDEN = metric(1, 2, 3)


def valid(d):
    return (
        all(d[i][i] == 0 for i in range(3))
        and all(d[i][j] == d[j][i] and (d[i][j] == 0) == (i == j)
                for i in range(3) for j in range(3))
        and all(d[i][k] <= d[i][j] + d[j][k]
                for i in range(3) for j in range(3) for k in range(3))
    )


def graph(d):
    return tuple(tuple(int(i != j and d[i][j] <= 1)
                       for j in range(3)) for i in range(3))


def degree(d, i):
    return 1 + sum(graph(d)[i])


def fire(d, c, i):
    assert c[i] >= degree(d, i)
    return tuple(c[j] - degree(d, i) if i == j else c[j] + graph(d)[i][j]
                 for j in range(3))


def stabilize(d, c, reverse=False):
    c = tuple(c)
    initial = sum(c)
    steps = 0
    while any(c[i] >= degree(d, i) for i in range(3)):
        order = range(2, -1, -1) if reverse else range(3)
        i = next(i for i in order if c[i] >= degree(d, i))
        c = fire(d, c, i)
        steps += 1
        assert sum(c) == initial - steps
        assert steps <= initial
    return c


class DualMetricChecks(unittest.TestCase):
    def test_metrics(self):
        for d in [OUT, INSIDE, HIDDEN]:
            self.assertTrue(valid(d))
        for i, j in product(range(3), repeat=2):
            self.assertLessEqual(OUT[i][j], INSIDE[i][j])
            self.assertLessEqual(INSIDE[i][j], 3 * OUT[i][j])
        self.assertNotEqual(OUT[1][2], INSIDE[1][2])

    def test_observer_chip_threshold(self):
        self.assertEqual(tuple(degree(OUT, i) for i in range(3)), (2, 3, 2))
        self.assertEqual(tuple(degree(INSIDE, i) for i in range(3)), (2, 2, 1))
        self.assertEqual(stabilize(OUT, (0, 1, 0)), (0, 1, 0))
        self.assertEqual(stabilize(INSIDE, (0, 1, 0)), (0, 1, 0))
        self.assertEqual(stabilize(OUT, (0, 2, 0)), (0, 2, 0))
        self.assertEqual(stabilize(INSIDE, (0, 2, 0)), (1, 0, 0))

    def test_hidden_geometry(self):
        self.assertNotEqual(INSIDE, HIDDEN)
        self.assertEqual(graph(INSIDE), graph(HIDDEN))
        for chips in product(range(5), repeat=3):
            self.assertEqual(stabilize(INSIDE, chips), stabilize(HIDDEN, chips))

    def test_order_independence_for_bounded_inputs(self):
        metrics = [metric(a, b, c)
                   for a, b, c in product(range(1, 5), repeat=3)
                   if valid(metric(a, b, c))]
        self.assertEqual(len(metrics), 52)
        for d in metrics:
            for chips in product(range(4), repeat=3):
                self.assertEqual(stabilize(d, chips),
                                 stabilize(d, chips, reverse=True),
                                 (d, chips))
        print("Checked 52 metric triples x 64 inputs = 3328 order comparisons")


if __name__ == "__main__":
    unittest.main(verbosity=2)
