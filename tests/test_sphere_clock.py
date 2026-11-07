"""Independent exhaustive finite checks of the sphere clock."""
from itertools import product
import unittest

def needle(route, t, point):
    _latitude, longitude = point
    return int(route[t] == longitude)

def dial(route, t, point):
    return sum(needle(route, k, point) for k in range(t))

class SphereClockCheck(unittest.TestCase):
    def test_discrete_difference_all_routes(self):
        for width in range(1, 5):
            for route in product(range(width), repeat=4):
                for t in range(4):
                    for p in product(range(3), range(width)):
                        self.assertEqual(needle(route, t, p),
                            dial(route, t + 1, p) - dial(route, t, p))

    def test_entire_dial_history_fixes_route(self):
        routes = list(product(range(3), repeat=3))
        for u in routes:
            for v in routes:
                same = all(dial(u, t, (0, lon)) == dial(v, t, (0, lon))
                    for t in range(4) for lon in range(3))
                self.assertEqual(same, u == v)

    def test_final_dial_can_forget_order(self):
        u, v = (0, 1), (1, 0)
        self.assertNotEqual(u, v)
        for p in product(range(3), range(2)):
            self.assertEqual(dial(u, 2, p), dial(v, 2, p))
        self.assertNotEqual(needle(u, 0, (0, 0)), needle(v, 0, (0, 0)))

    def test_meridian_covers_all_latitudes(self):
        self.assertEqual([needle((1,), 0, (lat, 1)) for lat in range(5)],
                         [1] * 5)
        self.assertEqual([needle((1,), 0, (lat, 0)) for lat in range(5)],
                         [0] * 5)

if __name__ == "__main__":
    unittest.main(verbosity=2)
