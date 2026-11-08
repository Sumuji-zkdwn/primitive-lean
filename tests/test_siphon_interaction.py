"""Independent finite arithmetic checks of the siphon interaction model.

No Lean implementation or physical simulation is imported here.  Integer
enumeration tests the exact-potential theorem; a toy hydraulic calculation
only demonstrates the *non*-invariance of discharge under path replacement.
"""

import itertools
import math
import unittest


def accumulated(E, start, path):
    total = 0
    current = start
    for nxt in path:
        total += E[nxt] - E[current]
        current = nxt
    return total


def has_chain(weights, n):
    return all(
        weights[a, b] + weights[b, c] == weights[a, c]
        for a, b, c in itertools.product(range(n), repeat=3)
    )


def has_anchor_potential(weights, n, anchor=0):
    E = {x: weights[anchor, x] for x in range(n)}
    return all(weights[a, b] == E[b] - E[a]
               for a, b in itertools.product(range(n), repeat=2))


class SiphonChecks(unittest.TestCase):
    def test_all_small_potential_paths(self):
        tested = 0
        for values in itertools.product((-2, 0, 3), repeat=3):
            for start in range(3):
                for size in range(6):
                    for word in itertools.product(range(3), repeat=size):
                        end = word[-1] if word else start
                        self.assertEqual(accumulated(values, start, word),
                                         values[end] - values[start])
                        tested += 1
        self.assertEqual(tested, 29484)  # 3^3 * 3 * sum(3^k, k=0..5)

    def test_chain_exactness_exhaustive(self):
        n = 3
        edges = tuple(itertools.product(range(n), repeat=2))
        potentials = 0
        for vals in itertools.product((-1, 0, 1), repeat=len(edges)):
            weights = dict(zip(edges, vals))
            chain = has_chain(weights, n)
            potential = has_anchor_potential(weights, n)
            self.assertEqual(chain, potential)
            potentials += chain
        self.assertEqual(potentials, 7)

    def test_same_endpoints_different_costs(self):
        heights = {0: 1, 1: 4, 2: 2, 3: 0}
        short, long = (1, 3), (1, 2, 3)
        self.assertEqual(accumulated(heights, 0, short),
                         accumulated(heights, 0, long))
        self.assertNotEqual(len(short), len(long))
        self.assertEqual(accumulated(heights, 0, short), -1)

    def test_hydraulic_same_head_different_discharge(self):
        # Dimensioned illustrative model: v=sqrt(2*g*dz/(1+f*L/D)),
        # equal diameter, roughness and reservoir/outlet heights.
        g, dz, f, diameter = 9.81, 2.0, 0.03, 0.02
        def speed(length):
            return math.sqrt(2*g*dz/(1+f*length/diameter))
        self.assertGreater(speed(8.0), speed(12.0))
        self.assertAlmostEqual(speed(8.0), math.sqrt(39.24/13))
        self.assertAlmostEqual(speed(12.0), math.sqrt(39.24/19))

    def test_apex_pressure_depends_on_geometry(self):
        # Idealized inviscid steady Bernoulli, p_crest = p_atm
        # +rho*g*(z_surface-z_crest)-rho*v^2/2; no claim about cavitation.
        patm, rho, g, z_surface, speed = 101325, 1000, 9.81, 2.0, 1.0
        def p_at_crest(z):
            return patm + rho*g*(z_surface-z) - rho*speed**2/2
        self.assertGreater(p_at_crest(3.0), p_at_crest(5.0))
        self.assertAlmostEqual(p_at_crest(3.0)-p_at_crest(5.0),
                               2*rho*g)


if __name__ == "__main__":
    unittest.main()
