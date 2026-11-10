"""Finite independent checks of observer-relative separating depths.

This is a finite oracle, not a substitute for the Lean proof.
An allowed-word distinction has length zero when immediate readouts differ.
If no continuation works, depth is None (the mathematical infinity case).
"""
from collections import deque
from itertools import combinations, product
import unittest


def shortest_depth(actions, observe, x, y, allowed):
    """BFS on ordered pairs is exact for deterministic finite-state systems."""
    queue = deque([(x, y, 0)])
    visited = {(x, y)}
    while queue:
        a, b, depth = queue.popleft()
        if observe[a] != observe[b]:
            return depth
        for action in allowed:
            aa, bb = actions[action][a], actions[action][b]
            if (aa, bb) not in visited:
                visited.add((aa, bb))
                queue.append((aa, bb, depth + 1))
    return None


class ObserverOrientationDepthTest(unittest.TestCase):
    def test_exhaustive_monotonicity_on_three_states(self):
        subsets = [tuple(i for i in range(2) if mask & (1 << i))
                   for mask in range(4)]
        comparisons = 0
        for step0 in product(range(3), repeat=3):
            for step1 in product(range(3), repeat=3):
                actions = (step0, step1)
                for observe in product(range(2), repeat=3):
                    for x, y in combinations(range(3), 2):
                        depths = {
                            allowed: shortest_depth(actions, observe, x, y, allowed)
                            for allowed in subsets
                        }
                        for smaller in subsets:
                            for larger in subsets:
                                if not set(smaller).issubset(larger):
                                    continue
                                a, b = depths[smaller], depths[larger]
                                self.assertTrue(
                                    a is None or (b is not None and b <= a),
                                    (actions, observe, x, y, smaller, larger, a, b),
                                )
                                comparisons += 1
        self.assertEqual(comparisons, 157464)

    def test_real_new_action_separates_without_old_actions(self):
        identity = (0, 1, 2)
        fresh = (0, 2, 2)
        observation = (0, 0, 1)
        actions = (identity, fresh)
        self.assertIsNone(shortest_depth(actions, observation, 0, 1, (0,)))
        self.assertEqual(shortest_depth(actions, observation, 0, 1, (0, 1)), 1)

    def test_macro_can_shorten_depth_without_new_distinctions(self):
        primitive = (0, 2, 3, 3)
        macro = tuple(primitive[primitive[i]] for i in range(4))
        observation = (0, 0, 0, 1)
        self.assertEqual(shortest_depth((primitive,), observation, 0, 1, (0,)), 2)
        self.assertEqual(shortest_depth((primitive, macro), observation, 0, 1, (0, 1)), 1)
        for x in range(4):
            for y in range(4):
                old = shortest_depth((primitive,), observation, x, y, (0,))
                new = shortest_depth((primitive, macro), observation, x, y, (0, 1))
                self.assertEqual(old is None, new is None)


if __name__ == "__main__":
    unittest.main()
