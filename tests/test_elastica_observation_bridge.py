"""Exhaustive finite-state check of the curvature-observer refinement example.

No Lean interface is used here; independent Python BFS checks the quotient
semantics for every pair and all reachable operator-word continuations.
"""
from collections import deque
from itertools import product
import unittest

STATES = (0, 1, 2)
K = (0, 0, 1)  # From the actual signed curvature of 0, 1, s at s=0.


def old(x):
    return x


def fresh(x):
    return 2 if x == 1 else x


def inert(x):
    return x


def word_equivalent(x, y, actions):
    """Search the complete reachable ordered-pair automaton, not a cutoff."""
    pending = deque([(x, y)])
    visited = set()
    while pending:
        a, b = pending.popleft()
        if K[a] != K[b]:
            return False
        if (a, b) in visited:
            continue
        visited.add((a, b))
        for transition in actions:
            pending.append((transition(a), transition(b)))
    return True


def classes(actions):
    groups = []
    for state in STATES:
        for group in groups:
            if word_equivalent(state, group[0], actions):
                group.append(state)
                break
        else:
            groups.append([state])
    return tuple(frozenset(g) for g in groups)


class ObservationBridgeFiniteCheck(unittest.TestCase):
    def test_all_pairs_equivalence_is_an_equivalence_relation(self):
        for actions in ((old,), (old, fresh), (old, inert)):
            for x, y, z in product(STATES, repeat=3):
                self.assertTrue(word_equivalent(x, x, actions))
                self.assertEqual(word_equivalent(x, y, actions),
                                 word_equivalent(y, x, actions))
                if (word_equivalent(x, y, actions)
                        and word_equivalent(y, z, actions)):
                    self.assertTrue(word_equivalent(x, z, actions))

    def test_strict_refinement_partition(self):
        self.assertEqual(classes((old,)),
                         (frozenset((0, 1)), frozenset((2,))))
        self.assertEqual(classes((old, fresh)),
                         (frozenset((0,)), frozenset((1,)), frozenset((2,))))
        self.assertTrue(word_equivalent(0, 1, (old,)))
        self.assertFalse(word_equivalent(0, 1, (old, fresh)))
        self.assertEqual((K[fresh(0)], K[fresh(1)]), (0, 1))

    def test_inert_extension_is_bijective_on_quotient(self):
        self.assertEqual(classes((old, inert)), classes((old,)))
        for x, y in product(STATES, repeat=2):
            self.assertEqual(word_equivalent(x, y, (old, inert)),
                             word_equivalent(x, y, (old,)))

    def test_forget_is_well_defined_and_surjective(self):
        old_groups = classes((old,))
        for actions in ((old, fresh), (old, inert)):
            new_groups = classes(actions)
            images = []
            for new_group in new_groups:
                targets = [o for o in old_groups if new_group <= o]
                self.assertEqual(len(targets), 1)
                images.append(targets[0])
            self.assertEqual(set(images), set(old_groups))
            self.assertEqual(len(images) == len(set(images)),
                             actions == (old, inert))


if __name__ == "__main__":
    unittest.main(verbosity=2)
