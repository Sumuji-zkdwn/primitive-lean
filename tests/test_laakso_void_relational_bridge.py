"""Independent finite check of first-level Laakso sheet-gluing and relational completeness."""
import itertools
import unittest

RAW = tuple((kind, i, sheet) for kind in ("old", "new")
            for i in range(2) for sheet in (False, True))
OBS = tuple(range(6))

def observe(x):
    kind, i, b = x
    return 2 * i + int(b) if kind == "old" else 4 + i

def advance(x):
    kind, i, b = x
    if kind == "old":
        return x
    return ("new", 1, b) if i == 0 else ("old", 1, b)

def fiber(q):
    return frozenset(x for x in RAW if observe(x) == q)

def rel_step(q):
    return frozenset(observe(advance(x)) for x in fiber(q))

def rel_set(labels):
    return frozenset(z for q in labels for z in rel_step(q))

def saturated(U):
    labels = frozenset(observe(x) for x in U)
    return frozenset(x for x in RAW if observe(x) in labels)

class LaaksoVoidBridgeTest(unittest.TestCase):
    def test_actual_refined_graph_edges(self):
        source = (0, 1, 4, 4, 5, 5)
        target = (4, 4, 5, 5, 2, 3)
        for b in (False, True):
            mid = 3 if b else 2
            right = 5 if b else 4
            w1, w2 = ("new", 0, b), ("new", 1, b)
            self.assertEqual((observe(w1), observe(advance(w1))),
                             (source[mid], target[mid]))
            self.assertEqual((observe(w2), observe(advance(w2))),
                             (source[right], target[right]))

    def test_six_seven_eight_predictive_states(self):
        for depth, expected in [(0, 6), (1, 7), (2, 8), (3, 8)]:
            signatures = []
            for x in RAW:
                word = []
                for i in range(depth + 1):
                    word.append(observe(x))
                    x = advance(x)
                signatures.append(tuple(word))
            self.assertEqual(len(set(signatures)), expected)

    def test_multivalued_but_exact_on_saturated_sets(self):
        self.assertEqual(rel_step(4), frozenset({5}))
        self.assertEqual(rel_step(5), frozenset({2, 3}))
        for q in OBS:
            output = {advance(x) for x in fiber(q)}
            self.assertEqual(saturated(output), output)
        for mask in range(64):
            labels = frozenset(q for q in OBS if mask & (1 << q))
            exact = saturated({x for x in RAW if observe(x) in labels})
            coarse = labels
            for t in range(10):
                self.assertEqual(coarse, frozenset(observe(x) for x in exact), (mask,t))
                coarse = rel_set(coarse)
                exact = frozenset(advance(x) for x in exact)

    def test_arbitrary_singleton_is_not_globally_exact(self):
        x, y = ("new", 0, False), ("new", 0, True)
        self.assertEqual(observe(x), observe(y))
        self.assertEqual(observe(advance(x)), observe(advance(y)))
        self.assertNotEqual(observe(advance(advance(x))),
                            observe(advance(advance(y))))
        self.assertEqual(rel_set(rel_set({observe(x)})), frozenset({2, 3}))
        self.assertEqual({observe(advance(advance(x)))}, {2})

if __name__ == "__main__":
    unittest.main()
