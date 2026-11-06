"""Independent finite check of observational join-congruence semantics.

Four two-bit bars; readout sees the first bit, rewrites are identity.
We compute the greatest observation-preserving congruence by refinement.
"""
import itertools
import unittest

STATES = tuple(itertools.product((False, True), repeat=2))


def observe(x):
    return x[0]


def rewrite(x):
    return x


def expose_join(x, y):
    return (x[0] ^ (x[1] and y[0]), x[1])


def opaque_join(x, y):
    return (x[0] ^ y[0], x[1] ^ y[1])


def blocks(join):
    # Readout fibers. Repeated signatures refine by every one-hole context:
    # a primitive rewrite, attaching each constant on the left or on the right.
    group = {x: int(observe(x)) for x in STATES}
    for _ in range(len(STATES)):
        sig = {x: (group[x], group[rewrite(x)],
                   *(group[join(x, z)] for z in STATES),
                   *(group[join(z, x)] for z in STATES)) for x in STATES}
        labels = {v: k for k, v in enumerate(dict.fromkeys(sig.values()))}
        newer = {x: labels[sig[x]] for x in STATES}
        if all((group[x] == group[y]) == (newer[x] == newer[y])
               for x in STATES for y in STATES):
            return newer
        group = newer
    raise AssertionError("refinement exceeded finite-state bound")


class JoinContextualEquivalenceTest(unittest.TestCase):
    def test_hidden_bit_exposed_by_join(self):
        a, b, z = (False, False), (False, True), (True, False)
        self.assertEqual(observe(a), observe(b))
        self.assertNotEqual(observe(expose_join(a, z)), observe(expose_join(b, z)))
        classes = blocks(expose_join)
        self.assertEqual(len(set(classes.values())), 4)
        for x, y in itertools.product(STATES, repeat=2):
            self.assertEqual(classes[x] == classes[y], x == y)

    def test_attachment_is_well_defined_after_context_quotient(self):
        for join in (expose_join, opaque_join):
            classes = blocks(join)
            for x, y, z, w in itertools.product(STATES, repeat=4):
                if classes[x] == classes[y] and classes[z] == classes[w]:
                    self.assertEqual(classes[join(x, z)], classes[join(y, w)])
            for x, y in itertools.product(STATES, repeat=2):
                if classes[x] == classes[y]:
                    self.assertEqual(observe(x), observe(y))
                    self.assertEqual(classes[rewrite(x)], classes[rewrite(y)])

    def test_old_quotient_is_sufficient_for_compatible_join(self):
        classes = blocks(opaque_join)
        self.assertEqual(len(set(classes.values())), 2)
        for x, y in itertools.product(STATES, repeat=2):
            self.assertEqual(classes[x] == classes[y], observe(x) == observe(y))

    def test_old_quotient_fails_for_exposing_join(self):
        a, b, z = (False, False), (False, True), (True, False)
        self.assertEqual(observe(a), observe(b))
        self.assertNotEqual(observe(expose_join(a, z)), observe(expose_join(b, z)))


if __name__ == "__main__":
    unittest.main()
