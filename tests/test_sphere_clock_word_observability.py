"""Exhaustive independent check of endpoint observability.

On G = Z/12, H = {0, 3, 6, 9}, compare all 8 normal-form
transformations at every one of the 20 quotient states.
This finite check is not a proof for G = R/Z.
"""
from itertools import product
from test_sphere_clock_word_normal_form import CLASSES, H, cls, flip, rotate


def endpoint(state, angle, odd):
    moved = rotate(state, angle)
    return cls(flip(moved) if odd else moved)


normal_forms = list(product(sorted(H), (False, True)))
pairwise_checks = 0
for state in CLASSES:
    theta, _ = state
    for (d, odd), (e, other) in product(normal_forms, repeat=2):
        observed_equal = endpoint(state, d, odd) == endpoint(state, e, other)
        criterion = d == e and (odd == other or theta in H)
        assert observed_equal == criterion, (state, d, e, odd, other)
        pairwise_checks += 1
assert pairwise_checks == 20 * 8 * 8 == 1280

# Global equality of actions: exactly one action per pair (total 8).
global_comparisons = 0
for a, b in product(normal_forms, repeat=2):
    same_map = all(endpoint(p, *a) == endpoint(p, *b) for p in CLASSES)
    assert same_map == (a == b)
    global_comparisons += 1
assert global_comparisons == 64

# At the glued locus, both bits are identified, for any allowed increment.
for p in CLASSES:
    theta, _ = p
    for delta in H:
        no_flip = endpoint(p, delta, False)
        flipped = endpoint(p, delta, True)
        assert (no_flip == flipped) == (theta in H)

# Outside H, a single known starting point determines a normal form.
for p in CLASSES:
    if p[0] not in H:
        outcomes = {endpoint(p, *a) for a in normal_forms}
        assert len(outcomes) == 8

print("PASS: exact endpoint iff for 1280 point/form-pair cases")
print("PASS: global action iff for 64 pairs; 8 forms distinguishable off gluing")
