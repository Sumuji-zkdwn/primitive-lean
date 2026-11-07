#!/usr/bin/env python3
"""Independent exact finite-state check of the Elastica 4-direction bridge.

SymPy evaluates the true constant-angle xCoord integral and an independent
finite partition-refinement procedure computes both predictive quotients.
This is NOT a Lean kernel check.
"""
import itertools
import sympy as sp

angles = (sp.Integer(0), sp.pi/2, sp.pi, -sp.pi/2)
states = range(4)
old = (0, 3, 2, 1)
fresh = (1, 2, 3, 0)
u = sp.symbols("u", real=True)
readout = tuple(sp.simplify(sp.integrate(sp.cos(angles[i]), (u, 0, 1)))
                for i in states)
assert readout == (1, 0, -1, 0)

def run(word, state):
    for action in word:
        state = (old if action == 0 else fresh)[state]
    return state

def quotient(actions):
    classes = [{i for i in states if readout[i] == value}
               for value in dict.fromkeys(readout)]
    while True:
        def signature(i):
            return (readout[i], tuple(
                next(k for k, block in enumerate(classes)
                     if (old if action == 0 else fresh)[i] in block)
                for action in actions))
        signatures = {i: signature(i) for i in states}
        next_classes = [{i for i in states if signatures[i] == key}
                        for key in dict.fromkeys(signatures.values())]
        if {frozenset(x) for x in next_classes} == {frozenset(x) for x in classes}:
            return sorted(tuple(sorted(x)) for x in classes)
        classes = next_classes

def profile(actions, state, n=5):
    return tuple(readout[run(w, state)]
                 for k in range(n + 1)
                 for w in itertools.product(actions, repeat=k))

old_classes = quotient((0,))
new_classes = quotient((0, 1))
assert old_classes == [(0,), (1, 3), (2,)]
assert new_classes == [(0,), (1,), (2,), (3,)]
assert profile((0,), 1) == profile((0,), 3)
assert profile((0, 1), 1) != profile((0, 1), 3)
assert (readout[fresh[1]], readout[fresh[3]]) == (-1, 1)
print("PASS", readout, "old quotient", old_classes, "new quotient", new_classes)
