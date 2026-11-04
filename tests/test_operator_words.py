"""Finite regression tests for the operator-word observation construction.

These are finite sanity checks, not a replacement for Lean proof checking.
"""
from itertools import product


def words(alphabet, max_length):
    return (w for n in range(max_length + 1) for w in product(alphabet, repeat=n))


def run(step, word, state):
    for symbol in word:
        state = step[symbol](state)
    return state


def compiled(code, word):
    return tuple(i for symbol in word for i in code[symbol])


def test_sequential_word_concatenation():
    step = {0: lambda x: (x + 1) % 3, 1: lambda x: 2 - x}
    for x in range(3):
        for a in words((0, 1), 3):
            for b in words((0, 1), 3):
                assert run(step, a + b, x) == run(step, b, run(step, a, x))


def test_compilation_preserves_actions_on_every_state():
    old = {0: lambda x: (x + 1) % 3, 1: lambda x: 2 - x}
    code = {0: (0, 1, 0), 1: (), 2: (1, 1)}
    new = {j: (lambda x, j=j: run(old, code[j], x)) for j in code}
    for x in range(3):
        for word in words(tuple(new), 5):
            assert run(new, word, x) == run(old, compiled(code, word), x)


def test_generated_language_never_refines_old_equivalence():
    # Multiple readouts, old actions and generated dictionaries.
    old = {0: lambda x: (x + 1) % 3, 1: lambda x: 2 - x}
    dictionaries = (
        {0: (), 1: (0, 0)},
        {0: (1,), 1: (0, 1)},
        {0: (0, 1), 1: (1, 0, 0)},
    )
    for output in product((0, 1), repeat=3):
        for x in range(3):
            for y in range(3):
                equivalent = all(
                    output[run(old, word, x)] == output[run(old, word, y)]
                    for word in words(tuple(old), 4)
                )
                if not equivalent:
                    continue
                for code in dictionaries:
                    new = {j: (lambda z, j=j: run(old, code[j], z)) for j in code}
                    assert all(
                        output[run(new, word, x)] == output[run(new, word, y)]
                        for word in words(tuple(new), 4)
                    )


def test_independent_transition_can_refine_equivalence():
    output = lambda x: int(x == 2)
    old = {None: lambda x: x}
    new = {False: lambda x: x, True: lambda x: 2 if x == 1 else x}
    assert all(
        output(run(old, word, 0)) == output(run(old, word, 1))
        for word in words(tuple(old), 4)
    )
    assert output(run(new, (True,), 0)) != output(run(new, (True,), 1))
