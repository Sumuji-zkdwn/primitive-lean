"""Finite-state partition refinement for a labelled deterministic operator family.

For N states and r initial output classes, the stable quotient is reached
after at most N-r refinements. Tests compare the efficient partition
algorithm with direct exhaustive enumeration of finite operator words.

These tests are independent computational cross-checks, not Lean proofs.
"""
from itertools import product
import random


def words(alphabet, length):
    if length == 0:
        yield ()
    else:
        for parts in product(alphabet, repeat=length):
            yield parts


def run(steps, word, x):
    for action in word:
        x = steps[action][x]
    return x


def labels(signature):
    ids = {}
    result = []
    for value in signature:
        if value not in ids:
            ids[value] = len(ids)
        result.append(ids[value])
    return tuple(result)


def partition_history(outputs, steps):
    """Return signature classes at each depth, ending at the first plateau."""
    current = labels(outputs)
    history = [current]
    while True:
        next_signature = tuple(
            (current[x], tuple(current[steps[a][x]] for a in range(len(steps))))
            for x in range(len(outputs))
        )
        updated = labels(next_signature)
        history.append(updated)
        if updated == current:
            return history
        current = updated


def word_kernel(outputs, steps, horizon):
    states = range(len(outputs))
    alphabet = range(len(steps))
    all_words = [word for n in range(horizon + 1)
                 for word in words(alphabet, n)]
    return {
        (x, y) for x in states for y in states
        if all(outputs[run(steps, w, x)] == outputs[run(steps, w, y)]
               for w in all_words)
    }


def partition_kernel(classes):
    return {
        (x, y) for x in range(len(classes))
        for y in range(len(classes)) if classes[x] == classes[y]
    }


def verify_case(outputs, steps):
    n = len(outputs)
    history = partition_history(outputs, steps)
    r = len(set(outputs))
    stable = history[-1]
    assert len(history) - 2 <= n - r
    assert len(history) <= n - r + 2
    assert partition_kernel(stable) == word_kernel(outputs, steps, n - r)
    for depth in range(n - r + 1):
        idx = min(depth, len(history) - 1)
        assert partition_kernel(history[idx]) == word_kernel(outputs, steps, depth)
    assert partition_kernel(history[0]) == partition_kernel(labels(outputs))
    assert history[-1] == history[-2]


def test_exhaustive_three_states_two_operator_actions():
    # 2 readout values, two arbitrary transitions, all 3-state functions.
    for outputs in product(range(2), repeat=3):
        for left in product(range(3), repeat=3):
            for right in product(range(3), repeat=3):
                verify_case(outputs, (left, right))


def test_random_four_and_five_state_operators():
    rng = random.Random(11042026)
    for size, cases in ((4, 250), (5, 125)):
        for _ in range(cases):
            outputs = tuple(rng.randrange(3) for _ in range(size))
            steps = tuple(
                tuple(rng.randrange(size) for _ in range(size))
                for _ in range(rng.randrange(1, 4))
            )
            verify_case(outputs, steps)


def test_original_identity_and_new_action_split():
    outputs = (0, 0, 1)
    old = ((0, 1, 2),)
    extended = ((0, 1, 2), (0, 2, 2))
    assert (0, 1) in partition_kernel(partition_history(outputs, old)[-1])
    assert (0, 1) not in partition_kernel(partition_history(outputs, extended)[-1])
    assert len(set(partition_history(outputs, old)[-1])) == 2
    assert len(set(partition_history(outputs, extended)[-1])) == 3


def test_generated_ops_do_not_split_old_kernel():
    rng = random.Random(1114)
    for size in (3, 4, 5):
        for _ in range(100):
            outputs = tuple(rng.randrange(3) for _ in range(size))
            original = tuple(
                tuple(rng.randrange(size) for _ in range(size))
                for _ in range(2)
            )
            code = ((0, 1), (), (1, 0, 1))
            synthetic = tuple(
                tuple(run(original, word, x) for x in range(size))
                for word in code
            )
            assert partition_kernel(partition_history(outputs, original)[-1]) == (
                partition_kernel(partition_history(outputs, original + synthetic)[-1])
            )
