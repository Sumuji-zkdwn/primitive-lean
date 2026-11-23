"""Replay the two reflected sandpiles. Run with python -B clock_avalanche_witness.py --m 2 3."""

import argparse
from collections import deque
from itertools import chain, repeat
import json
from math import comb

from square_clock import add_one, burns, instruments, observe


def stabilize_bulk(heights, adjacent):
    """Batch legal firings at each unstable vertex of a nonnegative configuration."""
    pending = deque(i for i, h in enumerate(heights) if h >= 4)
    while pending:
        i = pending.popleft()
        count, heights[i] = divmod(heights[i], 4)
        for j in adjacent[i]:
            heights[j] += count
            if heights[j] - count < 4 <= heights[j]:
                pending.append(j)
    return tuple(heights)


def reflect(state, n):
    return tuple(state[r * n + c] for r in range(n) for c in reversed(range(n)))


def verify(m):
    modulus, adjacent, clock, masks = instruments(m)
    n = modulus - 1
    left, right = 0, n - 1
    steps = modulus**2
    k = (steps - 1) // 2
    target = [3] * (n * n)
    target[left] = target[n + n // 2 - 1] = 1  # One-based (1,1) and (2,n/2).
    target = tuple(target)
    targets = (target, reflect(target, n))

    # sigma = Delta 1 counts sink edges. k*sigma minus the prefix input is
    # nonnegative; adding it to a recurrent target inverts the balanced prefix.
    heights = [h + k * (4 - len(ys)) for h, ys in zip(target, adjacent)]
    heights[left] -= 2 * k
    heights[right] -= 2 * k
    assert min(heights) >= 0
    first = stabilize_bulk(heights, adjacent)
    initial = (first, reflect(first, n))
    assert sum(initial[0]) == sum(initial[1])
    for state in (*initial, *targets):
        assert burns(state, adjacent)

    def observed(state):
        return observe(state, modulus, clock, masks)

    def replay(pair, sources):
        phase, bits = observed(pair[0])
        assert (phase, bits) == observed(pair[1])
        counts = [0, 0]
        for source in sources:
            for _ in range(2):  # Observe separately after each grain stabilizes.
                (a, fa), (b, fb) = (add_one(h, source, adjacent) for h in pair)
                pair = a, b
                counts[0] += fa
                counts[1] += fb
                phase = (phase + clock[source]) % modulus
                bits ^= masks[source]
                assert observed(a) == observed(b) == (phase, bits)
        return pair, counts

    # Abelianity allows any ordering of k left and k right double-grain steps.
    before_last, prefix = replay(initial, chain(repeat(left, k), repeat(right, k)))
    assert before_last == targets and prefix[0] == prefix[1]
    totals = []
    for source in (left, right):
        final, extra = replay(before_last, [source])
        assert all(burns(h, adjacent) for h in final)
        total = [a + b for a, b in zip(prefix, extra)]
        # Move the last step to the front. Both schedules must agree in final
        # states and cumulative firings, including when their last sides differ.
        reordered, reordered_total = replay(initial, chain([source], repeat(right, k), repeat(left, k)))
        assert reordered == final and reordered_total == total
        totals.append(total)
    low = prefix[0]
    high = low + n * n - 1
    assert totals == [[low, high], [high, low]]
    expected = {2: (158, 95, 158), 3: (1938, 1449, 2124)}
    if m in expected:
        assert (sum(first), low, high) == expected[m]
    return dict(m=m, side=n, steps=steps, initial_mass_each=sum(first),
                initial_clock_bits=observed(first), prefix_firings_each=low,
                last_left_totals=totals[0], last_right_totals=totals[1],
                firing_gap=high - low, probability_count_difference_one=2 * comb(steps, k) / 2**steps)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--m", type=int, nargs="+", default=[2, 3], help="levels m >= 2")
    levels = parser.parse_args().m
    if min(levels) < 2:
        parser.error("the two-hole construction requires m >= 2")
    print(json.dumps([verify(m) for m in levels], indent=2))
