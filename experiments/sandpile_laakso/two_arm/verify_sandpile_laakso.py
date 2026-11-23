"""Exact finite checks. Run with python -B verify_sandpile_laakso.py."""

import json
from collections import deque
from fractions import Fraction as F
from itertools import product


def thresholds(n):
    # Two edges per link. The sink is to the left of array index zero.
    return (4,) * (n - 1) + (2,)


def stabilize(state, source, grains=1):
    height = list(state)
    degree = thresholds(len(height))
    height[source] += grains
    pending = deque([source])
    odometer = [0] * len(height)
    while pending:
        i = pending.popleft()
        if height[i] < degree[i]:
            continue
        height[i] -= degree[i]
        odometer[i] += 1
        for neighbor in (i - 1, i + 1):
            if 0 <= neighbor < len(height):
                height[neighbor] += 2
                pending.append(neighbor)
        if height[i] >= degree[i]:
            pending.append(i)
    return tuple(height), tuple(odometer)


def check_closed_class(n, predicted):
    # Every stable state reaches the maximal stable state by filling each
    # site's deficit without toppling. Thus states reachable from that maximum
    # are precisely the unique closed communicating class.
    degree = thresholds(n)
    graph = {
        state: [stabilize(state, k)[0] for k in range(n)]
        for state in product(*(range(d) for d in degree))
    }
    maximum = tuple(d - 1 for d in degree)
    reached = {maximum}
    pending = [maximum]
    while pending:
        for child in graph[pending.pop()]:
            if child not in reached:
                reached.add(child)
                pending.append(child)
    assert reached == predicted
    return {"stable_states": len(graph), "recurrent_states": len(reached)}


def check_sandpile(n):
    predicted = set()
    baseline = tuple(d - 2 for d in thresholds(n))
    for bits in product(range(2), repeat=n):
        state = tuple(a + b for a, b in zip(baseline, bits))
        predicted.add(state)
        for k in range(n):
            final, odometer = stabilize(state, k)
            expected = list(state)
            expected[k] += 1 - 2 * bits[k]
            assert final == tuple(expected)
            assert odometer == tuple(bits[k] * min(i + 1, k + 1) for i in range(n))
        final, odometer = stabilize(state, n - 1, grains=2)
        assert final == state
        assert odometer == tuple(range(1, n + 1))
    row = {
        "n": n,
        "one_grain_state_source_pairs": n * len(predicted),
        "two_grains_at_tip_states": len(predicted),
    }
    if n <= 5:
        row["complete_stable_transition_graph"] = check_closed_class(n, predicted)
    return row


def integrate_quadratic(fn, a, b):
    # Simpson's identity is exact for every polynomial used on these pieces.
    return (b - a) * (fn(a) + 4 * fn((a + b) / 2) + fn(b)) / 6


def density(t):
    return 2 * abs(2 * t - 1)


def cumulative(t):
    z = 2 * t - 1
    return (1 + z * abs(z)) / 2


def check_bottleneck(eps):
    zero, half, one = F(0), F(1, 2), F(1)
    cuts = [zero, half - eps, half, half + eps, one]

    def ramp(t):
        return min(one, max(zero, (t - half + eps) / (2 * eps)))

    slab = gradient_integral = mean = oscillation = F(0)
    for a, b in zip(cuts, cuts[1:]):
        mass = integrate_quadratic(density, a, b)
        assert mass == cumulative(b) - cumulative(a)
        if half - eps < (a + b) / 2 < half + eps:
            slab += mass
            gradient_integral += mass / (2 * eps)
        mean += integrate_quadratic(lambda t: density(t) * ramp(t), a, b)
        oscillation += integrate_quadratic(lambda t: density(t) * abs(ramp(t) - half), a, b)
    assert mean == half
    assert slab == 4 * eps**2
    assert gradient_integral == 2 * eps
    assert oscillation == half - 2 * eps**2 / 3
    return {key: str(value) for key, value in (
        ("epsilon", eps), ("slab_mass", slab), ("mean", mean),
        ("gradient_integral", gradient_integral), ("mean_absolute_deviation", oscillation),
    )}


def main():
    sandpile = [check_sandpile(n) for n in range(1, 9)]
    report = {
        "sandpile": sandpile,
        "total_one_grain_state_source_pairs": sum(r["one_grain_state_source_pairs"] for r in sandpile),
        "total_two_grains_at_tip_states": sum(r["two_grains_at_tip_states"] for r in sandpile),
        "alpha_one_bottleneck_exact_integrals": [check_bottleneck(F(1, 2**p)) for p in range(1, 9)],
    }
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
