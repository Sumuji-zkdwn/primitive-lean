"""Wired square sandpile. Verify the harmonic clock, binary switches, and refinement.

All configurations have row-major indices; formulas and boundary labels use indices
starting at one. Every vertex has threshold four, including vertices next to the sink.
Run python -B square_clock.py to print a deterministic JSON report.
"""

from collections import Counter, deque
from itertools import product
from math import gcd
import json


def neighbors(n):
    return [
        [r * n + c for r, c in ((i - 1, j), (i + 1, j), (i, j - 1), (i, j + 1))
         if 0 <= r < n and 0 <= c < n]
        for i in range(n) for j in range(n)
    ]


def add_one(state, site, adjacent):
    h = list(state)
    h[site] += 1
    pending = deque([site])
    firings = 0
    while pending:
        x = pending.popleft()
        while h[x] >= 4:
            h[x] -= 4
            firings += 1
            for y in adjacent[x]:
                h[y] += 1
                if h[y] == 4:
                    pending.append(y)
    return tuple(h), firings


def burns(state, adjacent):
    unburnt = set(range(len(state)))
    while unburnt:
        burn = {x for x in unburnt if state[x] >= sum(y in unburnt for y in adjacent[x])}
        if not burn:
            return False
        unburnt -= burn
    return True


def switched_bit(j, modulus):
    period = modulus // gcd(j, modulus)
    level = 0
    while period % 3 == 0:
        period //= 3
        level += 1
    assert period == 1 and level >= 1
    return 1 << (level - 1)


def harmonic_masks(first_row):
    """Bit k of each site's mask is a harmonic test function modulo two."""
    n = len(first_row)
    previous, current = [0] * n, first_row
    masks = []
    for _ in range(n):
        masks.extend(current)
        padded = [0, *current, 0]
        following = [p ^ left ^ right for p, left, right in
                     zip(previous, padded, padded[2:])]
        previous, current = current, following
    assert not any(current), "far Dirichlet boundary must vanish"
    return masks


def instruments(m, *, full_basis=False):
    modulus = 3**m
    n = modulus - 1
    adjacent = neighbors(n)
    clock = [i * j for i in range(1, modulus) for j in range(1, modulus)]
    first_row = [switched_bit(j, modulus) for j in range(1, modulus)]
    masks = harmonic_masks(first_row)
    # Directly check the effect of firing ON EVERY VERTEX, sink edges included.
    for x, ys in enumerate(adjacent):
        assert (4 * clock[x] - sum(clock[y] for y in ys)) % modulus == 0
        residue = 0
        for y in ys:
            residue ^= masks[y]
        assert residue == 0
    if full_basis:
        independent = harmonic_masks([1 << j for j in range(n)])
        for ys in adjacent:
            residue = 0
            for y in ys:
                residue ^= independent[y]
            assert residue == 0
    return modulus, adjacent, clock, masks


def observe(state, modulus, clock, masks):
    phase = sum(a * b for a, b in zip(state, clock)) % modulus
    bits = 0
    for h, mask in zip(state, masks):
        if h % 2:
            bits ^= mask
    return phase, bits


def representatives(m, tools):
    modulus, adjacent, clock, masks = tools
    maximum = (3,) * len(clock)
    queue = deque([maximum])
    by_output = {observe(maximum, modulus, clock, masks): maximum}
    while queue:
        state = queue.popleft()
        for j in range(1, modulus):
            new, _ = add_one(state, j - 1, adjacent)
            output = observe(new, modulus, clock, masks)
            if output not in by_output:
                by_output[output] = new
                queue.append(new)
    assert len(by_output) == modulus * 2**m
    assert all(burns(s, adjacent) for s in by_output.values())
    return list(by_output.values())


def physical_return_test(m, tools):
    modulus, adjacent, clock, masks = tools
    n = modulus - 1
    if n == 2:
        states = [h for h in product(range(4), repeat=4) if burns(h, adjacent)]
        counts = Counter(observe(h, modulus, clock, masks) for h in states)
        assert len(states) == 192 and set(counts.values()) == {32}
        selection = "all recurrent states, selected by burning all 256 stable states"
    else:
        states = representatives(m, tools)
        selection = "one legally reached recurrent state per clock and binary output"
    steps = firings = returns = 0
    for h in states:
        original_phase, original_bits = observe(h, modulus, clock, masks)
        for j in range(1, modulus):
            period = modulus // gcd(j, modulus)
            current = h
            for k in range(1, period + 1):
                current, fired = add_one(current, j - 1, adjacent)
                phase, bits = observe(current, modulus, clock, masks)
                assert phase == (original_phase + k * j) % modulus
                assert bits == original_bits ^ (switched_bit(j, modulus) if k % 2 else 0)
                assert (phase == original_phase) == (k == period)
                steps += 1
                firings += fired
            assert current != h and bits != original_bits
            returns += 1
    return dict(side=n, selection=selection, states=len(states),
                local_first_returns=returns, single_grain_stabilizations=steps,
                legal_topplings_in_return_tests=firings)


def refinement(m):
    coarse = 3**m
    fine = 3 * coarse
    comparisons = 0
    for j in range(1, coarse):
        assert switched_bit(3 * j, fine) == switched_bit(j, coarse)
        assert fine // gcd(3 * j, fine) == coarse // gcd(j, coarse)
        for r in range(fine):
            assert ((r + 3 * j) % fine) // 3 == (r // 3 + j) % coarse
            comparisons += 1
    for j in range(1, fine):
        if j % 3:
            assert switched_bit(j, fine) == 1 << m
    return comparisons


def main():
    checks = []
    physical = []
    for m in range(1, 6):
        tools = instruments(m, full_basis=True)
        modulus = 3**m
        checks.append(dict(m=m, side=modulus - 1, sites=(modulus - 1)**2,
                           boundary_sources=modulus - 1,
                           periods=sorted({modulus // gcd(j, modulus) for j in range(1, modulus)})))
        if m <= 2:
            physical.append(physical_return_test(m, tools))
    print(json.dumps({
        "model": "nearest-neighbor square; every missing edge runs to a wired sink; top row drives",
        "algebra": checks, "physical": physical,
        "refinement_phase_source_checks": {f"{3**m}_to_{3**(m+1)}": refinement(m) for m in range(1, 5)},
        "scope": "algebra and legal firings are finite checks; the projection forgets microscopic states",
    }, indent=2))


if __name__ == "__main__":
    main()
