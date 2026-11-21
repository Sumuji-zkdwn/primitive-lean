"""Exact finite checks for CPR regeneration and a deterministic Moore sandpile.

Python 3.10+; standard library only. Run python3 verify_model.py for JSON.
The bit at x*side+y is one for an occupied cell. The default sweep visits
increasing x, then increasing y. A missing neighbor never wraps around.
"""

import json
from collections import defaultdict
from fractions import Fraction
from itertools import combinations


SCALE = 12_000  # 1/800, 1/500, and 1/300 are all integer multiples of 1/SCALE.
RULES = ("fixed8", "degree")


def check(condition, message):
    """Keep mathematical checks active in optimized Python, too."""
    if not condition:
        raise AssertionError(message)


class Board:
    def __init__(self, side):
        if side < 1:
            raise ValueError("side must be positive")
        self.side = side
        self.size = side * side
        self.sites = range(self.size)
        self.full = (1 << self.size) - 1
        self.neighbors = []
        for i in self.sites:
            x, y = divmod(i, side)
            self.neighbors.append(tuple(
                xx * side + yy
                for xx in range(max(0, x - 1), min(side, x + 2))
                for yy in range(max(0, y - 1), min(side, y + 2))
                if (xx, yy) != (x, y)
            ))
        self.masks = [sum(1 << j for j in nbr) for nbr in self.neighbors]
        self.edges = [(i, j) for i in self.sites for j in self.neighbors[i] if i < j]

    def units(self, rule):
        if rule == "fixed8":
            return [SCALE // 800] * self.size
        if rule == "degree":
            return [SCALE // (100 * len(nbr)) if nbr else 0 for nbr in self.neighbors]
        raise ValueError(rule)

    def count(self, state, site):
        return (state & self.masks[site]).bit_count()

    def sand(self, state):
        return tuple(0 if state & (1 << i) else self.count(state, i) for i in self.sites)

    def cut(self, state):
        return sum(((state >> i) ^ (state >> j)) & 1 for i, j in self.edges)

    def field(self, state, units):
        return tuple(w * n for w, n in zip(units, self.sand(state)))

    def probability_units(self, state, i, units):
        return 0 if state & (1 << i) else units[i] * self.count(state, i)


def harvest(state, site):
    return state & ~(1 << site)


def set_occupied(state, site):
    return state | (1 << site)


def sweep_sites(board, order):
    sites = tuple(order)
    if any(i not in board.sites for i in sites) or len(set(sites)) != len(sites):
        raise ValueError("a sweep visits distinct, in-board sites")
    return sites


def conditional_law(board, state, order, units, *, frozen=False):
    """Enumerate final-state weights for the indicated distinct single-site trials.

    Each trial has its stated Bernoulli probability conditional on the past.
    In frozen mode every probability is evaluated on the starting configuration.
    """
    order = sweep_sites(board, order)
    law = {state: 1}
    for i in order:
        after = defaultdict(int)
        for current, weight in law.items():
            p = board.probability_units(state if frozen else current, i, units)
            after[current] += weight * (SCALE - p)
            if p:
                after[set_occupied(current, i)] += weight * p
        law = dict(after)
    denominator = SCALE ** len(order)
    check(sum(law.values()) == denominator, 'trial probabilities do not sum to one')
    return law, denominator


def chance_occupied(law_denominator, i):
    law, denominator = law_denominator
    return Fraction(sum(w for s, w in law.items() if s & (1 << i)), denominator)


def expected_births(board, state, order, units):
    """Exact birth marginal at each site in one sweep with no harvest inside it."""
    marginals = [Fraction(0)] * board.size
    for i in sweep_sites(board, order):
        if state & (1 << i):
            continue
        earlier_births = sum(marginals[j] for j in board.neighbors[i])
        marginals[i] = Fraction(units[i], SCALE) * (board.count(state, i) + earlier_births)
    return marginals


def verify_cuts_and_flips(side):
    """Exhaust all configurations, both weighted cuts, and every single-site flip."""
    board = Board(side)
    configs = 1 << board.size
    units = board.units("degree")
    uniform = []
    weighted = []
    for state in range(configs):
        sand = board.sand(state)
        cut = board.cut(state)
        check(sum(sand) == cut, 'local weights and undirected cut differ')
        check((cut == 0) == (state in (0, board.full)),
              'a nonconstant configuration has zero cut or a constant configuration has nonzero cut')
        edge_sum = sum(
            units[j] if state & (1 << i) else units[i]
            for i, j in board.edges if ((state >> i) ^ (state >> j)) & 1
        )
        check(sum(s * w for s, w in zip(sand, units)) == edge_sum,
              'weighted boundary sum differs from the field sum')
        uniform.append(cut)
        weighted.append(edge_sum)
    for state in range(configs):
        for i in board.sites:
            bit = 1 << i
            after = state ^ bit
            sign = -1 if state & bit else 1
            n = board.count(state, i)
            nbr = board.neighbors[i]
            check(uniform[after] - uniform[state] == sign * (len(nbr) - 2 * n),
                  'incorrect fixed-denominator change after a flip')
            empty_weights = sum(units[j] for j in nbr if not state & (1 << j))
            check(weighted[after] - weighted[state] == sign * (empty_weights - units[i] * n),
                  'incorrect degree-weighted change after a flip')
    return {"boards": configs, "flips_per_rule": configs * board.size}


def verify_local_fields(side):
    """Exhaust each closed Moore neighborhood; a fixed background is held outside it."""
    board = Board(side)
    background = sum(1 << i for i in board.sites if sum(divmod(i, side)) % 2)
    tested = 0
    for i in board.sites:
        bit = 1 << i
        nbr = board.neighbors[i]
        other = background & ~(bit | board.masks[i])
        for pattern in range(1 << len(nbr)):
            occupied = [j for k, j in enumerate(nbr) if pattern & (1 << k)]
            empty_center = other | sum(1 << j for j in occupied)
            occupied_center = empty_center | bit
            before, after = board.sand(empty_center), board.sand(occupied_center)
            predicted = list(before)
            predicted[i] -= len(occupied)
            for j in nbr:
                predicted[j] += int(not (empty_center & (1 << j)))
            check(tuple(predicted) == after, 'local update disagrees with the recomputed field')
            # Comparing both full fields also checks the reverse (harvest) update.
            tested += 2
    return {"directed_local_flips": tested}


def verify_order(side, rule):
    board = Board(side)
    units = board.units(rule)
    pairs = list(combinations(board.sites, 2))
    changed = 0
    count_changed = 0
    min_tokens = None
    for state in range(1 << board.size):
        for i, j in pairs:
            first, denom = conditional_law(board, state, (i, j), units)
            second, _ = conditional_law(board, state, (j, i), units)
            both_empty = not state & ((1 << i) | (1 << j))
            adjacent = j in board.neighbors[i]
            ci, cj = board.count(state, i), board.count(state, j)
            differs = first != second
            check(differs == bool(both_empty and adjacent and (ci or cj)),
                  'order criterion disagrees with the joint law')
            if differs:
                changed += 1
                tokens = state.bit_count()
                min_tokens = tokens if min_tokens is None else min(min_tokens, tokens)
            contrast = sum(s.bit_count() * w for s, w in first.items())
            contrast -= sum(s.bit_count() * w for s, w in second.items())
            expected = units[i] * units[j] * (ci - cj) if both_empty and adjacent else 0
            check(denom == SCALE**2 and contrast == expected,
                  'two-trial expected-count contrast differs from the local formula')
            count_changed += int(contrast != 0)
    return {"board_pair_comparisons": (1 << board.size) * len(pairs),
            "different_final_law": changed, "different_expected_count": count_changed,
            "minimum_initial_tokens_for_different_law": min_tokens}


def verify_full_sweeps():
    """Check every birth marginal against exact joint laws on all 3x3 states."""
    board = Board(3)
    results = {}
    for rule in RULES:
        units = board.units(rule)
        changed = 0
        for state in range(1 << board.size):
            totals = []
            for order in (tuple(board.sites), tuple(reversed(board.sites))):
                b = expected_births(board, state, order, units)
                law = conditional_law(board, state, order, units)
                for i in board.sites:
                    old = int(bool(state & (1 << i)))
                    check(b[i] == chance_occupied(law, i) - old, 'sweep recurrence and the joint law differ')
                    check(b[i] >= Fraction(board.probability_units(state, i, units), SCALE),
                          'sequential marginal below the frozen marginal')
                totals.append(sum(b))
            changed += int(totals[0] != totals[1])
            frozen = conditional_law(board, state, board.sites, units, frozen=True)
            check(frozen == conditional_law(board, state, reversed(board.sites), units, frozen=True),
                  'frozen trials depend on enumeration order')
            mean = sum((s.bit_count() - state.bit_count()) * w for s, w in frozen[0].items())
            check(Fraction(mean, frozen[1]) == Fraction(sum(board.field(state, units)), SCALE),
                  'incorrect frozen expectation')
        results[rule] = {"initial_boards": 512, "sequential_joint_laws": 1024,
                         "forward_reverse_different_expected_total": changed}
    return results


def verify_absorption(side):
    board = Board(side)
    for rule in RULES:
        units = board.units(rule)
        for order in (tuple(board.sites), tuple(reversed(board.sites))):
            law, denom = conditional_law(board, 0, order, units)
            check(law == {0: denom}, 'empty board admits regeneration')
            check(conditional_law(board, 0, order, units, frozen=True) == (law, denom),
                  'frozen empty board admits regeneration')
            check(all(harvest(0, i) == 0 for i in board.sites), 'harvest changed an empty board')
    return True


def order_witnesses():
    board = Board(3)
    a, b, c = 3, 4, 5  # (1,0), (1,1), (1,2) in x-major coordinates.
    state = 1 << a
    result = {}
    for rule in RULES:
        units = board.units(rule)
        bc = conditional_law(board, state, (b, c), units)
        cb = conditional_law(board, state, (c, b), units)
        p_bc, p_cb = chance_occupied(bc, c), chance_occupied(cb, c)
        check(p_bc == Fraction(units[b] * units[c], SCALE**2) and p_cb == 0,
              'three-cell birth-order probabilities differ')
        birth_first = conditional_law(board, state, (b,), units)
        after_harvest = {harvest(s, a): w for s, w in birth_first[0].items()}
        harvest_first = conditional_law(board, harvest(state, a), (b,), units)
        p_hb = chance_occupied(harvest_first, b)
        p_bh = chance_occupied((after_harvest, birth_first[1]), b)
        check(p_hb == 0 and p_bh == Fraction(units[b], SCALE), 'two-cell harvest-order probabilities differ')
        result[rule] = {"P_c_b_then_c": str(p_bc), "P_c_c_then_b": str(p_cb),
                        "P_b_harvest_then_trial": str(p_hb), "P_b_trial_then_harvest": str(p_bh)}
    small = Board(2)
    units = small.units("fixed8")
    first = chance_occupied(conditional_law(small, 1, (1, 2), units), 2)
    last = chance_occupied(conditional_law(small, 1, (2, 1), units), 2)
    check((first, last) == (Fraction(801, 640000), Fraction(1, 800)), 'two-by-two marginal witness differs')
    result["2x2_fixed8_triangle"] = {"P_second_target_if_visited_last": str(first),
                                     "P_second_target_if_visited_first": str(last)}
    return result


def example_boards():
    board = Board(7)
    v = 3 * 7 + 3
    seed = 1 << v
    pair = seed | (1 << (v + 1))
    ring = board.masks[v]
    cases = {"one_center": seed, "adjacent_pair": pair, "eight_neighbor_ring": ring,
             "closed_ring_center_occupied": ring | seed, "empty": 0}
    result = {}
    for key, state in cases.items():
        result[key] = {}
        for rule in RULES:
            units = board.units(rule)
            frozen = Fraction(sum(board.field(state, units)), SCALE)
            sequential = sum(expected_births(board, state, board.sites, units), Fraction(0))
            result[key][rule] = {"frozen_expected_births": str(frozen),
                                 "sweep_expected_births": str(sequential),
                                 "sweep_rounded": round(float(sequential), 12)}
    check(result["one_center"]["fixed8"]["frozen_expected_births"] == "1/100", 'isolated seed expectation differs')
    check(result["adjacent_pair"]["fixed8"]["frozen_expected_births"] == "7/400",
          'adjacent-pair expectation differs')
    for name, state, expected in (("isolated", seed, -8), ("pair", pair, -6),
                                  ("surrounded", ring | seed, 8)):
        before = board.sand(state)
        after = board.sand(state & ~seed)
        change = [right - left for left, right in zip(before, after)]
        check(sum(change) == expected, 'central harvest cut difference differs')
        result["harvest_" + name] = {"sand_gained_at_center": change[v],
                                      "neighbor_sites_losing_one": change.count(-1),
                                      "change_in_cut": sum(change)}
    return result


def boundary_and_conservation_witnesses():
    board = Board(3)
    corner, edge, center = 0, 1, 4
    pair = (1 << corner) | (1 << edge)
    full_except_center = harvest(board.full, center)
    result = {}
    for rule in RULES:
        units = board.units(rule)

        def total(state):
            return Fraction(sum(board.field(state, units)), SCALE)

        corner_change = total(harvest(pair, corner)) - total(pair)
        law, denom = conditional_law(board, full_except_center, board.sites, units)
        after = sum(weight * total(s) for s, weight in law.items()) / denom
        check(total(0) == total(board.full) == 0, 'empty or full board has positive mass')
        check(total(harvest(board.full, center)) == Fraction(1, 100), 'incorrect single-hole initial mass')
        check(after == Fraction(99, 10000), 'incorrect single-hole next expected mass')
        result[rule] = {"corner_harvest_change": str(corner_change),
                        "one_hole_initial_potential": str(total(full_except_center)),
                        "one_hole_next_expected_potential": str(after)}
    check(result["fixed8"]["corner_harvest_change"] == "-1/800", 'fixed-denominator corner contrast differs')
    check(result["degree"]["corner_harvest_change"] == "1/12000", 'degree-weighted corner contrast differs')
    return result


def stabilize(board, state, reverse):
    height = state.copy()
    topplings = [0] * board.size
    sink = 0
    order = list(reversed(board.sites)) if reverse else list(board.sites)
    while True:
        i = next((k for k in order if height[k] >= 8), None)
        if i is None:
            break
        height[i] -= 8
        for j in board.neighbors[i]:
            height[j] += 1
        sink += 8 - len(board.neighbors[i])
        topplings[i] += 1
    check(sum(height) + sink == sum(state), 'board and sink grain count changed')
    check(all(0 <= h < 8 for h in height), 'final sandpile is unstable')
    return height, topplings, sink


def verify_sandpile(side):
    board = Board(side)
    center = (side // 2) * side + side // 2
    start = [0] * board.size
    start[center], start[center + 1], start[0] = 128, 64, 16
    forward = stabilize(board, start, reverse=False)
    backward = stabilize(board, start, reverse=True)
    check(forward == backward, 'sandpile stabilization or site toppling counts depend on order')
    height, odometer, sink = forward
    return {"initial_grains": sum(start), "final_grains": sum(height),
            "grains_at_sink": sink, "topplings": sum(odometer),
            "final_state_and_site_toppling_counts_agree": True}


def main():
    return {
        "units_per_probability_one": SCALE,
        "complete_configuration_checks": {s: verify_cuts_and_flips(s) for s in (3, 4)},
        "local_neighborhood_checks": {s: verify_local_fields(s) for s in range(3, 8)},
        "order_checks": {s: {r: verify_order(s, r) for r in RULES} for s in (1, 2, 3)},
        "full_sweep_checks_3x3": verify_full_sweeps(),
        "zero_absorbing": {s: verify_absorption(s) for s in range(3, 8)},
        "order_witnesses": order_witnesses(),
        "examples_7x7": example_boards(),
        "boundary_and_conservation_3x3": boundary_and_conservation_witnesses(),
        "deterministic_sandpile": {s: verify_sandpile(s) for s in range(3, 8)},
    }


if __name__ == "__main__":
    print(json.dumps(main(), indent=2))
