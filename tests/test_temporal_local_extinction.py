"""Independent finite model checking of temporal local-operation extinction.

The test oracle enumerates actual transition functions and injection maps.
It is not a substitute for the pinned Lean proof and axiom audit.
"""
from itertools import product


def first_enabled(locals_, is_enabled):
    return next((loc for loc in locals_ if is_enabled(loc)), None)


def successor(locals_, enabled, actions):
    def step(x):
        loc = first_enabled(locals_, lambda y: enabled(y, x))
        return x if loc is None else actions[loc][x]
    return tuple(step(x) for x in range(len(actions[0])))


def embeddings(obs_old, step_old, obs_new, step_new, dynamics=True):
    for f in product(range(len(obs_new)), repeat=len(obs_old)):
        if len(set(f)) != len(f):
            continue
        if any(obs_new[f[x]] != obs_old[x] for x in range(len(f))):
            continue
        if dynamics and any(f[step_old[x]] != step_new[f[x]]
                            for x in range(len(f))):
            continue
        yield f


def test_all_binary_local_action_libraries_have_sharp_extinction_boundary():
    actions = tuple(product(range(2), repeat=2))
    constant_observation = (0, 0)
    later_disabled = lambda loc, x: False

    for a, b in product(actions, repeat=2):
        pair = (a, b)
        for mask in range(16):
            old_enabled = lambda loc, x: bool(mask & (1 << (2 * loc + x)))
            old = successor((0, 1), old_enabled, pair)
            later = successor((0, 1), later_disabled, pair)
            assert later == (0, 1)

            possible = bool(tuple(embeddings(
                constant_observation, old, constant_observation, later)))
            expected = old == (0, 1)
            assert possible == expected


def test_no_action_rewrite_works_while_later_domains_remain_empty():
    flip = (1, 0)
    old = successor((0, 1), lambda loc, x: loc == 0, (flip, flip))
    obs = (0, 0)
    assert old == flip
    for a, b in product(tuple(product(range(2), repeat=2)), repeat=2):
        later = successor((0, 1), lambda loc, x: False, (a, b))
        assert later == (0, 1)
        assert not tuple(embeddings(obs, old, obs, later))


def test_local_replacement_survives_and_total_extinction_breaks_history():
    flip = (1, 0)
    def enabled(t, loc, x):
        return (t == 0 and loc == 0) or (t == 1 and loc == 1)

    transitions = tuple(
        successor((0, 1), lambda loc, x, t=t: enabled(t, loc, x),
                  (flip, flip)) for t in range(6))
    assert transitions[0] == flip
    assert transitions[1] == flip
    assert transitions[2:] == ((0, 1),) * 4

    obs = (0, 0)
    assert tuple(embeddings(obs, transitions[0], obs, transitions[1]))
    for t in range(2, 6):
        assert not tuple(embeddings(obs, transitions[0], obs, transitions[t]))
        assert tuple(embeddings(obs, transitions[0],
                                obs, transitions[t], dynamics=False))


def test_domain_reactivation_is_a_genuine_escape_from_no_rewrite_theorem():
    flip = (1, 0)
    old = successor((0, 1), lambda loc, x: loc == 0, (flip, flip))
    reactivated = successor((0, 1), lambda loc, x: loc == 0, (flip, flip))
    assert tuple(embeddings((0, 0), old, (0, 0), reactivated))


def test_endpoint_restoration_does_not_repair_broken_interval():
    flip = (1, 0)

    def enabled(t, loc, state):
        return (t == 0 and loc == 0) or (t == 1 and loc == 1) or (
            t == 3 and loc == 0)

    transitions = tuple(
        successor((0, 1), lambda loc, state, t=t: enabled(t, loc, state),
                  (flip, flip)) for t in range(4))
    assert transitions == (flip, flip, (0, 1), flip)
    obs = (0, 0)

    # The same operation is available at both endpoints.
    assert tuple(embeddings(obs, transitions[0], obs, transitions[3]))
    # But there is a genuine failure of historical simulation inside.
    assert not tuple(embeddings(obs, transitions[0], obs, transitions[2]))
    assert not all(tuple(embeddings(obs, transitions[0], obs, step))
                   for step in transitions)
