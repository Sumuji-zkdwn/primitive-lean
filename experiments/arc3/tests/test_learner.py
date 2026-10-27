from itertools import product

from core import Event, distinguishing_word
from experiments import primitive
from learner import Episode, synthesize


def episode(model, actions):
    state = "0"
    events = []
    for action in actions:
        step = model.edges[state, action]
        events.append((action, model.event(step)))
        state = step.target
    return Episode(model.view("0"), tuple(events))


def alphabet(data):
    return tuple(dict.fromkeys([e.initial for e in data] +
                              [event.view for e in data for _,event in e.events]))


def test_history_forces_extra_hidden_state_without_named_puzzle_primitives():
    actual = primitive(add_b=True)
    data = (episode(actual, ("A","B")), episode(actual, ("B",)))
    too_small = synthesize(data, alphabet(data), 2)
    assert too_small.complete_for_bound and not too_small.models
    expanded = synthesize(data, alphabet(data), 3)
    assert expanded.complete_for_bound and expanded.models
    assert expanded.minimum_consistent_states == 3
    assert any(distinguishing_word(m, "0", actual, "0") is None for m in expanded.models)


def test_further_interventions_resolve_all_surviving_candidate_behaviors():
    actual = primitive(add_b=True)
    data = tuple(episode(actual, word) for length in range(1,5)
                 for word in product(("A","B"), repeat=length))
    inferred = synthesize(data, alphabet(data), 3)
    assert inferred.complete_for_bound and inferred.models
    assert all(distinguishing_word(m,"0",actual,"0") is None for m in inferred.models)


def test_limited_search_is_explicitly_incomplete():
    actual = primitive(add_b=True)
    data = (episode(actual, ("A","B")), episode(actual, ("B",)))
    inferred = synthesize(data, alphabet(data), 3, max_tables=10)
    assert not inferred.complete_for_bound
    assert inferred.checked_tables == 10


def test_supplied_candidate_state_names_are_not_training_data():
    actual = primitive(add_b=True)
    data = (episode(actual, ("A","B")), episode(actual, ("B",)))
    # The learner receives only View, action, cost records; no Model or hidden state.
    assert all(isinstance(event, Event) for e in data for _,event in e.events)
    inferred = synthesize(data, alphabet(data), 3)
    assert all(m.name.startswith("inferred-") for m in inferred.models)
