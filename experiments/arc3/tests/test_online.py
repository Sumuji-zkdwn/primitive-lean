from online import InteractionModel


def test_alias_conflict_refines_history_and_replays_all_records():
    m = InteractionModel(max_depth=3)
    for first, result in [("a", 2), ("b", 3)]:
        m.start(0)
        m.update(first, 1)
        m.update("c", result)
    assert m.depth == 1
    assert len(m.records) == 4
    assert m.metrics()["unresolved_conflicts"] == 0
    assert m.edges[(m.state((0, ("a", 1)), 1), "c")].outcomes == {2: 1}
    assert m.edges[(m.state((0, ("b", 1)), 1), "c")].outcomes == {3: 1}


def test_identical_histories_with_different_outcomes_remain_unresolved():
    m = InteractionModel(max_depth=2)
    for outcome in (1, 2, 1):
        m.start(0)
        m.update("a", outcome)
    assert m.depth == 2
    assert len(m.records) == 3
    assert m.metrics()["unresolved_conflicts"] == 1
    assert next(iter(m.edges.values())).outcomes == {1: 2, 2: 1}


def test_episode_boundary_does_not_invent_a_transition():
    m = InteractionModel()
    m.start(0)
    m.update("a", 1)
    m.start(3)
    assert len(m.records) == 1
    assert m.state(m.history, 4) == (3, ())


def test_repeats_can_be_chosen_before_large_action_space_is_exhausted():
    m = InteractionModel(1)
    m.start(0)
    m.update("known", 0)
    actions = ("known",) + tuple(range(1000))
    choices = [m.choose(actions) for _ in range(100)]
    assert "known" in choices
    assert any(a != "known" for a in choices)


def test_arbitrary_bijective_token_renaming_preserves_choices_and_counts():
    old, new = InteractionModel(42), InteractionModel(42)
    obs = {i: object() for i in range(3)}
    acts = {a: object() for a in ("a", "b")}
    for _ in range(4):
        old.start(0)
        new.start(obs[0])
        for _ in range(8):
            a, b = old.choose(tuple(acts)), new.choose(tuple(acts.values()))
            assert acts[a] == b
            result = 1 if a == "a" else 2
            reward = float(a == "a")
            old.update(a, result, reward)
            new.update(b, obs[result], reward)
    assert old.metrics() == new.metrics()
