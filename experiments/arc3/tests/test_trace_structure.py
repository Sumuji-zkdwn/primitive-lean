from trace_structure import Record, TraceEvidence


def test_same_current_observation_separated_by_continuation():
    t = TraceEvidence()
    t.add(Record("h", ("a", "b"), (0, 0, 1)))
    t.add(Record("k", ("a", "b"), (0, 0, 2)))
    r = t.compare("h", "k")
    assert r.status == "different_samples"
    assert set(r.witnesses) == {(("a", "b"), (0, 0, 1), (0, 0, 2))}


def test_bijective_renaming_preserves_all_shortest_witnesses():
    # Rename both actions and observations into non-orderable opaque objects.
    actions = {"a": object(), "b": object()}
    observations = {i: object() for i in range(3)}
    contexts = {"h": object(), "k": object()}
    old, new = TraceEvidence(), TraceEvidence()
    records = [Record(c, (a,), (0, o)) for c, o in [("h", 1), ("k", 2)]
               for a in actions]
    for r in records:
        old.add(r)
        new.add(Record(contexts[r.context], tuple(actions[a] for a in r.actions),
                       tuple(observations[o] for o in r.observations)))
    expected = {(tuple(actions[a] for a in w),
                 tuple(observations[o] for o in x),
                 tuple(observations[o] for o in y))
                for w, x, y in old.compare("h", "k").witnesses}
    result = new.compare(contexts["h"], contexts["k"])
    assert result.status == old.compare("h", "k").status
    assert set(result.witnesses) == expected
    assert len(expected) == 2


def test_finite_agreement_does_not_prove_equivalence():
    t = TraceEvidence()
    for c in ("h", "k"):
        t.add(Record(c, ("a",), (0, 0)))
    assert t.compare("h", "k").status == "no_difference_observed"
    t.add(Record("h", ("a", "b"), (0, 0, 1)))
    t.add(Record("k", ("a", "b"), (0, 0, 2)))
    assert t.compare("h", "k").status == "different_samples"
    assert t.compare("h", "unrecorded").status == "untested"


def test_conflicting_repeats_and_counts_survive():
    t = TraceEvidence()
    for o in (1, 2, 1):
        t.add(Record("h", ("a",), (0, o)))
    assert len(t.records) == 3
    assert t.outcomes("h", ("a",)) == {(0, 1), (0, 2)}
    assert t.conflicting_words("h") == {("a",)}


def test_intermediate_difference_survives_same_final_observation():
    t = TraceEvidence()
    t.add(Record("h", ("a", "b"), (0, 1, 0)))
    t.add(Record("k", ("a", "b"), (0, 2, 0)))
    assert set(t.compare("h", "k").witnesses) == {(("a",), (0, 1), (0, 2))}
