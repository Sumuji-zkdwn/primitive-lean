# Cross-system shortest distinguishing words: exact finite experiment

This is an extension of CrossSystemObservation.inc and does NOT establish
modularity of an elliptic curve or any infinite-state theorem.

tools/shortest_cross_trace.py accepts two complete deterministic machines, an
ordered common action alphabet, exact output values, one initial pair and
optionally a total candidate state map. Its breadth-first search of the
synchronous product returns either the shortest word whose final output
differs, or the entire reachable product relation. The latter is a concrete
cross-bisimulation: the current readouts agree and the relation is closed
under every common labelled action.

The shortest mismatching word has length at most |A|*|B|-1. A zero-length
word is allowed when the initial outputs already differ. An independent
verifier checks every shorter reachable output profile for counterexamples.
For successful equivalences it checks reachability, closure, and outputs.
Incomplete actions or invalid indices are rejected rather than counted as
successes.

When a candidate map is supplied, analyze_mapping distinguishes exact
state-map commutation from potentially weaker observational agreement from
every source state.

Examples:
- delayed_failure: start (0,0) agrees now and after toggle_hidden but differs
  after the two-word [toggle_hidden, reveal_hidden]. The shortest word is 2.
  Over all source states the shortest failure occurs from left state 1 after
  one reveal_hidden action.
- valid_forgetting: four-bit-pair states forget the hidden bit into two target
  states; flip_visible commutes with that map. The reachable product relation
  from start (0,0) is [(0,0),(2,1)] and no finite word distinguishes them.

Commands:
    python tools/shortest_cross_trace.py --demo delayed_failure
    python tools/shortest_cross_trace.py --demo valid_forgetting
    python tools/shortest_cross_trace.py --case sample.json --output report.json
    python -m unittest discover -s tests -p 'test_shortest_cross_trace.py' -v

JSON schema: {"actions":["x"], "left":{"outputs":[0],"transitions":{"x":[0]}},
"right":{"outputs":[0],"transitions":{"x":[0]}}, "initial":[0,0],
"mapping":[0]} . The mapping field is optional. State indices are zero-based.

tests/test_shortest_cross_trace.py has eight tests, including 16,384
initial-pair two-state/two-action cases compared against all words of length
0..3. Tests run under pytest in GitHub CI and under unittest discovery in
the full repository integration. The Lean statement
separating_word_refutes_trace merely turns a particular word mismatch
into ¬CrossTrace; the BFS algorithm itself is verified by Python testing,
not yet fully formalized in Lean. Operator discovery and automatic repair
are not implemented.
