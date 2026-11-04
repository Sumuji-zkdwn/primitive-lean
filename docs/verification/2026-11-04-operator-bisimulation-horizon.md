# Multi-action operator closure and finite horizon (2026-11-04)

## Architectural purpose

PR #55 proved that renaming or composing a fixed operator vocabulary
cannot reveal distinctions invisible to the original language. This
stacked research extension adds three independent Lean supplements:

1. `OperatorBisimulation.inc` — observational bisimulation, its greatest
   fixed relation given by finite-word equivalence, and closure under
   converse, intersection, union, relational composition, arbitrary
   indexed joins/intersections, state encodings, and invisible symmetries.
2. `OperatorVocabularyRefinement.inc` — necessary and sufficient
   conservativity criterion when independent new operators are added,
   finite mixed-language witnesses, and the canonical surjective
   map from extended predictive states onto old predictive states.
   The forgetful map is injective when no distinctions are gained;
   a concrete Fin 3 example witnesses non-injectivity otherwise.
3. `OperatorFiniteHorizon.inc` — horizon profiles for *all* finite
   operator words, refinement monotonicity and strict growth before
   completion, and the finite-state bound `N-r` for short separating
   words (N original states, r distinct current observations).

## The main statements

For an observable `K : α → ω` and a family of labelled endomorphisms
`step : ι → α → α`:

```
WordEq K step x y ↔
  ∃ R, Bisimulation K step R ∧ R x y
```

The observer's entire language kernel is the greatest compatible
bisimulation, without requiring the state space to be finite.

For additional operators `fresh : κ → α → α`, old-language equivalence
is preserved **exactly if** every fresh action respects the old
word-equivalence relation:

```
(∀ x y, WordEq K (sumStep old fresh) x y ↔ WordEq K old x y) ↔
  (∀ j x y, WordEq K old x y →
    WordEq K old (fresh j x) (fresh j y))
```

For finite `α`, define `N = Fintype.card α` and
`r = rank K step 0`. Then:

```
WordEq K step x y ↔
  HorizonEq K step (N-r) x y
```

Thus no two states require a separating word longer than `N-r`.

## Boundaries

- All transitions are deterministic and total. The action alphabet
  may be infinite, but `α` is finite for the horizon bound.
- `r` is the rank of initial observations, not the rank of a matrix.
- This formalizes observations, not physical measurements, complexity
  estimates for enumerating infinite alphabets, or automatic generation
  of genuinely new primitive operators.
- Existing Lean fragments, historical source hashes and the PR #55
  definitions remain unchanged.
- Every new theorem remains a *candidate* until compilation
  with pinned Lean/mathlib, all-declaration axiom audit and the exact
  source-commit CI pass.

## Checks

```sh
python -m pytest -q tests/test_operator_refinement.py
python -B -X utf8 tools/verify.py --integration-only
```

The Python suite exhaustively checks all 3-state, two-operator transition
systems with binary output and randomized 4–5 state systems. This is
supplemental finite evidence, not a substitute for the Lean proof.
