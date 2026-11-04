# Operator-word observation and vocabulary closure (2026-11-04)

## Scope

The research branch contains a new additive supplement:
`linear_input/lean_check/OperatorWordObservations.inc`.
It studies arbitrary finite sequences of named, deterministic operations
`step : ι → α → α`, rather than only the iterates of a single operation.

Given a readout `K : α → ω`, define observational equivalence

```
WordEq K step x y :=
  ∀ word : List ι, K (run step word x) = K (run step word y).
```

This is a Setoid. The quotient has well-defined readouts and transitions;
an exact state representation cannot merge states with different word
traces. Paired observers intersect observation kernels.

## No-new-distinction theorem

For a code dictionary `code : κ → List ι`, define
`generated step code j = run step (code j)`. Then

```
WordEq K step x y →
  WordEq K (generated step code) x y.
```

The proof compiles every new word to a concatenated old word, showing
equality of their actions on every state. If every old letter is included
as a singleton code word, the two observational equivalence relations
coincide exactly.

This shows a limitation of syntactic composition, **not** an impossibility
result about genuinely new primitives, state enrichment, measurement
changes, or arbitrary programs.

A `Fin 3` example has a readout that identifies states 0 and 1.
The old identity-only language never separates them. An independent
action sending state 1 to state 2 does, proving a strict refinement.

## Verification boundaries

This source contributes **28 candidate theorems and 13 definitions or
abbreviations**. Counts here describe added source declarations, not
successful Lean verification.

The registered verification target is:

```sh
python -B -X utf8 tools/verify.py --integration-only
```

Required before claiming verification: pinned Lean/mathlib compilation,
all new declaration axiom audits, manifest/source audit, Python regression
tests, and a successful CI run bound to the exact source commit.

The original 2026-11-02 integrated proof files are not modified.
