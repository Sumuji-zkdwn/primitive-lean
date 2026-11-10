# Observer-relative orientation depth: a finite operational bridge

Date: 2026-11-11 JST. Additive source:
`linear_input/lean_check/OperatorOrientationDepth.inc`.
No changes to existing theorem statements, baseline proofs, or the default branch.

## Mathematical object

Use the existing `LinearInputOperatorWords.run` for total deterministic
primitive operations `step : ι → α → α` and fixed observation
`K : α → ω`. An observer has an allowed alphabet `A : Set ι`.
A word `w` is allowed when all its letters lie in `A`.

Two states `x,y` are distinguishable at horizon `n` when:

```text
SeparatedWithin K step A x y n
  iff exists w, (all letters of w lie in A)
     and length(w) <= n
     and K(run step w x) != K(run step w y).
```

`EverSeparated` is existence at some finite horizon. For any pair
satisfying it, `leastDepth` uses `Nat.find` to select the least such
horizon. Do **not** assign a numerical depth to an inseparable pair;
informally its depth is infinity.

## Lean claims

1. If `A ⊆ B`, then a bounded separator allowed by `A` remains a
   separator allowed by `B` (`separatedWithin_mono`).
2. If `A ⊆ B`, then `ObservationalEq B x y` implies
   `ObservationalEq A x y` (`observationalEq_antitone`).
3. Finite separation is precisely the failure of allowed-word observational
   equivalence (`everSeparated_iff_not_observationalEq`). With all actions
   allowed, the relation agrees with the existing `WordEq`.
4. Whenever a pair is separable with `A`, its least separating length with
   `B` is no larger (`leastDepth_antitone`). This is conditional;
   `A` can be inseparable while `B` separates the same pair.
5. The retained `Fin 3` machine from `OperatorWordObservations.inc`
   demonstrates precisely this possibility: action `false` acts as the
   identity, states 0 and 1 have the same present readout, but action
   `true` reveals the difference in exactly one step.
6. If a residue `R` is invariant under a supplied reversal `T`, any
   integer-valued sign dependent only on `R` that must flip under `T`
   vanishes identically (`invariant_residue_forces_zero_orientation`).

All results are conditional on fixed transition functions, readouts, and
operation semantics. The last sign lemma does not assume that every
history admits a canonical reversal: the reversal is supplied.

## Independent exhaustive checks

`python -m unittest tests.test_operator_orientation_depth -v` or run the
file directly. The exact three-state enumeration covers 2 primitive actions,
2-valued observations, and all unordered pairs of the 3 states, comparing
all nested alphabet pairs (157,464 comparisons). A four-state counterexample
shows that a *compiled macro* can change the numeric depth from 2 to 1
without changing the predictive indistinguishability relation.

This difference matters: shortest *named-word length* is not intrinsic
physical elapsed time. Neither computation proves a social or physical
temporal direction or establishes arbitrary asynchronous CA semantics.

## Reuse and boundaries

- Existing `OperatorWordObservations.inc`: action-word semantics and
  predictive kernel.
- Existing `OperatorVocabularyRefinement.inc`: extension conservativity
  and strict quotient splitting (already proved, not claimed as novel here).
- Existing `OperatorFiniteHorizon.inc`: finite-state global upper bound
  for distinguishing words; a separate result from subset monotonicity.
- Existing `CurveWordBVOrientation.inc`: behavior of path signatures
  under oriented reparametrizations; not an identification of the social
  observer relation with geometric path reversal.

The new mathematical content is a **vocabulary-relative shortest-depth
criterion** and a small direction-label obstruction. It does not endogenize
the selection of a narrative, supply a partial-order model of asynchronous
updating, or turn an operator-symbol count into a clock.

## Verification

Proofs must be checked on the exact PR head by the repository's pinned
`python -B -X utf8 tools/verify.py --integration-only` run, including
`--trust=0` Lean kernel compilation, all-declaration axiom audits, and
the independent finite tests. Before a successful exact-head CI, these
proofs remain candidates.
