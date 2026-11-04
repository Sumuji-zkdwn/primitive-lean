# Radical as a concrete arithmetic F0 (2026-11-05)

## Scope

This addition instantiates the existing `LinearInputF0` retraction,
`LinearInputF0Descent` update/fiber equivalence, and
`LinearInputF0FutureMinimality` predictive completeness criterion.

**Source:** `linear_input/lean_check/RadicalF0Bridge.inc`, namespace
`LinearInputRadicalF0`. It is appended as the final registered supplement;
no previously checked Lean proof fragment is changed.

For natural numbers, define
`radical(0) = 0` and, for `n != 0`,
`radical(n) = product(n.primeFactors)`.
The finite prime-support set discards repeated occurrences, not just order.

## Mathematical claims implemented

- `radical_primeFactors`: the support of a number is identical to the
  support of its radical, including at zero under this convention.
- `radical_idempotent`: `LinearInputF0.Idempotent radical`.
- `radical_kernel_iff`: for `x,y != 0`, equal radicals iff equal
  finite sets of distinct prime factors.
- `radical_squarefree` and `radical_fixed_iff_squarefree`: the
  nonzero fixed points are exactly the squarefree positive naturals.
- `two_four_same_radical` and `successors_distinguished`:
  `rad(2)=rad(4)=2` but `rad(3)=3 != 5=rad(5)`.
- `successor_not_fiber_respecting` and `successor_not_descending`:
  the update `Nat.succ` fails the exact existing F0 descent condition.
- `no_radical_successor_readout`: no map `g` on radical outputs
  alone can predict `radical(n+1)` from `radical(n)` for every `n`.
- `future_separates_two_four` and
  `radical_not_complete_predictive_state`: the two original states
  are currently identified but have unequal future observations.
  The last result explicitly applies the established future-completeness iff.

The mathematical dependencies `Nat.primeFactors_prod_primeFactors`,
`Nat.squarefree_prod_primeFactors` and
`Nat.prod_primeFactors_of_squarefree` come from the pinned Mathlib.
No new fundamental-theorem-of-arithmetic proof is claimed.

## Verification contract

Run the existing `python -B -X utf8 tools/verify.py --integration-only`,
which checks source hashes, registers every supplement, executes the
repository tests and invokes the full pinned Lean `--trust=0` source
and public-axiom audit. The new file is also covered by
`python -m unittest tests.test_radical_f0` or unittest discovery.

A source write and a mathematical argument do **not** count as
Lean verification until an exact-commit Actions job passes; record the
run and SHA once they are available.

## Nonclaims

This proves neither weak/strong abc, nor a numerical relation between
`a+b=c` and `rad(abc)`, nor any asymptotic number-theoretic estimate.
It does not identify the new multiplicity-forgetting radical F0 with
the prime-list **sorting** F0 of PR #54, which preserves multiplicity.
It also does not assert that all arithmetic operations fail descent:
the counterexample concerns successor specifically.
