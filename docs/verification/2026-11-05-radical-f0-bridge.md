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
- `squarefree_fixed`: a nonzero squarefree natural is fixed by radical.
  The reverse implication is not formalized in this module.
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

The mathematical dependencies `Nat.primeFactors_prod` and
`Nat.prod_primeFactors_of_squarefree` come from the pinned Mathlib.
The additive assembly imports `Mathlib.Data.Nat.Squarefree` explicitly,
without changing the historical baseline checker or proof sources.
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

## 2026-11-19 addendum: the reverse implication

The reverse of `squarefree_fixed` is proved in the independent module
`lean/Research/RadicalSquarefree.lean` (12 theorems, imports only `Mathlib`), which copies
the definition of `radical` verbatim (the test `tests/test_radical_squarefree.py` checks the
byte-identical definition line in both files). It is not part of the joint checker and does
not change its declaration counts.

- `radical_eq_self_iff`: `radical n = n ↔ n = 0 ∨ Squarefree n`, so the fixed points of the
  radical are exactly `0` and the squarefree numbers (`squarefree_fixed` is the `←` direction
  for `n ≠ 0`).
- `radical_squarefree`, `range_radical`: `radical n` is squarefree for `n ≠ 0`, and the image
  of `radical` is `{0} ∪ {squarefree}` (equal to its fixed-point set).
- `squarefree_dvd_radical`, `radical_dvd`: for `n ≠ 0`, `radical n` divides `n` and every
  squarefree divisor of `n` divides `radical n` (greatest squarefree divisor).
- `radical_mul_of_coprime`: `radical (a * b) = radical a * radical b` for coprime nonzero
  `a, b`; `radical_examples` evaluates `rad 12 = 6`, `rad 30 = 30`, `rad 72 = 6`.

Verification (2026-11-19, Lean `v4.36.0-rc2`): `lake env lean --trust=0
Research/RadicalSquarefree.lean` passes without warnings; all 12 theorems use only `propext`,
`Classical.choice`, `Quot.sound`. The exhaustive census `python -B
tests/test_radical_squarefree.py` checks the fixed-point characterization for `n ≤ 20000`, the
greatest-squarefree-divisor property for `n ≤ 3000`, and multiplicativity for coprime
`a, b ≤ 300`. Dedicated CI: `.github/workflows/radical-squarefree.yml`; integration stage
`radical-squarefree` in `tools/pr_integration.py`.

GitHub Actions: [run 44598448690](https://github.com/Sumuji-zkdwn/primitive-lean/actions/runs/44598448690) (commit `6296a30`) completed with conclusion `success`.
