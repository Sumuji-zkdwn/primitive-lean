# Future-observation minimal states — Lean formalization

Date: 2026-11-01. Base: active PR #3 `codex/primitive-history-derivation-20261029`.

## Definitions and assumptions

Let `K : α → ω` be a deterministic observation and `U : α → α`
a deterministic update. No finiteness or `K² = K` assumption is required
for the universal minimal-state construction.

Define
```text
FutureEq K U x y  ↔  ∀ t : ℕ, K (U^[t] x) = K (U^[t] y)
State K U        :=  Quotient (futureSetoid K U)
```

`FutureObservations.inc` proves:

- `FutureEq` is an equivalence relation and is forward invariant under `U`.
- `encode`, `readout`, `transition`: a canonical minimal deterministic
  machine, with exact output and exact descended transitions.
- `encode_iff_future`: compression is exactly future indistinguishability.
- `representation_iterate` and `predictive_kernel_sub`:
  any other exact predictive representation `f` respecting observation
  (`out(f x)=K x`) and update (`f(U x)=V(f x)`) cannot identify states
  that differ at any future observation.
- `predictive_minimal`, `factor`, `factor_encode`,
  `factor_surjective`: the canonical machine is a surjective quotient
  of any other *surjective* predictive representation.
- `commute_iterates`, `invisible_symmetry`: a symmetry commuting with
  `U` and invisible under `K` is also invisible to this minimal machine.

This is a deterministic automata / observable-state construction, not a
new statement about polynomial maps, Rule 481 counting, or square packing.

## Finite-state refinement: added formalization

Define finite-horizon equivalence
```text
x ≈ₜ y ↔ ∀ j ≤ t, K (U^[j] x) = K (U^[j] y)
```
and let `N = |α|`, `r = |range K|`. The desired finite-state
strengthening is:

```text
x ≈_(N-r) y ↔ FutureEq K U x y.
```

The added `FutureFiniteHorizon.inc` states and proves this bound by counting
distinct finite observation profiles. This proof requires finite α, a fixed
update U, and a fixed observer K; no new inputs are introduced after time zero.
The bound is not counted as verified until its exact commit passes Lean CI.

## Verification

Both new source files are registered in `tools/verify_main_result.py` and `tools/verify.py`.
The independent `tools/check_future_observation.py` enumerates all deterministic
pairs of update/observation maps on up to four labelled states (65,536
models at N=4) to test the finite cutoff.
Full integrated verification entry point:

```sh
python -B -X utf8 tools/verify.py --proof-only
```

This performs `lake env lean --trust=0`, checks the entire assembled
declaration inventory, and forbids `sorry`, unexpected axioms, or warnings.
GitHub Actions results and exact commit SHA are recorded in the PR discussion.

## Outstanding connections

The original F0 retraction, Rule 481 mirror updates, the square-folding
history, Hanna generating functions, and GPU-observation control models
can each be instantiated only after providing actual `K` and `U`
with the required proof obligations. Their equivalence or optimality is
not asserted here.
