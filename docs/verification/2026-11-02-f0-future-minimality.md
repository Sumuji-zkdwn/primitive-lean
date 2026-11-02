# F0 descent and complete predictive states

This additive integration joins the definitions already supplied by PR #7
(`LinearInputF0Descent`) and PR #9 (`LinearInputFutureObservation`). The original
proof modules and their assumptions are preserved.

For a fixed deterministic update `U : α → α` and observation `K : α → α`,
`RespectsFibers K U` is equivalent to

```text
∀ x y, FutureEq K U x y ↔ K x = K y.
```

Under `LinearInputF0.Idempotent K`, the same condition is equivalent to
`Descends K U`. Thus an idempotent forgotten state already contains every
future-observable distinction exactly when the update descends through it.
This is a general arbitrary-type theorem, with no finiteness or probability
assumption. It concerns one fixed deterministic update, not adaptive observers
or nonstationary transition laws.

`linear_input/lean_check/F0FutureMinimality.inc` provides six named theorems:

| Declaration | Claim |
|---|---|
| `future_of_respects` | Fiber-respecting updates preserve observation equality at every future time. |
| `respects_iff_future_eq` | One-step fiber invariance iff present and future observation kernels coincide. |
| `descends_iff_future_eq` | F0 descent iff the same kernel equality, assuming idempotence. |
| `encode_eq_iff_observation` | The canonical predictive quotient and F0 observation identify exactly the same pairs. |
| `representative_future_eq` | An original state and its F0 representative have the same future trace. |
| `example_current_equal_future_distinct` | The existing three-state counterexample merges states now that the next observation separates. |

The quotient and the observation are not asserted to have the same type.
The kernel equivalence is the precise shared statement. The finite checker
`tools/check_f0_future_minimality.py` exhausts all idempotent maps and all updates
on one through four states; it also rechecks the concrete separating witness.

This document describes the mathematical scope. The integrated proof result
and its exact commit belong to the final integration verification record.
