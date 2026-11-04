/-!
# When F0 forgetting is already a complete predictive state

This bridge uses the exact descent condition from PR #7 and the canonical
future-observation equivalence from PR #9.  It assumes one fixed deterministic
update U.  No finiteness, probability, or invertibility is required.
-/

noncomputable section

namespace LinearInputF0FutureMinimality

open LinearInputF0
open LinearInputF0Descent
open LinearInputFutureObservation

/-- A fiber-respecting update cannot expose a distinction forgotten now. -/
theorem future_of_respects {α : Type*} {K U : α → α}
    (hU : RespectsFibers K U) {x y : α} (hxy : K x = K y) :
    FutureEq K U x y := by
  intro t
  induction t with
  | zero => simpa only [Function.iterate_zero, id_eq] using hxy
  | succ t ih =>
      simpa only [Function.iterate_succ_apply'] using hU _ _ ih

/-- Current observation equality already captures every future distinction
exactly when one update respects its fibers. -/
theorem respects_iff_future_eq {α : Type*} (K U : α → α) :
    RespectsFibers K U ↔
      ∀ x y, FutureEq K U x y ↔ K x = K y := by
  constructor
  · intro h x y
    constructor
    · intro hf
      simpa only [Function.iterate_zero, id_eq] using hf 0
    · exact future_of_respects h
  · intro h x y hxy
    have hf := (h x y).2 hxy
    simpa only [Function.iterate_one] using hf 1

/-- For an idempotent F0 map, descent is precisely completeness of the
current forgotten state as a deterministic predictive representation. -/
theorem descends_iff_future_eq {α : Type*} {K U : α → α}
    (hK : Idempotent K) :
    Descends K U ↔ ∀ x y, FutureEq K U x y ↔ K x = K y := by
  exact (descends_iff_respects hK).trans (respects_iff_future_eq K U)

/-- The canonical predictive quotient and the F0 observation have the same
kernel under descent; this is an equality of distinctions, not of types. -/
theorem encode_eq_iff_observation {α : Type*} {K U : α → α}
    (hK : Idempotent K) (hU : Descends K U) (x y : α) :
    encode K U x = encode K U y ↔ K x = K y := by
  exact (encode_iff_future x y).trans ((descends_iff_future_eq hK).1 hU x y)

/-- Every original state and its fixed F0 representative then have the
same entire future observation trace. -/
theorem representative_future_eq {α : Type*} {K U : α → α}
    (hK : Idempotent K) (hU : Descends K U) (x : α) :
    FutureEq K U (K x) x := by
  exact ((descends_iff_future_eq hK).1 hU (K x) x).2 (hK x)

/-- The concrete non-descending update from PR #7 separates states that
the current F0 observation merges, so time-zero compression is insufficient. -/
theorem example_current_equal_future_distinct :
    exampleK (0 : Fin 3) = exampleK (1 : Fin 3) ∧
    ¬ FutureEq exampleK exampleUpdate (0 : Fin 3) (1 : Fin 3) := by
  constructor
  · decide
  · intro hf
    have h1 := hf 1
    have hne : exampleK (exampleUpdate (0 : Fin 3)) ≠
        exampleK (exampleUpdate (1 : Fin 3)) := by decide
    exact hne (by simpa only [Function.iterate_one] using h1)

end LinearInputF0FutureMinimality
