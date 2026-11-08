/-!
# F0 forgetting and the semantic closure of operators

This module connects the old deterministic F0 descent criterion with
the newer observational program semantics. A finite-word observational
kernel is present-time-complete whenever every primitive action respects
the observer's fibers.

Under that explicit hypothesis, a new operator is semantically compatible
if and only if it respects the same observer fibers. For idempotent F0
readouts the latter is precisely the established F0 descent equation.

This is a bridge of real definitions, not an asserted analogy between
distinct theories. No finite-state assumption is needed.
-/

noncomputable section

namespace LinearInputOperatorF0Bridge

open LinearInputOperatorWords
open LinearInputOperatorSemanticClosure
open LinearInputF0
open LinearInputF0Descent

/-- A state transformer respects the immediate readout fibers. -/
def FiberStable {α ω : Type*}
    (K : α → ω) (T : α → α) : Prop :=
  ∀ x y, K x = K y → K (T x) = K (T y)

theorem fiber_stable_id {α ω : Type*} (K : α → ω) :
    FiberStable K (fun x => x) := by
  intro x y h
  exact h

theorem fiber_stable_constant {α ω : Type*}
    (K : α → ω) (c : α) :
    FiberStable K (fun _ => c) := by
  intro x y h
  rfl

theorem fiber_stable_comp {α ω : Type*}
    (K : α → ω) (T S : α → α)
    (hT : FiberStable K T) (hS : FiberStable K S) :
    FiberStable K (fun x => S (T x)) := by
  intro x y h
  exact hS _ _ (hT x y h)

theorem fiber_stable_congr {α ω : Type*}
    (K : α → ω) (T S : α → α)
    (h : ∀ x, T x = S x) :
    FiberStable K T ↔ FiberStable K S := by
  constructor
  · intro ht x y hxy
    rw [← h x, ← h y]
    exact ht x y hxy
  · intro hs x y hxy
    rw [h x, h y]
    exact hs x y hxy

/-- Precomposing a readout by injective output relabelling preserves
the fiber-compatibility criterion exactly. -/
theorem fiber_stable_injective_relabel {α ω ν : Type*}
    (K : α → ω) (f : ω → ν) (hf : Function.Injective f)
    (T : α → α) :
    FiberStable (fun x => f (K x)) T ↔ FiberStable K T := by
  constructor
  · intro h x y hxy
    exact hf (h x y (congrArg f hxy))
  · intro h x y hxy
    exact congrArg f (h x y (hf hxy))

theorem fiber_stable_of_injective {α ω : Type*}
    (K : α → ω) (hK : Function.Injective K)
    (T : α → α) : FiberStable K T := by
  intro x y hxy
  rw [hK hxy]

theorem fiber_stable_of_constant_readout {α ω : Type*}
    (K : α → ω) (hK : ∀ x y, K x = K y)
    (T : α → α) : FiberStable K T := by
  intro x y _
  exact hK (T x) (T y)

/-- For a fiber-respecting old operator language, only the present output
matters for predicting all future words. -/
theorem old_word_kernel_iff_fiber {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (hs : Respects K step) (x y : α) :
    WordEq K step x y ↔ K x = K y :=
  (respects_iff_now_complete K step).1 hs x y

/-- Old-language semantic compatibility equals preservation of
immediate readout fibers when old primitives respect those fibers. -/
theorem compatible_iff_fiber_stable {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (hs : Respects K step) (T : α → α) :
    Compatible K step T ↔ FiberStable K T := by
  constructor
  · intro ht x y hxy
    have hword := (old_word_kernel_iff_fiber K step hs x y).2 hxy
    exact word_now (ht x y hword)
  · intro ht x y hxy
    have heq : K x = K y := word_now hxy
    exact (old_word_kernel_iff_fiber K step hs (T x) (T y)).2
      (ht x y heq)

/-- The predicate FiberStable is the exact existing F0 fiber condition
when K and T are endomorphisms of the same state space. -/
theorem fiber_stable_eq_F0_respects {α : Type*}
    (K T : α → α) :
    FiberStable K T ↔ RespectsFibers K T := by
  rfl

/-- For an idempotent F0 observation map, semantic compatibility
is equivalent to actual descent through forgetting. -/
theorem compatible_iff_f0_descends {α ι : Type*}
    (K : α → α) (step : ι → α → α)
    (hK : Idempotent K) (hs : Respects K step)
    (T : α → α) :
    Compatible K step T ↔ Descends K T := by
  rw [descends_iff_respects hK]
  exact (compatible_iff_fiber_stable K step hs T).trans
    (fiber_stable_eq_F0_respects K T)

/-- The F0 descendant of a compatible new operator is guaranteed
whenever the original vocabulary respects F0 fibers. -/
theorem compatible_to_f0_descends {α ι : Type*}
    (K : α → α) (step : ι → α → α)
    (hK : Idempotent K) (hs : Respects K step)
    (T : α → α) (hT : Compatible K step T) :
    Descends K T :=
  (compatible_iff_f0_descends K step hK hs T).1 hT

/-- Conversely every F0-descending update defines a semantic operator
on the old observation quotient. -/
theorem f0_descends_to_compatible {α ι : Type*}
    (K : α → α) (step : ι → α → α)
    (hK : Idempotent K) (hs : Respects K step)
    (T : α → α) (hT : Descends K T) :
    Compatible K step T :=
  (compatible_iff_f0_descends K step hK hs T).2 hT

/-- Each descending update can be added as an independent primitive
without refining the old prediction equivalence. -/
theorem f0_safe_extension {α ι : Type*}
    (K : α → α) (step : ι → α → α)
    (hK : Idempotent K) (hs : Respects K step)
    (T : α → α) (hT : Descends K T)
    (x y : α) :
    WordEq K (LinearInputOperatorRefinement.sumStep step
      (fun _ : Unit => T)) x y ↔ WordEq K step x y := by
  exact ((LinearInputOperatorRefinement.extension_exact_iff_preserves K step
    (fun _ : Unit => T)).2 (by
      intro j a b hab
      exact f0_descends_to_compatible K step hK hs T hT a b hab)) x y

/-- For a family of F0-descending updates, all extensions are safe. -/
theorem f0_safe_family_extension {α ι κ : Type*}
    (K : α → α) (step : ι → α → α)
    (hK : Idempotent K) (hs : Respects K step)
    (fresh : κ → α → α)
    (hT : ∀ j, Descends K (fresh j))
    (x y : α) :
    WordEq K (LinearInputOperatorRefinement.sumStep step fresh) x y ↔
      WordEq K step x y := by
  exact ((LinearInputOperatorRefinement.extension_exact_iff_preserves K step fresh).2
    (by
      intro j a b hab
      exact f0_descends_to_compatible K step hK hs (fresh j) (hT j) a b hab)) x y

/-- Compatibility carries the old quotient into itself: it never
splits a state class of the existing F0 observer. -/
theorem f0_descends_has_quotient_map {α ι : Type*}
    (K : α → α) (step : ι → α → α)
    (hK : Idempotent K) (hs : Respects K step)
    (T : α → α) (hT : Descends K T) :
    ∃ F : State K step → State K step,
      ∀ x, F (encode K step x) = encode K step (T x) := by
  exact (compatible_iff_induced_exists K step T).1
    (f0_descends_to_compatible K step hK hs T hT)

/-- This concrete F0 example fails semantic compatibility exactly
when its update exposes a forgotten distinction. -/
theorem example_noncompatible :
    ¬ Compatible LinearInputF0.exampleK
      (fun _ : Unit => (fun x : Fin 3 => x))
      LinearInputF0Descent.exampleUpdate := by
  intro h
  have hOld : WordEq LinearInputF0.exampleK
      (fun _ : Unit => (fun x : Fin 3 => x)) 0 1 := by
    intro word
    have hrun : ∀ x : Fin 3,
        run (fun _ : Unit => (fun x : Fin 3 => x)) word x = x := by
      intro x
      induction word with
      | nil => rfl
      | cons i tail ih =>
          change run (fun _ : Unit => (fun x : Fin 3 => x)) tail x = x
          exact ih
    rw [hrun, hrun]
    decide
  have heq := word_now (h 0 1 hOld)
  have hne :
      LinearInputF0.exampleK (LinearInputF0Descent.exampleUpdate (0 : Fin 3)) ≠
      LinearInputF0.exampleK (LinearInputF0Descent.exampleUpdate (1 : Fin 3)) := by decide
  exact hne heq

end LinearInputOperatorF0Bridge
