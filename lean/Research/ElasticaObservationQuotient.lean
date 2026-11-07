import Elastica.Geometry

/-!
# A definitional bridge from elastica curvature to predictive-state quotients

This file deliberately does not import the subsequent operator-word modules.
The abstract splitting result is derived from the quotient construction alone;
the finite curved example uses the original Elastica.curvature definition.
It does not show that the state-dependent fresh action is a physically feasible
middle-piece replacement, or that refinement is forced by elastica equations.
-/

namespace ElasticaObservationBridge

/-- Run a finite left-to-right word of deterministic actions. -/
def run {α ι : Type*} (step : ι → α → α) : List ι → α → α
  | [], x => x
  | i :: tail, x => run step tail (step i x)

/-- States are observationally equivalent when all action words have equal readout. -/
def ObsEq {α ω ι : Type*} (K : α → ω) (step : ι → α → α)
    (x y : α) : Prop :=
  ∀ word : List ι, K (run step word x) = K (run step word y)

/-- The setoid is just equality of all future observations. -/
def obsSetoid {α ω ι : Type*} (K : α → ω)
    (step : ι → α → α) : Setoid α where
  r := ObsEq K step
  iseqv := ⟨
    (by intro x word; rfl),
    (by intro x y h word; exact (h word).symm),
    (by intro x y z h g word; exact (h word).trans (g word))⟩

abbrev PredState {α ω ι : Type*} (K : α → ω)
    (step : ι → α → α) := Quotient (obsSetoid K step)

def encode {α ω ι : Type*} (K : α → ω)
    (step : ι → α → α) (x : α) : PredState K step :=
  Quotient.mk (obsSetoid K step) x

theorem encode_eq_iff {α ω ι : Type*} (K : α → ω)
    (step : ι → α → α) (x y : α) :
    encode K step x = encode K step y ↔ ObsEq K step x y := by
  constructor
  · intro h
    exact Quotient.exact h
  · intro h
    exact Quotient.sound h

/-- Extend the old alphabet by genuinely new action names. -/
def sumStep {α ι κ : Type*} (old : ι → α → α)
    (fresh : κ → α → α) : Sum ι κ → α → α
  | Sum.inl i => old i
  | Sum.inr j => fresh j

/-- An old word has the same action semantics in the enlarged alphabet. -/
theorem run_inl {α ι κ : Type*} (old : ι → α → α)
    (fresh : κ → α → α) (word : List ι) (x : α) :
    run (sumStep old fresh) (word.map Sum.inl) x = run old word x := by
  induction word generalizing x with
  | nil => rfl
  | cons i tail ih =>
      change run (sumStep old fresh) (tail.map Sum.inl) (old i x) =
        run old tail (old i x)
      exact ih (old i x)

/-- More available actions cannot coarsen the original word-equivalence. -/
theorem extended_implies_old {α ω ι κ : Type*}
    (K : α → ω) (old : ι → α → α) (fresh : κ → α → α)
    {x y : α} (h : ObsEq K (sumStep old fresh) x y) :
    ObsEq K old x y := by
  intro word
  have hword := h (word.map Sum.inl)
  simpa only [run_inl] using hword

/-- Forget the extra action names when comparing predictive states. -/
def forget {α ω ι κ : Type*}
    (K : α → ω) (old : ι → α → α) (fresh : κ → α → α) :
    PredState K (sumStep old fresh) → PredState K old :=
  Quotient.lift (fun x => encode K old x) (by
    intro x y h
    exact Quotient.sound (extended_implies_old K old fresh h))

/-- This is definitional, not a dynamical statement. -/
theorem forget_encode {α ω ι κ : Type*}
    (K : α → ω) (old : ι → α → α) (fresh : κ → α → α)
    (x : α) :
    forget K old fresh (encode K (sumStep old fresh) x) =
      encode K old x := rfl

/-- Reproof of the subsequent strict_refinement_splits_quotient statement,
without importing any subsequent theorem. The hypotheses contain the entire
strict-refinement premise. -/
theorem strict_refinement_splits_quotient {α ω ι κ : Type*}
    (K : α → ω) (old : ι → α → α) (fresh : κ → α → α)
    (x y : α)
    (hOld : ObsEq K old x y)
    (hExt : ¬ ObsEq K (sumStep old fresh) x y) :
    ∃ q r : PredState K (sumStep old fresh),
      q ≠ r ∧ forget K old fresh q = forget K old fresh r := by
  refine ⟨encode K (sumStep old fresh) x,
    encode K (sumStep old fresh) y, ?_, ?_⟩
  · intro hEq
    exact hExt ((encode_eq_iff K (sumStep old fresh) x y).1 hEq)
  · exact (encode_eq_iff K old x y).2 hOld

/-! ## An explicit three-curve, finite-state interpretation -/

/-- Three smooth angles: two constant tangents, and an affine tangent. -/
def angle (x : Fin 3) : ℝ → ℝ :=
  if x = 0 then (fun _ => (0 : ℝ))
  else if x = 1 then (fun _ => (1 : ℝ))
  else (fun s => s)

/-- Read out the initial Elastica signed curvature at arc-length zero. -/
def K (x : Fin 3) : ℝ := Elastica.curvature (angle x) 0

/-- The first two curves have the same observed curvature. -/
theorem K_zero : K (0 : Fin 3) = 0 := by
  simp [K, angle]

theorem K_one : K (1 : Fin 3) = 0 := by
  simp [K, angle]

/-- The third curve is distinguished using the initial curvature definition. -/
theorem K_two : K (2 : Fin 3) = 1 := by
  simp [K, angle, Elastica.curvature]

/-- The old system leaves the curve label unchanged. -/
def oldStep (_ : Unit) (x : Fin 3) : Fin 3 := x

/-- The added action sends the second curve to the affine curve. -/
def freshStep (_ : Unit) (x : Fin 3) : Fin 3 :=
  if x = 1 then 2 else x

theorem run_old (word : List Unit) (x : Fin 3) :
    run oldStep word x = x := by
  induction word generalizing x with
  | nil => rfl
  | cons _ tail ih =>
      change run oldStep tail x = x
      exact ih x

theorem old_cannot_separate : ObsEq K oldStep (0 : Fin 3) 1 := by
  intro word
  simpa [run_old, K_zero, K_one]

theorem fresh_separates :
    ¬ ObsEq K (sumStep oldStep freshStep) (0 : Fin 3) 1 := by
  intro h
  have hbad : (0 : ℝ) = 1 := by
    simpa [run, sumStep, freshStep, K_zero, K_two] using (h [Sum.inr ()])
  exact zero_ne_one hbad

/-- Conditional quotient splitting is witnessed by the three actual angles. -/
theorem curve_split :
    ∃ q r : PredState K (sumStep oldStep freshStep),
      q ≠ r ∧ forget K oldStep freshStep q = forget K oldStep freshStep r := by
  exact strict_refinement_splits_quotient K oldStep freshStep
    0 1 old_cannot_separate fresh_separates

/-! ## A finite countermodel to *unconditional* splitting -/

/-- Another allowable new action, an identity, carries no extra information. -/
def inertStep (_ : Unit) (x : Fin 3) : Fin 3 := x

theorem run_inert (word : List (Sum Unit Unit)) (x : Fin 3) :
    run (sumStep oldStep inertStep) word x = x := by
  induction word generalizing x with
  | nil => rfl
  | cons action tail ih =>
      cases action with
      | inl i =>
          change run (sumStep oldStep inertStep) tail x = x
          exact ih x
      | inr j =>
          change run (sumStep oldStep inertStep) tail x = x
          exact ih x

/-- The forgetful map is injective in this alternative finite transition model. -/
theorem inert_forget_injective :
    Function.Injective (forget K oldStep inertStep) := by
  intro q r hEq
  induction q using Quotient.inductionOn with
  | _ x =>
    induction r using Quotient.inductionOn with
    | _ y =>
        have hOld : ObsEq K oldStep x y :=
          (encode_eq_iff K oldStep x y).1 hEq
        have hK : K x = K y := by
          simpa [run_old] using (hOld [])
        apply (encode_eq_iff K (sumStep oldStep inertStep) x y).2
        intro word
        simpa [run_inert] using hK

/-- With the same initial curves and observer, unconditional splitting is false. -/
theorem inert_no_split :
    ¬ ∃ q r : PredState K (sumStep oldStep inertStep),
      q ≠ r ∧ forget K oldStep inertStep q = forget K oldStep inertStep r := by
  rintro ⟨q, r, hne, heq⟩
  exact hne (inert_forget_injective heq)

#print axioms strict_refinement_splits_quotient
#print axioms K_two
#print axioms curve_split
#print axioms inert_no_split

end ElasticaObservationBridge
