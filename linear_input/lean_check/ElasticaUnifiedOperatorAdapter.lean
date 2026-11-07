import ElasticaOperatorTheory
import Research.ElasticaObservationQuotient

/-!
Additive adapter between the actual #99 and #100 declarations.
Neither source is modified. Quotient isomorphisms are for the same K/step;
the two geometric examples are not asserted to be the same system.
-/
noncomputable section

namespace ElasticaUnifiedOperatorAdapter

open LinearInputOperatorWords
open LinearInputOperatorRefinement

theorem run_agrees {α ι : Type*} (step : ι → α → α)
    (word : List ι) (x : α) :
    ElasticaObservationBridge.run step word x = run step word x := by
  induction word generalizing x with
  | nil => rfl
  | cons i tail ih =>
      change ElasticaObservationBridge.run step tail (step i x) =
        run step tail (step i x)
      exact ih (step i x)

theorem obs_eq_wordEq {α ω ι : Type*} (K : α → ω)
    (step : ι → α → α) (x y : α) :
    ElasticaObservationBridge.ObsEq K step x y ↔ WordEq K step x y := by
  unfold ElasticaObservationBridge.ObsEq WordEq
  simp only [run_agrees]

def toLater {α ω ι : Type*} (K : α → ω) (step : ι → α → α) :
    ElasticaObservationBridge.PredState K step → State K step :=
  Quotient.lift (fun x => encode K step x) (by
    intro x y h
    exact Quotient.sound ((obs_eq_wordEq K step x y).mp h))

def fromLater {α ω ι : Type*} (K : α → ω) (step : ι → α → α) :
    State K step → ElasticaObservationBridge.PredState K step :=
  Quotient.lift (fun x => ElasticaObservationBridge.encode K step x) (by
    intro x y h
    exact Quotient.sound ((obs_eq_wordEq K step x y).mpr h))

theorem from_to {α ω ι : Type*} (K : α → ω) (step : ι → α → α)
    (q : ElasticaObservationBridge.PredState K step) :
    fromLater K step (toLater K step q) = q := by
  induction q using Quotient.inductionOn with
  | _ x => rfl

theorem to_from {α ω ι : Type*} (K : α → ω) (step : ι → α → α)
    (q : State K step) :
    toLater K step (fromLater K step q) = q := by
  induction q using Quotient.inductionOn with
  | _ x => rfl

theorem forget_commutes {α ω ι κ : Type*}
    (K : α → ω) (old : ι → α → α) (fresh : κ → α → α)
    (q : ElasticaObservationBridge.PredState K
      (ElasticaObservationBridge.sumStep old fresh)) :
    toLater K old (ElasticaObservationBridge.forget K old fresh q) =
      LinearInputOperatorRefinement.forget K old fresh
        (toLater K (ElasticaObservationBridge.sumStep old fresh) q) := by
  induction q using Quotient.inductionOn with
  | _ x => rfl

theorem injective_readout_relabel {α ω ν ι : Type*}
    (K : α → ω) (f : ω → ν) (hf : Function.Injective f)
    (step : ι → α → α) (x y : α) :
    WordEq (fun z => f (K z)) step x y ↔ WordEq K step x y := by
  constructor
  · intro h word
    exact hf (h word)
  · intro h word
    exact congrArg f (h word)

/-- The #100 observer is the old finite example embedded in the reals. -/
theorem curvature_as_old_example (i : Fin 3) :
    ElasticaObservationBridge.K i = ((exampleK i).val : ℝ) := by
  fin_cases i <;>
    simp [exampleK, ElasticaObservationBridge.K_zero,
      ElasticaObservationBridge.K_one, ElasticaObservationBridge.K_two]

theorem old_action_is_existing :
    ElasticaObservationBridge.oldStep = baseStep := rfl

theorem fresh_action_is_existing :
    ElasticaObservationBridge.freshStep = witnessFresh := rfl

theorem existing_finite_example_same_kernel (step : ι → Fin 3 → Fin 3)
    (x y : Fin 3) :
    WordEq ElasticaObservationBridge.K step x y ↔
      WordEq exampleK step x y := by
  constructor
  · intro h word
    apply Fin.ext
    have hv := h word
    rw [curvature_as_old_example, curvature_as_old_example] at hv
    exact_mod_cast hv
  · intro h word
    rw [curvature_as_old_example, curvature_as_old_example]
    exact_mod_cast congrArg Fin.val (h word)

theorem pr100_same_extended_kernel (x y : Fin 3) :
    ElasticaObservationBridge.ObsEq ElasticaObservationBridge.K
      (ElasticaObservationBridge.sumStep ElasticaObservationBridge.oldStep
        ElasticaObservationBridge.freshStep) x y ↔
    WordEq exampleK (sumStep baseStep witnessFresh) x y := by
  rw [obs_eq_wordEq, existing_finite_example_same_kernel]
  rfl

#print axioms obs_eq_wordEq
#print axioms forget_commutes
#print axioms curvature_as_old_example
#print axioms pr100_same_extended_kernel
end ElasticaUnifiedOperatorAdapter
