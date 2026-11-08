/-!
# Feedback policies versus fixed operator words

A fixed word is compiled before seeing the current state. A feedback
policy instead chooses the next operator label by observing the state.
Even when every existing primitive preserves the old predictive kernel,
a state-dependent dispatch may distinguish states hidden by all fixed
operator words.

Quotient-measurable policies are safe: when the chosen label depends
only on the old predictive state, their adaptive transformer descends
to the quotient and cannot refine the old observation equivalence.

These statements concern deterministic total maps, not a learnable
policy synthesis procedure or physical creation of information.
-/

noncomputable section

namespace LinearInputOperatorPolicies

open LinearInputOperatorWords
open LinearInputOperatorRefinement
open LinearInputOperatorSemanticClosure

/-- Choose an operator label from the current raw state. -/
def adaptive {α ι : Type*} (step : ι → α → α)
    (policy : α → ι) (x : α) : α :=
  step (policy x) x

/-- A safe policy selects equal labels for observationally equal states. -/
def PolicyStable {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (policy : α → ι) : Prop :=
  ∀ x y, WordEq K step x y → policy x = policy y

theorem policy_constant_stable {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) (i : ι) :
    PolicyStable K step (fun _ => i) := by
  intro x y _
  rfl

/-- A policy based only on the immediate readout is automatically safe. -/
theorem policy_stable_of_readout {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) (choose : ω → ι) :
    PolicyStable K step (fun x => choose (K x)) := by
  intro x y h
  exact congrArg choose (word_now h)

/-- Any policy defined on predictive quotient states is safe. -/
theorem policy_stable_of_quotient {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (choose : State K step → ι) :
    PolicyStable K step (fun x => choose (encode K step x)) := by
  intro x y h
  exact congrArg choose ((encode_eq_iff K step x y).2 h)

/-- Postprocessing labels preserves policy stability. -/
theorem policy_stable_postprocess {α ω ι κ : Type*}
    (K : α → ω) (step : ι → α → α)
    (policy : α → ι) (newLabel : ι → κ)
    (h : PolicyStable K step policy) :
    ∀ x y, WordEq K step x y →
      newLabel (policy x) = newLabel (policy y) := by
  intro x y hxy
  exact congrArg newLabel (h x y hxy)

/-- A stable policy's adaptive state transformer is semantically compatible. -/
theorem adaptive_compatible {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) (policy : α → ι)
    (hP : PolicyStable K step policy) :
    Compatible K step (adaptive step policy) := by
  intro x y hxy
  have hp : policy x = policy y := hP x y hxy
  change WordEq K step (step (policy x) x) (step (policy y) y)
  rw [← hp]
  exact word_step hxy (policy x)

theorem constant_adaptive_compatible {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) (i : ι) :
    Compatible K step (adaptive step (fun _ => i)) :=
  adaptive_compatible K step (fun _ => i)
    (policy_constant_stable K step i)

/-- A readout policy cannot add observational distinctions. -/
theorem readout_policy_compatible {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) (choose : ω → ι) :
    Compatible K step (adaptive step (fun x => choose (K x))) :=
  adaptive_compatible K step _ (policy_stable_of_readout K step choose)

/-- The adaptive operator of a quotient-policy induces a well-defined
endomorphism of the minimal predictive quotient. -/
theorem quotient_policy_has_induced {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (choose : State K step → ι) :
    ∃ F : State K step → State K step,
      ∀ x, F (encode K step x) =
        encode K step (adaptive step
          (fun a => choose (encode K step a)) x) := by
  exact (compatible_iff_induced_exists K step _).1
    (adaptive_compatible K step _
      (policy_stable_of_quotient K step choose))

/-- Registering a safe feedback policy as a new primitive is conservative. -/
theorem safe_adaptive_extension {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (policy : α → ι) (hP : PolicyStable K step policy)
    (x y : α) :
    WordEq K
        (sumStep step (fun _ : Unit => adaptive step policy)) x y ↔
      WordEq K step x y := by
  exact ((extension_exact_iff_preserves K step
    (fun _ : Unit => adaptive step policy)).2 (by
      intro j a b h
      exact adaptive_compatible K step policy hP a b h)) x y

/-- Any number of safe adaptive operators can be added simultaneously. -/
theorem safe_family_extension {α ω ι κ : Type*}
    (K : α → ω) (step : ι → α → α)
    (policy : κ → α → ι)
    (hP : ∀ j, PolicyStable K step (policy j))
    (x y : α) :
    WordEq K (sumStep step (fun j => adaptive step (policy j))) x y ↔
      WordEq K step x y := by
  exact ((extension_exact_iff_preserves K step
    (fun j => adaptive step (policy j))).2 (by
      intro j a b h
      exact adaptive_compatible K step (policy j) (hP j) a b h)) x y

/-- Fixed-step feedback iteration. -/
def feedbackIter {α ι : Type*}
    (step : ι → α → α) (policy : α → ι) :
    ℕ → α → α
  | 0, x => x
  | n + 1, x => feedbackIter step policy n (adaptive step policy x)

theorem feedback_zero {α ι : Type*}
    (step : ι → α → α) (policy : α → ι) (x : α) :
    feedbackIter step policy 0 x = x := rfl

theorem feedback_succ {α ι : Type*}
    (step : ι → α → α) (policy : α → ι) (n : ℕ) (x : α) :
    feedbackIter step policy (n + 1) x =
      feedbackIter step policy n (adaptive step policy x) := rfl

/-- Every finite feedback iterate preserves old predictive equivalence
when the underlying policy does. -/
theorem feedback_preserves_kernel {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (policy : α → ι) (hP : PolicyStable K step policy)
    (n : ℕ) {x y : α} (hxy : WordEq K step x y) :
    WordEq K step (feedbackIter step policy n x)
      (feedbackIter step policy n y) := by
  induction n generalizing x y with
  | zero =>
      exact hxy
  | succ n ih =>
      exact ih (adaptive_compatible K step policy hP x y hxy)

/-- Indistinguishable old states have the same readouts at every
feedback time, under a safe policy. -/
theorem feedback_readout_conservative {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (policy : α → ι) (hP : PolicyStable K step policy)
    {x y : α} (hxy : WordEq K step x y) (n : ℕ) :
    K (feedbackIter step policy n x) =
      K (feedbackIter step policy n y) :=
  word_now (feedback_preserves_kernel K step policy hP n hxy)

/-- An old system with identity and constant-to-2 actions. -/
def witnessStep : Bool → Fin 3 → Fin 3 :=
  fun b x => if b then 2 else x

/-- A feedback controller selects the constant action at state 1. -/
def witnessPolicy (x : Fin 3) : Bool := decide (x = 1)

theorem witness_respects_readout :
    Respects exampleK witnessStep := by
  intro b x y h
  cases b
  · simpa [witnessStep] using h
  · simp [witnessStep]

theorem witness_old_equivalent :
    WordEq exampleK witnessStep (0 : Fin 3) (1 : Fin 3) := by
  apply respects_implies_now_complete exampleK witnessStep
    witness_respects_readout
  decide

theorem witness_feedback_separates :
    exampleK (adaptive witnessStep witnessPolicy (0 : Fin 3)) ≠
      exampleK (adaptive witnessStep witnessPolicy (1 : Fin 3)) := by
  decide

/-- Unsafe feedback may split states that every fixed old word merges. -/
theorem witness_feedback_not_compatible :
    ¬ Compatible exampleK witnessStep (adaptive witnessStep witnessPolicy) := by
  intro h
  exact witness_feedback_separates
    (word_now (h 0 1 witness_old_equivalent))

theorem witness_policy_not_stable :
    ¬ PolicyStable exampleK witnessStep witnessPolicy := by
  intro h
  have hp := h 0 1 witness_old_equivalent
  have hne : witnessPolicy (0 : Fin 3) ≠ witnessPolicy (1 : Fin 3) := by decide
  exact hne hp

/-- Extending the old language by the unsafe feedback action strictly
increases its distinguishing power. -/
theorem witness_strict_extension :
    ¬ WordEq exampleK
      (sumStep witnessStep
        (fun _ : Unit => adaptive witnessStep witnessPolicy))
      (0 : Fin 3) (1 : Fin 3) := by
  intro h
  have hNew := h [Sum.inr ()]
  exact witness_feedback_separates (by simpa [run, sumStep] using hNew)

end LinearInputOperatorPolicies
