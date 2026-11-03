/-!
# Semantic operator closure on the minimal predictive quotient

A new primitive operator can be compatible with the observational
equivalence of the old operator language even if it is not obtainable
by finite composition of old operators.

The precise distinction:
* syntactic generation: an old finite word computes the new action;
* semantic compatibility: the new action respects the entire old
  observational kernel, so it acts on the old quotient.

We formalize the induced quotient operation and its universal property,
and give a concrete finite witness of a compatible but non-generatable
primitive. No claim is made about efficient discovery of such operators.
-/

noncomputable section

namespace LinearInputOperatorSemanticClosure

open LinearInputOperatorWords
open LinearInputOperatorRefinement

/-- A state transformer preserves all equivalences visible to the old language. -/
def Compatible {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) (T : α → α) : Prop :=
  ∀ x y, WordEq K step x y → WordEq K step (T x) (T y)

/-- Every finite word defines a compatible semantic operator. -/
theorem compatible_word {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) (word : List ι) :
    Compatible K step (run step word) := by
  intro x y hxy
  exact word_run hxy word

/-- The identity transformer is observationally compatible. -/
theorem compatible_id {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) :
    Compatible K step (fun x => x) := by
  intro x y hxy
  exact hxy

/-- Compatible state transformers are closed under sequential composition. -/
theorem compatible_comp {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (T S : α → α)
    (hT : Compatible K step T) (hS : Compatible K step S) :
    Compatible K step (fun x => S (T x)) := by
  intro x y hxy
  exact hS _ _ (hT x y hxy)

/-- Every constant transformer is compatible, regardless of the old language. -/
theorem compatible_constant {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) (c : α) :
    Compatible K step (fun _ => c) := by
  intro x y _
  exact word_refl K step c

/-- A compatible transformer induces a map on minimal predictive states. -/
def induced {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) (T : α → α)
    (hT : Compatible K step T) :
    State K step → State K step :=
  Quotient.lift (fun x => encode K step (T x)) (by
    intro x y hxy
    exact Quotient.sound (hT x y hxy))

/-- Encoding after a new primitive equals applying its induced map. -/
theorem induced_encode {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) (T : α → α)
    (hT : Compatible K step T) (x : α) :
    induced K step T hT (encode K step x) = encode K step (T x) := rfl

/-- The quotient operator is uniquely determined by its action on encoded states. -/
theorem induced_unique {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) (T : α → α)
    (hT : Compatible K step T)
    (F : State K step → State K step)
    (hF : ∀ x, F (encode K step x) = encode K step (T x)) :
    F = induced K step T hT := by
  funext q
  induction q using Quotient.inductionOn with
  | _ x =>
      exact hF x

/-- A state transformer is compatible iff it admits a semantic quotient action. -/
theorem compatible_iff_induced_exists {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) (T : α → α) :
    Compatible K step T ↔
      ∃ F : State K step → State K step,
        ∀ x, F (encode K step x) = encode K step (T x) := by
  constructor
  · intro hT
    exact ⟨induced K step T hT, fun x => induced_encode K step T hT x⟩
  · rintro ⟨F, hF⟩ x y hxy
    apply (encode_eq_iff K step (T x) (T y)).1
    calc
      encode K step (T x) = F (encode K step x) := (hF x).symm
      _ = F (encode K step y) :=
        congrArg F ((encode_eq_iff K step x y).2 hxy)
      _ = encode K step (T y) := hF y

/-- The induced identity transformer is the identity of predictive states. -/
theorem induced_id {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) :
    induced K step (fun x => x) (compatible_id K step) =
      (fun q => q) := by
  funext q
  induction q using Quotient.inductionOn with
  | _ x => rfl

/-- Syntactic composition agrees with composition on the predictive quotient. -/
theorem induced_comp {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (T S : α → α)
    (hT : Compatible K step T) (hS : Compatible K step S)
    (q : State K step) :
    induced K step (fun x => S (T x))
        (compatible_comp K step T S hT hS) q =
      induced K step S hS (induced K step T hT q) := by
  induction q using Quotient.inductionOn with
  | _ x => rfl

/-- An onto original state transformer induces an onto predictive operator. -/
theorem induced_surjective {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (T : α → α) (hT : Compatible K step T)
    (hs : Function.Surjective T) :
    Function.Surjective (induced K step T hT) := by
  intro q
  induction q using Quotient.inductionOn with
  | _ x =>
      obtain ⟨p, hp⟩ := hs x
      refine ⟨encode K step p, ?_⟩
      rw [induced_encode, hp]

/-- If T reflects old observational equality, its quotient action is one-to-one. -/
theorem induced_injective_of_reflects {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (T : α → α) (hT : Compatible K step T)
    (hreflect : ∀ x y, WordEq K step (T x) (T y) →
      WordEq K step x y) :
    Function.Injective (induced K step T hT) := by
  intro q r hqr
  induction q using Quotient.inductionOn with
  | _ x =>
    induction r using Quotient.inductionOn with
    | _ y =>
        have hTxTy : WordEq K step (T x) (T y) :=
          (encode_eq_iff K step (T x) (T y)).1 hqr
        exact (encode_eq_iff K step x y).2
          (hreflect x y hTxTy)

/-- Compatible operators with unchanged original readout have unchanged
readout after quotienting. -/
theorem induced_readout_invariant {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α)
    (T : α → α) (hT : Compatible K step T)
    (hK : ∀ x, K (T x) = K x)
    (q : State K step) :
    readout K step (induced K step T hT q) =
      readout K step q := by
  induction q using Quotient.inductionOn with
  | _ x =>
      exact hK x

/-- When old current observations already determine all word observations,
preservation of a single readout is enough for semantic compatibility. -/
theorem compatible_of_respects_readout {α ω ι : Type*}
    (K : α → ω) (step : ι → α → α) (T : α → α)
    (hs : Respects K step)
    (hT : ∀ x y, K x = K y → K (T x) = K (T y)) :
    Compatible K step T := by
  intro x y hxy
  exact respects_implies_now_complete K step hs
    (hT x y (word_now hxy))

/-- A concrete primitive whose action is not a word in the old alphabet. -/
def constantTwo : Fin 3 → Fin 3 := fun _ => 2

theorem constantTwo_compatible :
    Compatible exampleK baseStep constantTwo :=
  compatible_constant exampleK baseStep 2

/-- The new constant primitive does not create new observational distinctions. -/
theorem constantTwo_conservative (x y : Fin 3) :
    WordEq exampleK
        (sumStep baseStep (fun _ : Unit => constantTwo)) x y ↔
      WordEq exampleK baseStep x y := by
  apply (extension_exact_iff_preserves exampleK baseStep
    (fun _ : Unit => constantTwo)).2
  intro j a b _
  exact word_refl exampleK baseStep 2

/-- Nevertheless no finite word of the old alphabet can implement this
primitive, even modulo observational equivalence. -/
theorem constantTwo_not_old_word_mod_observation (word : List Unit) :
    ¬ ∀ x : Fin 3,
      encode exampleK baseStep (run baseStep word x) =
        encode exampleK baseStep (constantTwo x) := by
  intro h
  have he : encode exampleK baseStep (0 : Fin 3) =
      encode exampleK baseStep (2 : Fin 3) := by
    simpa [run_base, constantTwo] using h 0
  have hK : exampleK (0 : Fin 3) = exampleK (2 : Fin 3) :=
    word_now ((encode_eq_iff exampleK baseStep 0 2).1 he)
  have hne : exampleK (0 : Fin 3) ≠ exampleK (2 : Fin 3) := by decide
  exact hne hK

/-- Thus no dictionary of old words realizes this observationally
conservative new primitive on the predictive quotient. -/
theorem constantTwo_not_generated_mod_observation
    (code : Unit → List Unit) :
    ¬ ∀ x : Fin 3,
      encode exampleK baseStep ((generated baseStep code) () x) =
        encode exampleK baseStep (constantTwo x) := by
  exact constantTwo_not_old_word_mod_observation (code ())

end LinearInputOperatorSemanticClosure
