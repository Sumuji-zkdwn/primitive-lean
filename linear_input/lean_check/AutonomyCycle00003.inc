/-!
Autonomously generated finite witness, cycle 3.

Initial states 0 and 1 have the same readout; the old action is
the identity. The generated additional operator separates them.
This is a finite counterexample certificate, not a new general law.
Generation is restricted to enumerated small finite models.
-/

noncomputable section
namespace LinearInputAutoCycle00003

def observer (x : Fin 3) : Fin 2 :=
  if x.val < 2 then 0 else 1

def oldStep : Unit → Fin 3 → Fin 3 :=
  fun _ x => x

def newStep (x : Fin 3) : Fin 3 :=
  if x = 0 then 2 else if x = 1 then 0 else x

theorem old_run_identity (word : List Unit) (x : Fin 3) :
    LinearInputOperatorWords.run oldStep word x = x := by
  induction word with
  | nil => rfl
  | cons _ rest ih =>
      change LinearInputOperatorWords.run oldStep rest x = x
      exact ih

theorem old_indistinguishable :
    LinearInputOperatorWords.WordEq observer oldStep
      (0 : Fin 3) (1 : Fin 3) := by
  intro word
  rw [old_run_identity, old_run_identity]
  decide

theorem new_distinguishes :
    ¬ LinearInputOperatorWords.WordEq observer
      (LinearInputOperatorRefinement.sumStep oldStep
        (fun _ : Unit => newStep))
      (0 : Fin 3) (1 : Fin 3) := by
  intro h
  have hne : observer (newStep (0 : Fin 3)) ≠
      observer (newStep (1 : Fin 3)) := by decide
  have heq := h [Sum.inr ()]
  apply hne
  simpa [LinearInputOperatorWords.run,
    LinearInputOperatorRefinement.sumStep] using heq

theorem no_old_word_dictionary (code : Unit → List Unit) :
    ¬ (∀ x y : Fin 3,
      LinearInputOperatorWords.WordEq observer
        (LinearInputOperatorWords.generated oldStep code) x y ↔
      LinearInputOperatorWords.WordEq observer
        (LinearInputOperatorRefinement.sumStep oldStep
          (fun _ : Unit => newStep)) x y) := by
  intro h
  have hg : LinearInputOperatorWords.WordEq observer
      (LinearInputOperatorWords.generated oldStep code)
      (0 : Fin 3) (1 : Fin 3) :=
    LinearInputOperatorWords.generated_no_new_distinctions
      observer oldStep code old_indistinguishable
  exact new_distinguishes ((h 0 1).mp hg)

theorem minimal_quotient_splits :
    ∃ q r : LinearInputOperatorWords.State observer
        (LinearInputOperatorRefinement.sumStep oldStep
          (fun _ : Unit => newStep)),
      q ≠ r ∧
        LinearInputOperatorRefinement.forget observer oldStep
          (fun _ : Unit => newStep) q =
        LinearInputOperatorRefinement.forget observer oldStep
          (fun _ : Unit => newStep) r := by
  exact LinearInputOperatorRefinement.strict_refinement_splits_quotient
    observer oldStep (fun _ : Unit => newStep)
      0 1 old_indistinguishable new_distinguishes

end LinearInputAutoCycle00003
