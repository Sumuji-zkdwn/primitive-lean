/-!
# Genuine bridge from the original OperatorWordObservations.inc proof source

This snippet is compiled in CI with the exact native .inc file prepended
before it and imports SelfRewritingObserverExtensions. This is not a copied
or renamed substitute for the repository's original WordEq theorem.
-/

namespace SelfRewritingObserver

/-- The two independently defined list interpreters are extensionally equal. -/
theorem run_agrees_native (m : Mode) :
    ∀ (w : List Action) (s : State),
      LinearInputOperatorWords.run (step m) w s = run m w s := by
  intro w
  induction w with
  | nil =>
      intro s
      rfl
  | cons a rest ih =>
      intro s
      exact ih (step m a s)

/-- The concrete finite observer uses exactly the native observational kernel. -/
theorem native_wordEq_iff_signature (m : Mode) (s t : State) :
    LinearInputOperatorWords.WordEq readout (step m) s t ↔
      signature m s = signature m t := by
  constructor
  · intro h
    apply (wordEq_iff_signature m s t).1
    intro w
    have hw : readout (LinearInputOperatorWords.run (step m) w s) =
        readout (LinearInputOperatorWords.run (step m) w t) := h w
    rw [run_agrees_native m w s, run_agrees_native m w t] at hw
    exact hw
  · intro h
    intro w
    rw [run_agrees_native m w s, run_agrees_native m w t]
    exact ((wordEq_iff_signature m s t).2 h) w

/-- Every old-program composite preserves all distinctions formerly invisible. -/
theorem compiled_old_program_cannot_reveal (m : Mode) {κ : Type*}
    (code : κ → List Action) (s t : State)
    (h : signature m s = signature m t) :
    LinearInputOperatorWords.WordEq readout
      (LinearInputOperatorWords.generated (step m) code) s t := by
  exact LinearInputOperatorWords.generated_no_new_distinctions
    readout (step m) code ((native_wordEq_iff_signature m s t).2 h)

/-- The rule probe is genuinely new observational power, not any dictionary
of finite programs in the former fixed scan/action alphabet. -/
theorem peek_rule_not_generated (code : RuleAction → List Action) :
    ¬ (∀ s t : State,
      LinearInputOperatorWords.WordEq readout
        (LinearInputOperatorWords.generated (step .feedback) code) s t ↔
          RuleWordEq s t) := by
  intro h
  let s0 : State := ⟨false, false, false, false, false⟩
  let s1 : State := ⟨false, false, false, false, true⟩
  have hsig : signature .feedback s0 = signature .feedback s1 := by decide
  have hOld := compiled_old_program_cannot_reveal .feedback code s0 s1 hsig
  have hNew : ¬ RuleWordEq s0 s1 := by
    intro hr
    have hw : readout (ruleRun [.peekRule] s0) ≠
        readout (ruleRun [.peekRule] s1) := by decide
    exact hw (hr [.peekRule])
  exact hNew ((h s0 s1).1 hOld)

end SelfRewritingObserver
