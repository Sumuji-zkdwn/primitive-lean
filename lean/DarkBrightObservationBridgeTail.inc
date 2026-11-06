/-!
This tail is compiled after the exact repository OperatorWordObservations.inc,
with an import of DarkBrightObservation.  It does not duplicate WordEq.
-/
namespace DarkBrightObservation
open LinearInputOperatorWords

/-- The native all-word observational quotient is exactly the three quantities. -/
theorem native_wordEq_iff_summary (x y : Spinor) :
    WordEq output step x y ↔ summary x = summary y := by
  constructor
  · intro h
    apply summary_eq_of_two_reads x y
    · simpa only [run] using h []
    · simpa only [run] using h [()]
  · intro h
    apply (representation_word_eq output step summary summaryStep project
      project_summary summary_step x y).2
    intro word
    rw [h]

/-- For this particular model, depth one already determines every future word. -/
theorem native_wordEq_iff_two_reads (x y : Spinor) :
    WordEq output step x y ↔
      (output x = output y ∧ output (step () x) = output (step () y)) := by
  rw [native_wordEq_iff_summary, two_reads_iff_summary]

/-- Current darkness is not all-future invisibility. -/
theorem native_current_not_future :
    output witnessLeft = output witnessRight ∧
    ¬ WordEq output step witnessLeft witnessRight := by
  constructor
  · exact current_collision.1
  · intro h
    exact next_separates (by simpa only [run] using h [()])

/-- Common phase is invisible even after arbitrarily many allowed pulses. -/
theorem native_common_phase_invisible (p q : ℝ)
    (h : p^2+q^2=1) (x : Spinor) :
    WordEq output step (commonPhase p q x) x := by
  apply (native_wordEq_iff_summary _ _).2
  exact common_phase_summary p q h x

/-- Kernel minimality, not an unrestricted claim about coordinate dimension. -/
theorem native_predictive_minimal {β : Type*}
    (f : Spinor → β) (update : Unit → β → β) (out : β → Observation)
    (hout : ∀ x, out (f x) = output x)
    (hf : ∀ u x, f (step u x) = update u (f x))
    {x y : Spinor} (hxy : f x = f y) : summary x = summary y := by
  apply (native_wordEq_iff_summary x y).1
  apply (representation_word_eq output step f update out hout hf x y).2
  intro word
  rw [hxy]

end DarkBrightObservation
