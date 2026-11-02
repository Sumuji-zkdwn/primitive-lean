/-!
Boundary case: the exact conjugacy-orbit and right-zero-band conclusions for
one-point forgetting are NOT general consequences of F0 idempotence.

A constant F0 retraction on Fin 3 has a Galois closure containing a genuinely
non-idempotent two-stage chain. This is a direct proof, not a computation oracle.
-/

namespace LinearInputStrangeBoundary

open LinearInputStrangeGalois LinearInputStrangeConjugacy

/-- An ordinary F0 idempotent collapsing all of Fin 3 to zero. -/
def constantZero (_ : Fin 3) : Fin 3 := 0

/-- A length-two transition chain 2 -> 1 -> 0 -> 0. -/
def delayedZero (x : Fin 3) : Fin 3 :=
  if x = 2 then 1 else 0

theorem constant_zero_idempotent :
    LinearInputF0.Idempotent constantZero := by
  intro x
  rfl

theorem delayed_zero_not_idempotent :
    ¬ LinearInputF0.Idempotent delayedZero := by
  intro h
  have h2 := h (2 : Fin 3)
  norm_num [delayedZero, Fin.ext_iff] at h2

/-- Every test stopping constantZero also stops delayedZero. -/
theorem delayed_zero_in_constant_closure :
    delayedZero ∈
      Close (Stops (α := Fin 3)) ({constantZero} : Set (Fin 3 → Fin 3)) := by
  intro T hT
  have ht : Stops T constantZero := hT constantZero rfl
  obtain ⟨x, hx, hfixed⟩ := ht
  have hx0 : x ≠ (0 : Fin 3) := by
    intro h
    subst x
    exact hx rfl
  have hTx : T x = 0 := by
    simpa [constantZero] using hfixed.symm
  refine ⟨x, ?_, ?_⟩
  · fin_cases x
    · exact (hx0 rfl).elim
    · decide
    · decide
  · simp [delayedZero, hTx]

/-- Every conjugate of a constant map is constant; the chain is not. -/
theorem delayed_zero_not_constant_conjugate :
    ¬ ∃ e : Fin 3 ≃ Fin 3, delayedZero = Conjugate e constantZero := by
  rintro ⟨e, he⟩
  have h02 : delayedZero (0 : Fin 3) = delayedZero (2 : Fin 3) := by
    calc
      delayedZero 0 = Conjugate e constantZero 0 := congrFun he 0
      _ = Conjugate e constantZero 2 := rfl
      _ = delayedZero 2 := (congrFun he 2).symm
  norm_num [delayedZero, Fin.ext_iff] at h02

/-- A general idempotent's closed family need not be a conjugacy orbit. -/
theorem constant_closure_not_conjugacy_orbit :
    Close (Stops (α := Fin 3)) ({constantZero} : Set (Fin 3 → Fin 3)) ≠
      {S | ∃ e : Fin 3 ≃ Fin 3, S = Conjugate e constantZero} := by
  intro heq
  have hm := delayed_zero_in_constant_closure
  rw [heq] at hm
  exact delayed_zero_not_constant_conjugate hm

end LinearInputStrangeBoundary
