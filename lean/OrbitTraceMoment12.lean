import Mathlib

/-!
# First twelve moments of a quartic trace recurrence

The initial four moments and the p=3 recurrence imply every entry needed
for the four 3-step chain witness. This is a universal theorem in a commutative
ring, with the recurrence and initial conditions stated as explicit hypotheses.
-/

namespace OrbitTrace

theorem quartic_trace_first_twelve
    {K : Type*} [CommRing K] (s a : K) (M : ℕ → K)
    (h0 : M 0 = 1) (h1 : M 1 = s) (h2 : M 2 = s ^ 2)
    (h3 : M 3 = s ^ 3)
    (hrec : ∀ k : ℕ, M (k + 4) = s * M (k + 3) - a * M k) :
    M 4 = s ^ 4 - a ∧
    M 5 = s ^ 5 - 2 * a * s ∧
    M 6 = s ^ 6 - 3 * a * s ^ 2 ∧
    M 7 = s ^ 7 - 4 * a * s ^ 3 ∧
    M 8 = s ^ 8 - 5 * a * s ^ 4 + a ^ 2 ∧
    M 9 = s ^ 9 - 6 * a * s ^ 5 + 3 * a ^ 2 * s ∧
    M 10 = s ^ 10 - 7 * a * s ^ 6 + 6 * a ^ 2 * s ^ 2 ∧
    M 11 = s ^ 11 - 8 * a * s ^ 7 + 10 * a ^ 2 * s ^ 3 := by
  have h4 : M 4 = s ^ 4 - a := by
    calc
      M 4 = s * M 3 - a * M 0 := by simpa using (hrec 0)
      _ = s ^ 4 - a := by rw [h3, h0]; ring
  have h5 : M 5 = s ^ 5 - 2 * a * s := by
    calc
      M 5 = s * M 4 - a * M 1 := by simpa using (hrec 1)
      _ = s ^ 5 - 2 * a * s := by rw [h4, h1]; ring
  have h6 : M 6 = s ^ 6 - 3 * a * s ^ 2 := by
    calc
      M 6 = s * M 5 - a * M 2 := by simpa using (hrec 2)
      _ = s ^ 6 - 3 * a * s ^ 2 := by rw [h5, h2]; ring
  have h7 : M 7 = s ^ 7 - 4 * a * s ^ 3 := by
    calc
      M 7 = s * M 6 - a * M 3 := by simpa using (hrec 3)
      _ = s ^ 7 - 4 * a * s ^ 3 := by rw [h6, h3]; ring
  have h8 : M 8 = s ^ 8 - 5 * a * s ^ 4 + a ^ 2 := by
    calc
      M 8 = s * M 7 - a * M 4 := by simpa using (hrec 4)
      _ = s ^ 8 - 5 * a * s ^ 4 + a ^ 2 := by rw [h7, h4]; ring
  have h9 : M 9 = s ^ 9 - 6 * a * s ^ 5 + 3 * a ^ 2 * s := by
    calc
      M 9 = s * M 8 - a * M 5 := by simpa using (hrec 5)
      _ = s ^ 9 - 6 * a * s ^ 5 + 3 * a ^ 2 * s := by rw [h8, h5]; ring
  have h10 : M 10 = s ^ 10 - 7 * a * s ^ 6 + 6 * a ^ 2 * s ^ 2 := by
    calc
      M 10 = s * M 9 - a * M 6 := by simpa using (hrec 6)
      _ = s ^ 10 - 7 * a * s ^ 6 + 6 * a ^ 2 * s ^ 2 := by rw [h9, h6]; ring
  have h11 : M 11 = s ^ 11 - 8 * a * s ^ 7 + 10 * a ^ 2 * s ^ 3 := by
    calc
      M 11 = s * M 10 - a * M 7 := by simpa using (hrec 7)
      _ = s ^ 11 - 8 * a * s ^ 7 + 10 * a ^ 2 * s ^ 3 := by rw [h10, h7]; ring
  exact ⟨h4, h5, h6, h7, h8, h9, h10, h11⟩

#print axioms OrbitTrace.quartic_trace_first_twelve

end OrbitTrace
