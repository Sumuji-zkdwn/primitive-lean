import Research.SiphonPolynomialE
import OrbitTrace

/-!
# Five tangent-coordinate observations identify a siphon state

Every observation here is the squared first coordinate. The probability
p₁(z) = 1/(1+9*z.1^4) carries precisely the same information.
E and L are the existing maps; no new axioms or analytic assumptions.
-/

namespace SiphonTangentObservation

open Elastica.SiphonPolynomialE

private def afterEL (u r : ℝ) : ℝ :=
  let v := r - u ^ 3
  v + (v - u + v ^ 3) ^ 2

private theorem afterEL_zero (u : ℝ) :
    afterEL u 0 = -u ^ 3 + (u + u ^ 3 + u ^ 9) ^ 2 := by
  dsimp [afterEL]
  ring

private theorem afterEL_zero_neg (u : ℝ) :
    afterEL (-u) 0 = u ^ 3 + (u + u ^ 3 + u ^ 9) ^ 2 := by
  dsimp [afterEL]
  ring

private theorem afterEL_at_zero (r : ℝ) :
    afterEL 0 r = r + (r + r ^ 3) ^ 2 := by
  dsimp [afterEL]
  ring

private theorem afterEL_at_zero_neg (r : ℝ) :
    afterEL 0 (-r) = -r + (r + r ^ 3) ^ 2 := by
  dsimp [afterEL]
  ring

private theorem square_eq_split (a b : ℝ) (h : a ^ 2 = b ^ 2) :
    a = b ∨ a = -b := by
  have hf : (a - b) * (a + b) = 0 := by nlinarith only [h]
  rcases mul_eq_zero.mp hf with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (by linarith)

/-- Over invariant coordinates (u,r), five squared reads determine both coordinates. -/
private theorem five_square_core
    (u r x s : ℝ)
    (h0 : u ^ 2 = x ^ 2)
    (h1 : (u + r ^ 2) ^ 2 = (x + s ^ 2) ^ 2)
    (h2 : (u + 2 * r ^ 2) ^ 2 = (x + 2 * s ^ 2) ^ 2)
    (hL : (r - u ^ 3) ^ 2 = (s - x ^ 3) ^ 2)
    (hEL : (afterEL u r) ^ 2 = (afterEL x s) ^ 2) :
    u = x ∧ r = s := by
  have hr4 : r ^ 4 = s ^ 4 := by nlinarith only [h0, h1, h2]
  have hr2 : r ^ 2 = s ^ 2 := by
    have hf : (r ^ 2 - s ^ 2) * (r ^ 2 + s ^ 2) = 0 := by
      nlinarith only [hr4]
    rcases mul_eq_zero.mp hf with h | h
    · linarith
    · nlinarith [sq_nonneg r, sq_nonneg s]
  by_cases hr : r = 0
  · have hs2 : s ^ 2 = 0 := by simpa [hr] using hr2.symm
    have hs : s = 0 := by
      by_contra hne
      exact (pow_ne_zero 2 hne) hs2
    subst r
    subst s
    rcases square_eq_split u x h0 with hux | hneg
    · exact ⟨hux, rfl⟩
    · by_cases hu : u = 0
      · have hx : x = 0 := by linarith
        exact ⟨by rw [hu, hx], rfl⟩
      · have hx : x = -u := by linarith
        rw [hx, afterEL_zero, afterEL_zero_neg] at hEL
        have hfac : u + u ^ 3 + u ^ 9 = u * (1 + u ^ 2 + u ^ 8) := by ring
        have hq : u + u ^ 3 + u ^ 9 ≠ 0 := by
          rw [hfac]
          exact mul_ne_zero hu (by positivity)
        have hp : u ^ 3 * (u + u ^ 3 + u ^ 9) ^ 2 = 0 := by
          nlinarith only [hEL]
        exact False.elim ((mul_ne_zero (pow_ne_zero 3 hu) (pow_ne_zero 2 hq)) hp)
  · have h1' : (u + r ^ 2) ^ 2 = (x + r ^ 2) ^ 2 := by
      simpa only [← hr2] using h1
    have hm : (u - x) * r ^ 2 = 0 := by nlinarith only [h0, h1']
    have hu : u = x := by
      have hz : u - x = 0 := (mul_eq_zero.mp hm).resolve_right (pow_ne_zero 2 hr)
      linarith
    subst x
    rcases square_eq_split r s hr2 with hsame | hneg
    · exact ⟨rfl, hsame⟩
    · have hs : s = -r := by linarith
      by_cases hu0 : u = 0
      · subst u
        rw [hs, afterEL_at_zero, afterEL_at_zero_neg] at hEL
        have hfac : r + r ^ 3 = r * (1 + r ^ 2) := by ring
        have hq : r + r ^ 3 ≠ 0 := by
          rw [hfac]
          exact mul_ne_zero hr (by positivity)
        have hp : r * (r + r ^ 3) ^ 2 = 0 := by
          nlinarith only [hEL]
        exact False.elim ((mul_ne_zero hr (pow_ne_zero 2 hq)) hp)
      · rw [hs] at hL
        have hp : r * u ^ 3 = 0 := by nlinarith only [hL]
        exact False.elim ((mul_ne_zero hr (pow_ne_zero 3 hu0)) hp)

/-- Squared coordinate reading, monotonically equivalent to the first
probability weight of the invariant-curve tangent. -/
def squareRead (z : ℝ × ℝ) : ℝ := z.1 ^ 2

private theorem read_E (z : ℝ × ℝ) :
    squareRead (E z) = (z.1 + I z ^ 2) ^ 2 := rfl

private theorem read_E2 (z : ℝ × ℝ) :
    squareRead (E (E z)) = (z.1 + 2 * I z ^ 2) ^ 2 := by
  calc
    squareRead (E (E z)) = ((E z).1 + I (E z) ^ 2) ^ 2 := rfl
    _ = (z.1 + 2 * I z ^ 2) ^ 2 := by rw [I_E]; dsimp [E]; ring

private theorem read_L (z : ℝ × ℝ) :
    squareRead (OrbitTrace.linearE z) = (I z - z.1 ^ 3) ^ 2 := by
  rcases z with ⟨u,v⟩
  dsimp [squareRead, OrbitTrace.linearE, I]
  ring

private theorem read_EL (z : ℝ × ℝ) :
    squareRead (E (OrbitTrace.linearE z)) = (afterEL z.1 (I z)) ^ 2 := by
  rcases z with ⟨u,v⟩
  dsimp [squareRead, E, OrbitTrace.linearE, I, afterEL]
  ring

/-- Five squared coordinate observations suffice to distinguish every real
state, even though each individual reading forgets the coordinate sign. -/
theorem five_square_reads_injective (z w : ℝ × ℝ)
    (h0 : squareRead z = squareRead w)
    (h1 : squareRead (E z) = squareRead (E w))
    (h2 : squareRead (E (E z)) = squareRead (E (E w)))
    (hL : squareRead (OrbitTrace.linearE z) = squareRead (OrbitTrace.linearE w))
    (hEL : squareRead (E (OrbitTrace.linearE z)) =
           squareRead (E (OrbitTrace.linearE w))) : z = w := by
  have hc := five_square_core z.1 (I z) w.1 (I w)
    (by simpa [squareRead] using h0)
    (by simpa only [read_E] using h1)
    (by simpa only [read_E2] using h2)
    (by simpa only [read_L] using hL)
    (by simpa only [read_EL] using hEL)
  obtain ⟨hu, hr⟩ := hc
  apply Prod.ext
  · exact hu
  · dsimp [I] at hr
    rw [hu] at hr
    linarith

/-- First probability weight of the tangent-minor distribution. -/
noncomputable def probRead (z : ℝ × ℝ) : ℝ := 1 / (1 + 9 * z.1 ^ 4)

private theorem prob_eq_implies_square_eq (z w : ℝ × ℝ)
    (h : probRead z = probRead w) : squareRead z = squareRead w := by
  have ha : 1 + 9 * z.1 ^ 4 ≠ (0 : ℝ) := by positivity
  have hb : 1 + 9 * w.1 ^ 4 ≠ (0 : ℝ) := by positivity
  have hf : z.1 ^ 4 = w.1 ^ 4 := by
    unfold probRead at h
    field_simp [ha, hb] at h
    nlinarith only [h]
  have hp : (z.1 ^ 2 - w.1 ^ 2) * (z.1 ^ 2 + w.1 ^ 2) = 0 := by
    nlinarith only [hf]
  rcases mul_eq_zero.mp hp with hdiff | hsum
  · dsimp [squareRead]
    linarith
  · dsimp [squareRead]
    nlinarith [sq_nonneg z.1, sq_nonneg w.1]

/-- The actual probability-only observation map is injective. -/
theorem five_probability_reads_injective (z w : ℝ × ℝ)
    (h0 : probRead z = probRead w)
    (h1 : probRead (E z) = probRead (E w))
    (h2 : probRead (E (E z)) = probRead (E (E w)))
    (hL : probRead (OrbitTrace.linearE z) = probRead (OrbitTrace.linearE w))
    (hEL : probRead (E (OrbitTrace.linearE z)) =
           probRead (E (OrbitTrace.linearE w))) : z = w := by
  exact five_square_reads_injective z w
    (prob_eq_implies_square_eq _ _ h0)
    (prob_eq_implies_square_eq _ _ h1)
    (prob_eq_implies_square_eq _ _ h2)
    (prob_eq_implies_square_eq _ _ hL)
    (prob_eq_implies_square_eq _ _ hEL)

end SiphonTangentObservation

#print axioms SiphonTangentObservation.five_square_reads_injective
#print axioms SiphonTangentObservation.five_probability_reads_injective
