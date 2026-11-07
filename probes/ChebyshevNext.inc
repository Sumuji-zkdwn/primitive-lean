/-!
Rational-function and degree lemmas toward the generic Chebyshev Galois group.
Exploratory probe: only promote claims into registered source after the pinned
Lean compiler verifies them. All proofs must be kernel-checked with the pinned toolchain.
-/
noncomputable section
namespace LinearInputChebyshevNext

open Polynomial
open LinearInputChebyshevDescent

theorem cubicPoly_natDegree :
    (cubicPoly (K := ℂ)).natDegree = 3 := by
  unfold cubicPoly
  compute_degree
  · norm_num
  · omega

theorem chebyPoly_natDegree (k : ℕ) :
    (chebyPoly (K := ℂ) k).natDegree = 3 ^ k := by
  induction k with
  | zero => simp [chebyPoly]
  | succ k ih =>
    change ((cubicPoly (K := ℂ)).comp (chebyPoly k)).natDegree = 3 ^ (k + 1)
    rw [Polynomial.natDegree_comp, cubicPoly_natDegree, ih, pow_succ]
    omega

/-- A rational-function indeterminate has square outside the constant field. -/
theorem generic_square_not_constant (c : ℂ) :
    (RatFunc.X : RatFunc ℂ) ^ 2 ≠ RatFunc.C c := by
  intro hc
  have hdeg : (Polynomial.X ^ 2 - Polynomial.C c : Polynomial ℂ).natDegree = 2 := by
    compute_degree; norm_num
  have hpoly : (Polynomial.X ^ 2 - Polynomial.C c : Polynomial ℂ) ≠ 0 := by
    intro hh
    rw [hh] at hdeg
    norm_num at hdeg
  have hzero :
      Polynomial.aeval (RatFunc.X : RatFunc ℂ)
        (Polynomial.X ^ 2 - Polynomial.C c) = 0 := by
    simpa using (sub_eq_zero.mpr hc)
  exact hpoly ((transcendental_iff.mp (RatFunc.transcendental_X (K := ℂ))) _ hzero)


/-- Collision of the inversion quotient over the rational-function field. -/
theorem joukowski_eq_iff_rf (a b : RatFunc ℂ)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    joukowski a = joukowski b ↔ a = b ∨ a * b = 1 := by
  have hab : 2 * a * b ≠ (0 : RatFunc ℂ) :=
    mul_ne_zero (mul_ne_zero (by norm_num) ha) hb
  have hf : (joukowski a - joukowski b) * (2 * a * b) =
      (a - b) * (a * b - 1) := by
    unfold joukowski
    field_simp [ha, hb]
    ring
  constructor
  · intro h
    rw [h, sub_self, zero_mul] at hf
    rcases mul_eq_zero.mp hf.symm with hleft | hright
    · exact Or.inl (sub_eq_zero.mp hleft)
    · exact Or.inr (sub_eq_zero.mp hright)
  · rintro (h | h)
    · rw [h]
    · have hprod : (a - b) * (a * b - 1) = 0 := by
        rw [h]
        ring
      have hf' := hf.trans hprod
      exact sub_eq_zero.mp ((mul_eq_zero.mp hf').resolve_right hab)

/-- For a transcendental rational variable, the primitive radical labels
of a fixed order are pairwise distinct on the standard index interval. -/
theorem generic_candidate_injective (m : ℕ) (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ m) (hm : m ≠ 0)
    (j k : ℕ) (hj : j < m) (hk : k < m) (hjk : j ≠ k) :
    rootCandidate (RatFunc.C ζ) (RatFunc.X : RatFunc ℂ) j ≠
      rootCandidate (RatFunc.C ζ) (RatFunc.X : RatFunc ℂ) k := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hm
  have hc0 : RatFunc.C ζ ≠ (0 : RatFunc ℂ) :=
    by simpa only [map_zero] using (RatFunc.C (K := ℂ)).injective.ne hζ0
  have hz : (RatFunc.X : RatFunc ℂ) ≠ 0 := RatFunc.X_ne_zero
  have haj : (RatFunc.C ζ) ^ j * RatFunc.X ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hc0) hz
  have hak : (RatFunc.C ζ) ^ k * RatFunc.X ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hc0) hz
  intro h
  have hcase := (joukowski_eq_iff_rf _ _ haj hak).mp h
  rcases hcase with heq | hprod
  · have hp : (RatFunc.C ζ : RatFunc ℂ) ^ j =
        (RatFunc.C ζ : RatFunc ℂ) ^ k :=
      (mul_right_cancel₀ hz) heq
    have hp' : ζ ^ j = ζ ^ k := (RatFunc.C (K := ℂ)).injective (by
      simpa only [map_pow] using hp)
    exact hjk (hζ.pow_inj hj hk hp')
  · have hprod' : (RatFunc.C (ζ ^ (j + k))) *
        (RatFunc.X : RatFunc ℂ) ^ 2 = 1 := by
      calc
        RatFunc.C (ζ ^ (j + k)) * RatFunc.X ^ 2 =
            ((RatFunc.C ζ) ^ j * RatFunc.X) *
              ((RatFunc.C ζ) ^ k * RatFunc.X) := by
                simp only [pow_add, map_mul, map_pow]
                ring
        _ = 1 := hprod
    have hh : ζ ^ (j + k) ≠ 0 := pow_ne_zero _ hζ0
    have hhC : RatFunc.C (ζ ^ (j + k)) ≠ (0 : RatFunc ℂ) :=
      by simpa only [map_zero] using (RatFunc.C (K := ℂ)).injective.ne hh
    have hsq : (RatFunc.X : RatFunc ℂ) ^ 2 =
        1 / RatFunc.C (ζ ^ (j + k)) :=
      (eq_div_iff hhC).2 (by simpa only [mul_comm] using hprod')
    apply generic_square_not_constant ((ζ ^ (j + k))⁻¹)
    simpa only [map_inv₀, one_div] using hsq

end LinearInputChebyshevNext
