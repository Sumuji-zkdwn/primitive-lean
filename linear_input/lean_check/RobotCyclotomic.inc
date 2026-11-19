/-!
For a primitive root of prime-power order, a rational polynomial of degree
below the order vanishes exactly when its coefficient vector repeats in blocks.
The quotient by the cyclotomic polynomial recovers the common block.
-/

noncomputable section
namespace LinearInputRobotCyclotomic

open Polynomial
open scoped BigOperators Polynomial

private theorem block_coeff {q d : ℕ} (hd : 0 < d) (B : ℚ[X])
    (hB : B.natDegree < d) (i : ℕ) (hi : i < q * d) :
    ((∑ j ∈ Finset.range q, (X : ℚ[X]) ^ (d * j)) * B).coeff i =
      B.coeff (i % d) := by
  rw [Finset.sum_mul, finsetSum_coeff, Finset.sum_eq_single (i / d)]
  · simp only [coeff_X_pow_mul', Nat.mul_div_le, ↓reduceIte]
    have hm := Nat.mod_add_div i d
    congr 1
    omega
  · intro j hj hjne
    rw [coeff_X_pow_mul']
    split_ifs with hjle
    · apply coeff_eq_zero_of_natDegree_lt
      have hjlt : j < i / d := lt_of_le_of_ne ((Nat.le_div_iff_mul_le hd).mpr (by simpa [Nat.mul_comm] using hjle)) hjne
      have hb := Nat.mul_le_mul_left d (show j + 1 ≤ i / d from hjlt)
      have hc := Nat.mul_div_le i d
      rw [Nat.mul_add, Nat.mul_one] at hb
      omega
    · rfl
  · intro h
    exact (h (Finset.mem_range.mpr ((Nat.div_lt_iff_lt_mul hd).mpr hi))).elim

/-- Any nonnegative edge counts, indexed by heading. The final position is
zero precisely when all counts in each residue class modulo `q^a` agree. -/
theorem sum_zero_iff_periodic (q a : ℕ) (hq : q.Prime) {ζ : ℂ}
    (hz : IsPrimitiveRoot ζ (q ^ (a + 1))) (c : ℕ → ℕ) :
    (∑ i ∈ Finset.range (q ^ (a + 1)), (c i : ℂ) * ζ ^ i) = 0 ↔
      ∀ i < q ^ (a + 1), c i = c (i % q ^ a) := by
  let d := q ^ a
  let N := q ^ (a + 1)
  have hd : 0 < d := pow_pos hq.pos _
  have hN : 0 < N := pow_pos hq.pos _
  have hsize : N = q * d := pow_succ' q a
  have hdle : d ≤ N := by rw [hsize]; exact Nat.le_mul_of_pos_left _ hq.pos
  let P := ofFn N (fun i => (c i.val : ℚ))
  have hcoeff (i : ℕ) (hi : i < N) : P.coeff i = c i := ofFn_coeff_eq_val_of_lt _ hi
  have heval : aeval ζ P = ∑ i ∈ Finset.range N, (c i : ℂ) * ζ ^ i := by
    simp [P, ofFn_eq_sum_monomial, ← Fin.sum_univ_eq_sum_range, aeval_monomial]
  change (∑ i ∈ Finset.range N, (c i : ℂ) * ζ ^ i) = 0 ↔ ∀ i < N, c i = c (i % d)
  rw [← heval, ← minpoly.dvd_iff, ← cyclotomic_eq_minpoly_rat hz hN]
  have hphi : cyclotomic N ℚ = ∑ j ∈ Finset.range q, (X : ℚ[X]) ^ (d * j) := by
    simp only [N, d, cyclotomic_prime_pow_eq_geom_sum hq, pow_mul]
  constructor
  · rintro ⟨B, hPB⟩
    have hB : B.natDegree < d := by
      by_cases h0 : B = 0
      · simpa [h0] using hd
      have h := ofFn_natDegree_lt (v := fun i : Fin N => (c i.val : ℚ)) hN
      change P.natDegree < N at h
      rw [hPB, natDegree_mul (cyclotomic_ne_zero _ _) h0,
        natDegree_cyclotomic, Nat.totient_prime_pow hq (Nat.succ_pos a)] at h
      have hsplit : (q - 1) * d + d = N := by rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hq.one_le, hsize]
      dsimp [d] at hsplit ⊢
      simp only [Nat.add_one_sub_one] at h
      nlinarith [Nat.mul_comm (q ^ a) (q - 1)]
    have hb (i : ℕ) (hi : i < N) : (c i : ℚ) = B.coeff (i % d) := by
      rw [← hcoeff i hi, hPB, hphi]
      exact block_coeff hd B hB i (hsize ▸ hi)
    intro i hi
    have hmod := Nat.mod_lt i hd
    have heq := hb (i % d) (lt_of_lt_of_le hmod hdle)
    rw [Nat.mod_eq_of_lt hmod] at heq
    exact_mod_cast (hb i hi).trans heq.symm
  · intro hc
    let B := ofFn d (fun i => (c i.val : ℚ))
    have hB : B.natDegree < d := ofFn_natDegree_lt hd _
    refine ⟨B, ?_⟩
    ext i
    by_cases hi : i < N
    · rw [hcoeff i hi, hphi, block_coeff hd B hB i (hsize ▸ hi)]
      simp only [B, ofFn_coeff_eq_val_of_lt _ (Nat.mod_lt i hd), hc i hi]
    · have hphiDeg : (cyclotomic N ℚ * B).natDegree < N := by
        have hle : (cyclotomic N ℚ * B).natDegree ≤ _ := natDegree_mul_le
        rw [natDegree_cyclotomic, Nat.totient_prime_pow hq (Nat.succ_pos a)] at hle
        have hsplit : (q - 1) * d + d = N := by rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hq.one_le, hsize]
        simp only [Nat.add_one_sub_one] at hle
        dsimp [d] at hsplit hB
        nlinarith [Nat.mul_comm (q ^ a) (q - 1)]
      rw [show P.coeff i = 0 from ofFn_coeff_eq_zero_of_ge _ (by omega),
        coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hphiDeg (by omega))]

end LinearInputRobotCyclotomic
end
