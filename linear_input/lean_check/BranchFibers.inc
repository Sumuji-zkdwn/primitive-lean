/-!
Finite labels, cosine collisions, and distinct real inverse images of the
existing ternary iterate. Labels and geometric states are counted separately.
-/

noncomputable section
open Real Set

namespace LinearInputBranchFibers

def candidate (d : ℕ) (t : ℝ) (j : Fin d) : ℝ :=
  cos ((t + (j : ℝ) * (2 * π)) / d)

def candidateSet (d : ℕ) (t : ℝ) : Finset ℝ := by
  classical
  exact Finset.univ.image (candidate d t)

theorem cos_eq_on_turn {a b : ℝ}
    (ha0 : 0 ≤ a) (ha2 : a < 2 * π) (hb0 : 0 ≤ b) (hb2 : b < 2 * π) :
    cos a = cos b ↔ a = b ∨ a + b = 2 * π := by
  constructor
  · intro h
    by_cases ha : a ≤ π
    · by_cases hb : b ≤ π
      · exact Or.inl (Real.injOn_cos ⟨ha0, ha⟩ ⟨hb0, hb⟩ h)
      · have he := Real.injOn_cos ⟨ha0, ha⟩
          (show 2 * π - b ∈ Icc 0 π from ⟨by linarith, by linarith⟩)
          (h.trans (Real.cos_two_pi_sub b).symm)
        exact Or.inr (by linarith)
    · by_cases hb : b ≤ π
      · have he := Real.injOn_cos
          (show 2 * π - a ∈ Icc 0 π from ⟨by linarith, by linarith⟩) ⟨hb0, hb⟩
          ((Real.cos_two_pi_sub a).trans h)
        exact Or.inr (by linarith)
      · have he := Real.injOn_cos
          (show 2 * π - a ∈ Icc 0 π from ⟨by linarith, by linarith⟩)
          (show 2 * π - b ∈ Icc 0 π from ⟨by linarith, by linarith⟩)
          ((Real.cos_two_pi_sub a).trans (h.trans (Real.cos_two_pi_sub b).symm))
        exact Or.inl (by linarith)
  · rintro (rfl | h)
    · rfl
    · rw [show b = 2 * π - a by linarith, Real.cos_two_pi_sub]

theorem candidate_angle_bounds {d : ℕ} (hd : 0 < d) {t : ℝ}
    (ht0 : 0 ≤ t) (htπ : t ≤ π) (j : Fin d) :
    0 ≤ (t + (j : ℝ) * (2 * π)) / d ∧
      (t + (j : ℝ) * (2 * π)) / d < 2 * π := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hj : (j : ℝ) + 1 ≤ d := by exact_mod_cast j.isLt
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  constructor
  · positivity
  · apply (div_lt_iff₀ hd').mpr
    nlinarith [Real.pi_pos]

/-- The only possible collision on one turn is reflection. -/
theorem candidate_eq_iff {d : ℕ} (hd : 0 < d) {t : ℝ}
    (ht0 : 0 ≤ t) (htπ : t ≤ π) (j k : Fin d) :
    candidate d t j = candidate d t k ↔
      j = k ∨ t + ((j : ℝ) + (k : ℝ)) * π = d * π := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  obtain ⟨hj0, hj2⟩ := candidate_angle_bounds hd ht0 htπ j
  obtain ⟨hk0, hk2⟩ := candidate_angle_bounds hd ht0 htπ k
  rw [candidate, candidate, cos_eq_on_turn hj0 hj2 hk0 hk2]
  constructor
  · rintro (he | he)
    · left
      have he' := (div_left_inj' hd').mp he
      have hjk : (j : ℝ) = k := by nlinarith [Real.pi_pos]
      apply Fin.ext
      exact_mod_cast hjk
    · right
      have he' : t + (j : ℝ) * (2 * π) + (t + (k : ℝ) * (2 * π)) =
          2 * π * d := by
        rw [← add_div, div_eq_iff hd'] at he
        exact he
      nlinarith
  · rintro (rfl | he)
    · exact Or.inl rfl
    · right
      rw [← add_div, div_eq_iff hd']
      nlinarith

theorem candidate_injective_regular {d : ℕ} (hd : 0 < d) {t : ℝ}
    (ht0 : 0 < t) (htπ : t < π) : Function.Injective (candidate d t) := by
  intro j k he
  rcases (candidate_eq_iff hd ht0.le htπ.le j k).mp he with h | h
  · exact h
  · have hlt : (j : ℕ) + (k : ℕ) < d := by
      have : (j : ℝ) + (k : ℝ) < d := by nlinarith [Real.pi_pos]
      exact_mod_cast this
    have hgt : d < (j : ℕ) + (k : ℕ) + 1 := by
      have : (d : ℝ) < (j : ℝ) + (k : ℝ) + 1 := by nlinarith [Real.pi_pos]
      exact_mod_cast this
    omega

theorem candidate_eq_zero_iff {d : ℕ} (hd : 0 < d) (j k : Fin d) :
    candidate d 0 j = candidate d 0 k ↔ j = k ∨ (j : ℕ) + k = d := by
  rw [candidate_eq_iff hd (le_refl 0) Real.pi_pos.le]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · right
      have : (j : ℝ) + (k : ℝ) = d := by nlinarith [Real.pi_pos]
      exact_mod_cast this
  · rintro (h | h)
    · exact Or.inl h
    · right
      have : (j : ℝ) + (k : ℝ) = d := by exact_mod_cast h
      rw [this, zero_add]

theorem candidate_eq_pi_iff {d : ℕ} (hd : 0 < d) (j k : Fin d) :
    candidate d π j = candidate d π k ↔ j = k ∨ (j : ℕ) + k + 1 = d := by
  rw [candidate_eq_iff hd Real.pi_pos.le (le_refl π)]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · right
      have : (j : ℝ) + (k : ℝ) + 1 = d := by nlinarith [Real.pi_pos]
      exact_mod_cast this
  · rintro (h | h)
    · exact Or.inl h
    · right
      have : (j : ℝ) + (k : ℝ) + 1 = d := by exact_mod_cast h
      rw [← this]
      ring

theorem candidateSet_card_regular {d : ℕ} (hd : 0 < d) {t : ℝ}
    (ht0 : 0 < t) (htπ : t < π) : (candidateSet d t).card = d := by
  classical
  rw [candidateSet, Finset.card_image_of_injective _ (candidate_injective_regular hd ht0 htπ)]
  simp

def lowLabel (m : ℕ) (j : Fin (m + 1)) : Fin (2 * m + 1) :=
  ⟨j, by have := j.isLt; omega⟩

def zeroRepresentative (m : ℕ) (j : Fin (2 * m + 1)) : Fin (m + 1) :=
  ⟨min (j : ℕ) (2 * m + 1 - j), by have := j.isLt; omega⟩

def piRepresentative (m : ℕ) (j : Fin (2 * m + 1)) : Fin (m + 1) :=
  ⟨min (j : ℕ) (2 * m - j), by have := j.isLt; omega⟩

theorem zeroRepresentative_lowLabel (m : ℕ) (j : Fin (m + 1)) :
    zeroRepresentative m (lowLabel m j) = j := by
  apply Fin.ext
  simp only [zeroRepresentative, lowLabel, Fin.val_mk]
  have := j.isLt
  omega

theorem piRepresentative_lowLabel (m : ℕ) (j : Fin (m + 1)) :
    piRepresentative m (lowLabel m j) = j := by
  apply Fin.ext
  simp only [piRepresentative, lowLabel, Fin.val_mk]
  have := j.isLt
  omega

theorem candidate_zero_representative (m : ℕ) (j : Fin (2 * m + 1)) :
    candidate (2 * m + 1) 0 (lowLabel m (zeroRepresentative m j)) =
      candidate (2 * m + 1) 0 j := by
  apply (candidate_eq_zero_iff (by omega) _ _).mpr
  simp only [lowLabel, zeroRepresentative, Fin.ext_iff, Fin.val_mk]
  have := j.isLt
  omega

theorem candidate_pi_representative (m : ℕ) (j : Fin (2 * m + 1)) :
    candidate (2 * m + 1) π (lowLabel m (piRepresentative m j)) =
      candidate (2 * m + 1) π j := by
  apply (candidate_eq_pi_iff (by omega) _ _).mpr
  simp only [lowLabel, piRepresentative, Fin.ext_iff, Fin.val_mk]
  have := j.isLt
  omega

theorem candidate_zero_low_injective (m : ℕ) :
    Function.Injective (fun j : Fin (m + 1) => candidate (2 * m + 1) 0 (lowLabel m j)) := by
  intro j k h
  have he := (candidate_eq_zero_iff (by omega) (lowLabel m j) (lowLabel m k)).mp h
  simp only [lowLabel, Fin.ext_iff, Fin.val_mk] at he
  apply Fin.ext
  have := j.isLt
  have := k.isLt
  omega

theorem candidate_pi_low_injective (m : ℕ) :
    Function.Injective (fun j : Fin (m + 1) => candidate (2 * m + 1) π (lowLabel m j)) := by
  intro j k h
  have he := (candidate_eq_pi_iff (by omega) (lowLabel m j) (lowLabel m k)).mp h
  simp only [lowLabel, Fin.ext_iff, Fin.val_mk] at he
  apply Fin.ext
  have := j.isLt
  have := k.isLt
  omega

theorem candidateSet_zero_image (m : ℕ) :
    candidateSet (2 * m + 1) 0 =
      Finset.univ.image (fun j : Fin (m + 1) => candidate (2 * m + 1) 0 (lowLabel m j)) := by
  classical
  ext x
  simp only [candidateSet, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨zeroRepresentative m j, candidate_zero_representative m j⟩
  · rintro ⟨j, rfl⟩
    exact ⟨lowLabel m j, rfl⟩

theorem candidateSet_pi_image (m : ℕ) :
    candidateSet (2 * m + 1) π =
      Finset.univ.image (fun j : Fin (m + 1) => candidate (2 * m + 1) π (lowLabel m j)) := by
  classical
  ext x
  simp only [candidateSet, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨piRepresentative m j, candidate_pi_representative m j⟩
  · rintro ⟨j, rfl⟩
    exact ⟨lowLabel m j, rfl⟩

theorem candidateSet_zero_card (m : ℕ) : (candidateSet (2 * m + 1) 0).card = m + 1 := by
  classical
  rw [candidateSet_zero_image, Finset.card_image_of_injective _ (candidate_zero_low_injective m)]
  simp

theorem candidateSet_pi_card (m : ℕ) : (candidateSet (2 * m + 1) π).card = m + 1 := by
  classical
  rw [candidateSet_pi_image, Finset.card_image_of_injective _ (candidate_pi_low_injective m)]
  simp

theorem zero_retraction_idempotent (m : ℕ) :
    ∀ j, lowLabel m (zeroRepresentative m (lowLabel m (zeroRepresentative m j))) =
      lowLabel m (zeroRepresentative m j) := by
  intro j
  simp only [zeroRepresentative_lowLabel]

theorem pi_retraction_idempotent (m : ℕ) :
    ∀ j, lowLabel m (piRepresentative m (lowLabel m (piRepresentative m j))) =
      lowLabel m (piRepresentative m j) := by
  intro j
  simp only [piRepresentative_lowLabel]

theorem three_pow_odd_form (n : ℕ) : 3 ^ n = 2 * (3 ^ n / 2) + 1 := by
  have h : 3 ^ n % 2 = 1 := by simp [Nat.pow_mod]
  omega

theorem ternary_candidates_regular_card (n : ℕ) {t : ℝ} (ht0 : 0 < t) (htπ : t < π) :
    (candidateSet (3 ^ n) t).card = 3 ^ n :=
  candidateSet_card_regular (by positivity) ht0 htπ

theorem ternary_candidates_zero_card (n : ℕ) :
    (candidateSet (3 ^ n) 0).card = (3 ^ n + 1) / 2 := by
  have h := candidateSet_zero_card (3 ^ n / 2)
  rw [← three_pow_odd_form n] at h
  have := three_pow_odd_form n
  omega

theorem ternary_candidates_pi_card (n : ℕ) :
    (candidateSet (3 ^ n) π).card = (3 ^ n + 1) / 2 := by
  have h := candidateSet_pi_card (3 ^ n / 2)
  rw [← three_pow_odd_form n] at h
  have := three_pow_odd_form n
  omega

/-- Exhaust every cosine solution, not only the displayed candidates. -/
theorem cosine_solution_has_label {d : ℕ} (hd : 0 < d) {a t : ℝ}
    (ha0 : 0 ≤ a) (haπ : a ≤ π) (ht0 : 0 ≤ t) (htπ : t ≤ π)
    (h : cos ((d : ℝ) * a) = cos t) :
    ∃ j : Fin d, candidate d t j = cos a := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hda0 : 0 ≤ (d : ℝ) * a := mul_nonneg hd'.le ha0
  have hdaπ : (d : ℝ) * a ≤ d * π := mul_le_mul_of_nonneg_left haπ hd'.le
  obtain ⟨k, hk | hk⟩ := Real.cos_eq_cos_iff.mp h.symm
  · have hklo : (-1 : ℝ) < k := by
      apply (mul_lt_mul_iff_left₀ Real.pi_pos).mp
      nlinarith [Real.pi_pos]
    have hk0 : (0 : ℤ) ≤ k := by
      have : (-1 : ℤ) < k := by exact_mod_cast hklo
      omega
    have hkhi : (k : ℝ) < d := by
      apply (mul_lt_mul_iff_left₀ Real.pi_pos).mp
      nlinarith [mul_pos hd' Real.pi_pos]
    lift k to ℕ using hk0
    simp only [Int.cast_natCast] at hk hkhi
    have hkd : k < d := by exact_mod_cast hkhi
    refine ⟨⟨k, hkd⟩, ?_⟩
    unfold candidate
    congr 1
    apply (div_eq_iff hd'.ne').mpr
    simpa only [Fin.val_mk] using (show t + (k : ℝ) * (2 * π) = a * d by nlinarith [hk])
  · have hk0 : (0 : ℤ) ≤ k := by
      have hkr : (0 : ℝ) ≤ k := by
        apply (mul_le_mul_iff_left₀ Real.pi_pos).mp
        nlinarith
      exact_mod_cast hkr
    have hkhi : (k : ℝ) ≤ d := by
      apply (mul_le_mul_iff_left₀ Real.pi_pos).mp
      nlinarith [mul_le_mul_of_nonneg_right hd1 Real.pi_pos.le]
    lift k to ℕ using hk0
    simp only [Int.cast_natCast] at hk hkhi
    have hkd : k ≤ d := by exact_mod_cast hkhi
    by_cases hkz : k = 0
    · subst k
      have ha : a = 0 := by norm_num at hk; nlinarith
      have ht : t = 0 := by rw [ha] at hk; norm_num at hk; linarith
      refine ⟨⟨0, hd⟩, ?_⟩
      simp [candidate, ha, ht]
    · have hj : d - k < d := by omega
      refine ⟨⟨d - k, hj⟩, ?_⟩
      unfold candidate
      have he : (t + ((d - k : ℕ) : ℝ) * (2 * π)) / d = 2 * π - a := by
        rw [Nat.cast_sub hkd, div_eq_iff hd'.ne']
        nlinarith [hk]
      simp only [he, Real.cos_two_pi_sub]

theorem chebyshev_gt_one {x : ℝ} (hx : 1 < x) :
    1 < LinearInputBranchForgetting.chebyshevThree x := by
  have hs : 1 < x ^ 2 := by nlinarith [sq_nonneg (x - 1)]
  have hp : 0 < x * (x ^ 2 - 1) := mul_pos (by linarith) (by linarith)
  unfold LinearInputBranchForgetting.chebyshevThree
  nlinarith

theorem ternaryIterate_gt_one (n : ℕ) {x : ℝ} (hx : 1 < x) :
    1 < LinearInputBranchForgetting.ternaryIterate n x := by
  induction n with
  | zero => exact hx
  | succ n ih => exact chebyshev_gt_one ih

theorem ternaryIterate_neg (n : ℕ) (x : ℝ) :
    LinearInputBranchForgetting.ternaryIterate n (-x) =
      -LinearInputBranchForgetting.ternaryIterate n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [LinearInputBranchForgetting.ternaryIterate, ih,
      LinearInputBranchForgetting.chebyshevThree]
    ring

theorem ternary_inverse_mem_interval (n : ℕ) {x y : ℝ}
    (hy0 : -1 ≤ y) (hy1 : y ≤ 1)
    (h : LinearInputBranchForgetting.ternaryIterate n x = y) : -1 ≤ x ∧ x ≤ 1 := by
  constructor
  · by_contra hx
    have hn : 1 < -x := by linarith
    have hh := ternaryIterate_gt_one n hn
    rw [ternaryIterate_neg, h] at hh
    linarith
  · by_contra hx
    have hh := ternaryIterate_gt_one n (show 1 < x by linarith)
    rw [h] at hh
    linarith

/-- Equality with the entire real solution set; no root is omitted. -/
theorem ternary_inverse_iff_candidate (n : ℕ) {t : ℝ}
    (ht0 : 0 ≤ t) (htπ : t ≤ π) (x : ℝ) :
    LinearInputBranchForgetting.ternaryIterate n x = cos t ↔
      x ∈ candidateSet (3 ^ n) t := by
  classical
  constructor
  · intro h
    obtain ⟨hx0, hx1⟩ := ternary_inverse_mem_interval n (Real.neg_one_le_cos t) (Real.cos_le_one t) h
    have hc := Real.cos_arccos hx0 hx1
    have he : cos (((3 ^ n : ℕ) : ℝ) * arccos x) = cos t := by
      have hh := LinearInputBranchForgetting.ternaryIterate_cos n (arccos x)
      rw [hc, h] at hh
      simpa using hh.symm
    obtain ⟨j, hj⟩ := cosine_solution_has_label (by positivity)
      (Real.arccos_nonneg x) (Real.arccos_le_pi x) ht0 htπ he
    apply Finset.mem_image.mpr
    exact ⟨j, Finset.mem_univ _, hj.trans hc⟩
  · intro h
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp h
    simpa [candidate] using LinearInputBranchForgetting.iterated_inverse_candidate n t j.val

theorem real_inverse_card_regular (n : ℕ) {y : ℝ} (hy0 : -1 < y) (hy1 : y < 1) :
    {x : ℝ | LinearInputBranchForgetting.ternaryIterate n x = y}.ncard = 3 ^ n := by
  have hs : {x : ℝ | LinearInputBranchForgetting.ternaryIterate n x = y} =
      (candidateSet (3 ^ n) (arccos y) : Set ℝ) := by
    ext x
    simpa only [Set.mem_setOf_eq, Finset.mem_coe, Real.cos_arccos hy0.le hy1.le] using
      ternary_inverse_iff_candidate n (Real.arccos_nonneg y) (Real.arccos_le_pi y) x
  rw [hs, Set.ncard_coe_finset]
  exact ternary_candidates_regular_card n (Real.arccos_pos.mpr hy1) (Real.arccos_lt_pi.mpr hy0)

theorem real_inverse_card_one (n : ℕ) :
    {x : ℝ | LinearInputBranchForgetting.ternaryIterate n x = 1}.ncard = (3 ^ n + 1) / 2 := by
  have hs : {x : ℝ | LinearInputBranchForgetting.ternaryIterate n x = 1} =
      (candidateSet (3 ^ n) 0 : Set ℝ) := by
    ext x
    simpa using ternary_inverse_iff_candidate n (le_refl 0) Real.pi_pos.le x
  rw [hs, Set.ncard_coe_finset, ternary_candidates_zero_card]

theorem real_inverse_card_neg_one (n : ℕ) :
    {x : ℝ | LinearInputBranchForgetting.ternaryIterate n x = -1}.ncard = (3 ^ n + 1) / 2 := by
  have hs : {x : ℝ | LinearInputBranchForgetting.ternaryIterate n x = -1} =
      (candidateSet (3 ^ n) π : Set ℝ) := by
    ext x
    simpa using ternary_inverse_iff_candidate n Real.pi_pos.le (le_refl π) x
  rw [hs, Set.ncard_coe_finset, ternary_candidates_pi_card]

theorem critical_depth_two_not_binary :
    {x : ℝ | LinearInputBranchForgetting.ternaryIterate 2 x = 1}.ncard ≠ 2 ^ 2 := by
  rw [real_inverse_card_one]
  norm_num

def zeroPartner (m : ℕ) (j : Fin (2 * m + 1)) : Fin (2 * m + 1) :=
  ⟨if (j : ℕ) = 0 then 0 else 2 * m + 1 - j, by
    have := j.isLt
    split_ifs <;> omega⟩

def piPartner (m : ℕ) (j : Fin (2 * m + 1)) : Fin (2 * m + 1) :=
  ⟨2 * m - j, by have := j.isLt; omega⟩

theorem zeroPartner_fixed_iff (m : ℕ) (j : Fin (2 * m + 1)) :
    zeroPartner m j = j ↔ (j : ℕ) = 0 := by
  simp only [zeroPartner, Fin.ext_iff]
  have := j.isLt
  split_ifs <;> omega

theorem piPartner_fixed_iff (m : ℕ) (j : Fin (2 * m + 1)) :
    piPartner m j = j ↔ (j : ℕ) = m := by
  simp only [piPartner, Fin.ext_iff]
  have := j.isLt
  omega

theorem zero_fiber_pair (m : ℕ) (j : Fin (2 * m + 1)) :
    Finset.univ.filter (fun k => candidate (2 * m + 1) 0 k = candidate (2 * m + 1) 0 j) =
      {j, zeroPartner m j} := by
  classical
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  rw [candidate_eq_zero_iff (by omega) k j]
  simp only [zeroPartner, Fin.ext_iff]
  have := j.isLt
  have := k.isLt
  split_ifs <;> omega

theorem pi_fiber_pair (m : ℕ) (j : Fin (2 * m + 1)) :
    Finset.univ.filter (fun k => candidate (2 * m + 1) π k = candidate (2 * m + 1) π j) =
      {j, piPartner m j} := by
  classical
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  rw [candidate_eq_pi_iff (by omega) k j]
  simp only [piPartner, Fin.ext_iff]
  have := j.isLt
  have := k.isLt
  omega

theorem zero_fiber_card (m : ℕ) (j : Fin (2 * m + 1)) :
    (Finset.univ.filter (fun k => candidate (2 * m + 1) 0 k = candidate (2 * m + 1) 0 j)).card =
      if (j : ℕ) = 0 then 1 else 2 := by
  classical
  rw [zero_fiber_pair]
  by_cases h : (j : ℕ) = 0
  · rw [(zeroPartner_fixed_iff m j).mpr h]
    simp [h]
  · have hp : j ≠ zeroPartner m j := Ne.symm (mt (zeroPartner_fixed_iff m j).mp h)
    simp [h, hp]

theorem pi_fiber_card (m : ℕ) (j : Fin (2 * m + 1)) :
    (Finset.univ.filter (fun k => candidate (2 * m + 1) π k = candidate (2 * m + 1) π j)).card =
      if (j : ℕ) = m then 1 else 2 := by
  classical
  rw [pi_fiber_pair]
  by_cases h : (j : ℕ) = m
  · rw [(piPartner_fixed_iff m j).mpr h]
    simp [h]
  · have hp : j ≠ piPartner m j := Ne.symm (mt (piPartner_fixed_iff m j).mp h)
    simp [h, hp]

theorem critical_candidate_collision :
    candidate 3 0 ⟨1, by decide⟩ = candidate 3 0 ⟨2, by decide⟩ := by
  apply (candidate_eq_zero_iff (by decide) _ _).mpr
  exact Or.inr (by decide)

end LinearInputBranchFibers
