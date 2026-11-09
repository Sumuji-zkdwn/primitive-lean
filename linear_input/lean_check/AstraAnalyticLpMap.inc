
/-! Analytic construction: an actual uniformly bounded diagonal map on l1. -/

namespace KerrKoopman.AnalyticLpMap

noncomputable section

open scoped ENNReal

variable {ι A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

abbrev L1 (ι A : Type*) [NormedAddCommGroup A] := lp (fun _ : ι => A) 1

omit [NormedSpace ℝ A] in
theorem summable_norm (u : L1 ι A) : Summable (fun i => ‖u i‖) := by
  simpa using u.2.summable

omit [NormedSpace ℝ A] in
theorem norm_eq_tsum (u : L1 ι A) : ‖u‖ = ∑' i, ‖u i‖ := by
  simpa using lp.norm_eq_tsum_rpow (p := 1) (by norm_num) u

theorem map_mem (F : ι → A →L[ℝ] B) (C : ℝ) (hF : ∀ i, ‖F i‖ ≤ C)
    (u : L1 ι A) : Memℓp (fun i => F i (u i)) 1 := by
  apply (memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)).mpr
  simpa using Summable.of_nonneg_of_le (fun i => norm_nonneg (F i (u i)))
    (fun i => ((F i).le_opNorm (u i)).trans
      (mul_le_mul_of_nonneg_right (hF i) (norm_nonneg _)))
    ((summable_norm u).mul_left C)

def mapLinear (F : ι → A →L[ℝ] B) (C : ℝ) (hF : ∀ i, ‖F i‖ ≤ C) :
    L1 ι A →ₗ[ℝ] L1 ι B where
  toFun u := ⟨fun i => F i (u i), map_mem F C hF u⟩
  map_add' u v := by
    apply Subtype.ext
    funext i
    exact map_add (F i) (u i) (v i)
  map_smul' c u := by
    apply Subtype.ext
    funext i
    exact map_smul (F i) c (u i)

theorem mapLinear_apply (F : ι → A →L[ℝ] B) (C : ℝ) (hF : ∀ i, ‖F i‖ ≤ C)
    (u : L1 ι A) (i : ι) : mapLinear F C hF u i = F i (u i) := rfl

theorem mapLinear_norm_le (F : ι → A →L[ℝ] B) (C : ℝ) (hF : ∀ i, ‖F i‖ ≤ C)
    (u : L1 ι A) : ‖mapLinear F C hF u‖ ≤ C * ‖u‖ := by
  rw [norm_eq_tsum, norm_eq_tsum]
  calc
    _ ≤ ∑' i, C * ‖u i‖ := Summable.tsum_le_tsum
      (fun i => ((F i).le_opNorm (u i)).trans
        (mul_le_mul_of_nonneg_right (hF i) (norm_nonneg _)))
      (summable_norm (mapLinear F C hF u)) ((summable_norm u).mul_left C)
    _ = C * ∑' i, ‖u i‖ := tsum_mul_left

/-- Coordinatewise application, bundled as a continuous linear map. -/
def diagonal (F : ι → A →L[ℝ] B) (C : ℝ) (hF : ∀ i, ‖F i‖ ≤ C) :
    L1 ι A →L[ℝ] L1 ι B :=
  (mapLinear F C hF).mkContinuous C (mapLinear_norm_le F C hF)

theorem diagonal_apply (F : ι → A →L[ℝ] B) (C : ℝ) (hF : ∀ i, ‖F i‖ ≤ C)
    (u : L1 ι A) (i : ι) : diagonal F C hF u i = F i (u i) := rfl

theorem diagonal_norm_le (F : ι → A →L[ℝ] B) (C : ℝ) (hF : ∀ i, ‖F i‖ ≤ C)
    (u : L1 ι A) : ‖diagonal F C hF u‖ ≤ C * ‖u‖ := mapLinear_norm_le F C hF u

theorem diagonal_opNorm_le (F : ι → A →L[ℝ] B) (C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ i, ‖F i‖ ≤ C) : ‖diagonal F C hF‖ ≤ C :=
  (diagonal F C hF).opNorm_le_bound hC (diagonal_norm_le F C hF)

end

end KerrKoopman.AnalyticLpMap
