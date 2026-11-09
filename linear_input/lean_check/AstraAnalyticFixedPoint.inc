
/-!
Phase-3 intermediate contraction module. The nonlinear material map is the
constructed polynomial inverse, not an assumed nonlinearity. The actual
weighted mode-time product, displacement map, and Duhamel operator must still
be supplied by their construction files before this gives a PDE solution.
-/

namespace KerrKoopman.AnalyticFixedPoint

noncomputable section

open Set Metric Phase3PolynomialInverse
open scoped NNReal Topology

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

abbrev Ball (Y : Type*) [NormedAddCommGroup Y] := closedBall (0 : Y) (1 / 4)

omit [CompleteSpace X] [CompleteSpace Y] in
theorem displacement_norm_le (D : Y →L[ℝ] X) (hD : ‖D‖ ≤ 10 / 7)
    (z : Ball Y) : ‖D z.val‖ ≤ 134 / 375 := by
  have hz : ‖z.val‖ ≤ 1 / 4 := mem_closedBall_zero_iff.mp z.property
  have hb := D.le_opNorm z.val
  have hprod : ‖D‖ * ‖z.val‖ ≤ (10 / 7 : ℝ) * (1 / 4) := by gcongr
  linarith

def outerStep (B : X →L[ℝ] X →L[ℝ] X)
    (hB : ∀ x y, ‖B x y‖ ≤ ‖x‖ * ‖y‖)
    (D : Y →L[ℝ] X) (hD : ‖D‖ ≤ 10 / 7)
    (K : X →L[ℝ] Y) (L : Y) (z : Ball Y) : Y :=
  L + K (nonlinear B hB (D z.val) (displacement_norm_le D hD z))

omit [CompleteSpace Y] in
theorem outerStep_norm_le (B : X →L[ℝ] X →L[ℝ] X)
    (hB : ∀ x y, ‖B x y‖ ≤ ‖x‖ * ‖y‖)
    (D : Y →L[ℝ] X) (hD : ‖D‖ ≤ 10 / 7)
    (K : X →L[ℝ] Y) (hK : ‖K‖ ≤ 1) (L : Y) (hL : ‖L‖ ≤ 57 / 250)
    (z : Ball Y) : ‖outerStep B hB D hD K L z‖ ≤ 1 / 4 := by
  have hn := nonlinear_norm_le B hB (D z.val) (displacement_norm_le D hD z)
  have hKn : ‖K (nonlinear B hB (D z.val) (displacement_norm_le D hD z))‖ ≤ 8 / 375 := by
    apply (K.le_opNorm _).trans
    calc
      _ ≤ 1 * (8 / 375 : ℝ) := by gcongr
      _ = _ := one_mul _
  exact (norm_add_le _ _).trans (by linarith)

def outerMap (B : X →L[ℝ] X →L[ℝ] X)
    (hB : ∀ x y, ‖B x y‖ ≤ ‖x‖ * ‖y‖)
    (D : Y →L[ℝ] X) (hD : ‖D‖ ≤ 10 / 7)
    (K : X →L[ℝ] Y) (hK : ‖K‖ ≤ 1) (L : Y) (hL : ‖L‖ ≤ 57 / 250)
    (z : Ball Y) : Ball Y :=
  ⟨outerStep B hB D hD K L z,
    mem_closedBall_zero_iff.mpr (outerStep_norm_le B hB D hD K hK L hL z)⟩

omit [CompleteSpace Y] in
theorem outerStep_norm_sub_le (B : X →L[ℝ] X →L[ℝ] X)
    (hB : ∀ x y, ‖B x y‖ ≤ ‖x‖ * ‖y‖)
    (D : Y →L[ℝ] X) (hD : ‖D‖ ≤ 10 / 7)
    (K : X →L[ℝ] Y) (hK : ‖K‖ ≤ 1) (L : Y) (z w : Ball Y) :
    ‖outerStep B hB D hD K L z - outerStep B hB D hD K L w‖ ≤
      (55 / 273 : ℝ) * ‖z.val - w.val‖ := by
  let nz := nonlinear B hB (D z.val) (displacement_norm_le D hD z)
  let nw := nonlinear B hB (D w.val) (displacement_norm_le D hD w)
  have hN : ‖nz - nw‖ ≤ (11 / 78 : ℝ) * ‖D z.val - D w.val‖ :=
    nonlinear_norm_sub_le B hB _ _ _ _
  have hd : ‖D z.val - D w.val‖ ≤ (10 / 7 : ℝ) * ‖z.val - w.val‖ := by
    rw [← map_sub]
    exact (D.le_opNorm _).trans (mul_le_mul_of_nonneg_right hD (norm_nonneg _))
  change ‖(L + K nz) - (L + K nw)‖ ≤ _
  rw [add_sub_add_left_eq_sub, ← map_sub]
  have hk : ‖K (nz - nw)‖ ≤ ‖nz - nw‖ := by
    exact (K.le_opNorm _).trans (by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hK (norm_nonneg (nz - nw)))
  linarith

omit [CompleteSpace Y] in
theorem outerMap_contracting (B : X →L[ℝ] X →L[ℝ] X)
    (hB : ∀ x y, ‖B x y‖ ≤ ‖x‖ * ‖y‖)
    (D : Y →L[ℝ] X) (hD : ‖D‖ ≤ 10 / 7)
    (K : X →L[ℝ] Y) (hK : ‖K‖ ≤ 1) (L : Y) (hL : ‖L‖ ≤ 57 / 250) :
    ContractingWith (55 / 273 : ℝ≥0) (outerMap B hB D hD K hK L hL) := by
  constructor
  · norm_num
  · apply LipschitzWith.of_dist_le_mul
    intro z w
    change dist (outerStep B hB D hD K L z) (outerStep B hB D hD K L w) ≤
      ((55 / 273 : ℝ≥0) : ℝ) * dist z.val w.val
    simp only [dist_eq_norm]
    norm_num only [NNReal.coe_div, NNReal.coe_ofNat]
    exact outerStep_norm_sub_le B hB D hD K hK L z w

/-- Actual existence and convergent iteration for the assembled map. Its
eventual PDE interpretation must be proved by constructing B, D, K and L. -/
theorem exists_outer_fixedpoint (B : X →L[ℝ] X →L[ℝ] X)
    (hB : ∀ x y, ‖B x y‖ ≤ ‖x‖ * ‖y‖)
    (D : Y →L[ℝ] X) (hD : ‖D‖ ≤ 10 / 7)
    (K : X →L[ℝ] Y) (hK : ‖K‖ ≤ 1) (L : Y) (hL : ‖L‖ ≤ 57 / 250) :
    ∃ z : Ball Y, outerStep B hB D hD K L z = z.val ∧
      Filter.Tendsto
        (fun n : ℕ => ((outerMap B hB D hD K hK L hL)^[n]
          ⟨0, mem_closedBall_self (by norm_num)⟩).val)
        Filter.atTop (𝓝 z.val) := by
  letI : CompleteSpace (Ball Y) := isClosed_closedBall.isComplete.completeSpace_coe
  let z₀ : Ball Y := ⟨0, mem_closedBall_self (by norm_num)⟩
  obtain ⟨z, hf, ht, _⟩ := (outerMap_contracting B hB D hD K hK L hL).exists_fixedPoint
    z₀ (edist_ne_top _ _)
  refine ⟨z, congrArg Subtype.val hf, ?_⟩
  exact (continuous_subtype_val.tendsto z).comp ht

end

end KerrKoopman.AnalyticFixedPoint
