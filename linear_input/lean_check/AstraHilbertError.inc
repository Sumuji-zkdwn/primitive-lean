
/-!
# Actual local error of the explicit shear step

These estimates compare the explicit algebraic step with the global solution
constructed in HilbertFlow. Neither existence nor the local defect is assumed.
Only global Lipschitz continuity of the material map is used.
-/

namespace KerrKoopman.HilbertError

noncomputable section

open Set HilbertFlow HilbertShear
open scoped NNReal Topology

theorem exp_sub_one_le (r : ℝ) : Real.exp r - 1 ≤ r * Real.exp r := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-r)) (Real.exp_nonneg r)
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
  nlinarith

theorem gronwall_zero_le (K C t : ℝ) (hK : 0 ≤ K) (hC : 0 ≤ C) :
    gronwallBound 0 K C t ≤ C * t * Real.exp (K * t) := by
  by_cases hK0 : K = 0
  · subst K
    simp [gronwallBound_K0]
  · simp only [gronwallBound_of_K_ne_0 hK0, zero_mul, zero_add]
    calc
      C / K * (Real.exp (K * t) - 1) ≤ C / K * (K * t * Real.exp (K * t)) :=
        mul_le_mul_of_nonneg_left (exp_sub_one_le _) (div_nonneg hC hK)
      _ = C * t * Real.exp (K * t) := by field_simp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem flow_displacement_le {F : E → E} {K : ℝ≥0}
    (hF : LipschitzWith K F) (t : ℝ) (ht : 0 ≤ t) (x : E) :
    ‖globalFlow hF t x - x‖ ≤ ‖F x‖ * t * Real.exp ((K : ℝ) * t) := by
  let u : ℝ → E := fun s => globalFlow hF s x - x
  have hu (s : ℝ) : HasDerivAt u (F (globalFlow hF s x)) s :=
    (hasDerivAt_globalFlow hF s x).sub_const x
  have hb (s : ℝ) : ‖F (globalFlow hF s x)‖ ≤ (K : ℝ) * ‖u s‖ + ‖F x‖ := by
    calc
      _ ≤ ‖F (globalFlow hF s x) - F x‖ + ‖F x‖ := norm_le_norm_sub_add _ _
      _ ≤ (K : ℝ) * ‖u s‖ + ‖F x‖ := by
        gcongr
        exact hF.norm_sub_le _ _
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := u) (f' := fun s => F (globalFlow hF s x))
    (δ := 0) (K := (K : ℝ)) (ε := ‖F x‖)
    (fun s _ => (hu s).continuousAt.continuousWithinAt)
    (fun s _ => (hu s).hasDerivWithinAt)
    (show ‖u 0‖ ≤ 0 by simp [u, globalFlow_zero])
    (fun s _ => hb s) t ⟨ht, le_rfl⟩
  have hg' : ‖u t‖ ≤ gronwallBound 0 (K : ℝ) ‖F x‖ t := by
    simpa only [sub_zero] using hg
  exact hg'.trans (gronwall_zero_le (K : ℝ) ‖F x‖ t K.coe_nonneg (norm_nonneg _))

/-- The actual flow differs from its first Euler step by at most the stated
quadratic bound, with the initial field norm instead of the state norm. -/
theorem flow_euler_error_le {F : E → E} {K : ℝ≥0}
    (hF : LipschitzWith K F) (t : ℝ) (ht : 0 ≤ t) (x : E) :
    ‖globalFlow hF t x - (x + t • F x)‖ ≤
      (1 / 2 : ℝ) * (K : ℝ) * t ^ 2 * Real.exp ((K : ℝ) * t) * ‖F x‖ := by
  let C : ℝ := (K : ℝ) * Real.exp ((K : ℝ) * t) * ‖F x‖
  let u : ℝ → E := fun s => globalFlow hF s x - (x + s • F x)
  have hu (s : ℝ) : HasDerivAt u (F (globalFlow hF s x) - F x) s := by
    convert (hasDerivAt_globalFlow hF s x).sub
      (((hasDerivAt_id s).smul_const (F x)).const_add x) using 1
    · rfl
    · simp
  have hB (s : ℝ) : HasDerivAt (fun r : ℝ => C / 2 * r ^ 2) (C * s) s := by
    convert ((hasDerivAt_id s).pow 2).const_mul (C / 2) using 1
    · rfl
    · simp only [id_eq]
      ring
  have hb (s : ℝ) (hs : s ∈ Ico 0 t) :
      ‖F (globalFlow hF s x) - F x‖ ≤ C * s := by
    calc
      _ ≤ (K : ℝ) * ‖globalFlow hF s x - x‖ := hF.norm_sub_le _ _
      _ ≤ (K : ℝ) * (‖F x‖ * s * Real.exp ((K : ℝ) * s)) :=
        mul_le_mul_of_nonneg_left (flow_displacement_le hF s hs.1 x) K.coe_nonneg
      _ ≤ (K : ℝ) * (‖F x‖ * s * Real.exp ((K : ℝ) * t)) := by
        apply mul_le_mul_of_nonneg_left _ K.coe_nonneg
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (norm_nonneg _) hs.1)
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs.2.le K.coe_nonneg)
      _ = C * s := by dsimp [C]; ring
  have hg := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := u) (f' := fun s => F (globalFlow hF s x) - F x)
    (a := 0) (b := t) (B := fun r : ℝ => C / 2 * r ^ 2) (B' := fun r => C * r)
    (fun s _ => (hu s).continuousAt.continuousWithinAt)
    (fun s _ => (hu s).hasDerivWithinAt)
    (by simp [u, globalFlow_zero]) hB hb (show t ∈ Icc 0 t from ⟨ht, le_rfl⟩)
  change ‖u t‖ ≤ _
  convert hg using 1
  dsimp [C]
  ring

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Exact algebraic identity: the split step's Euler defect is confined to the
second component. -/
theorem lieStep_euler_difference (Q : V →L[ℝ] V) (G : V → V)
    (t : ℝ) (z : State V) :
    lieStep Q G t z - (z + t • field Q G z) =
      WithLp.toLp 2 (0, -t • Q (G (z.fst - t • Q z.snd) - G z.fst)) := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · change z.fst - t • Q z.snd - (z.fst + t • -Q z.snd) = 0
    simp only [smul_neg]
    abel
  · change z.snd - t • Q (G (z.fst - t • Q z.snd)) -
      (z.snd + t • -Q (G z.fst)) = -t • Q (G (z.fst - t • Q z.snd) - G z.fst)
    simp only [map_sub, smul_sub, neg_smul, smul_neg]
    abel

theorem lieStep_euler_error_le (Q : V →L[ℝ] V) (G : V → V)
    (hG : LipschitzWith 1 G) (t : ℝ) (ht : 0 ≤ t) (z : State V) :
    ‖lieStep Q G t z - (z + t • field Q G z)‖ ≤
      ‖Q‖ * t ^ 2 * ‖field Q G z‖ := by
  rw [lieStep_euler_difference, WithLp.norm_toLp_snd, norm_smul,
    Real.norm_eq_abs, abs_neg, abs_of_nonneg ht]
  have hGd : ‖G (z.fst - t • Q z.snd) - G z.fst‖ ≤ t * ‖Q z.snd‖ := by
    have hg := hG.norm_sub_le (z.fst - t • Q z.snd) z.fst
    simpa only [NNReal.coe_one, one_mul, sub_sub_cancel_left, norm_neg,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg ht] using hg
  have hQH : ‖Q z.snd‖ ≤ ‖field Q G z‖ := by
    have h := WithLp.norm_fst_le V (field Q G z)
    change ‖-Q z.snd‖ ≤ _ at h
    simpa only [norm_neg] using h
  calc
    _ ≤ t * (‖Q‖ * ‖G (z.fst - t • Q z.snd) - G z.fst‖) := by
      exact mul_le_mul_of_nonneg_left (Q.le_opNorm _) ht
    _ ≤ t * (‖Q‖ * (t * ‖field Q G z‖)) := by
      gcongr
      exact hGd.trans (mul_le_mul_of_nonneg_left hQH ht)
    _ = ‖Q‖ * t ^ 2 * ‖field Q G z‖ := by ring

/-- Proven local error against the actual global solution. -/
theorem lieStep_flow_error_le [CompleteSpace V] (Q : V →L[ℝ] V) (G : V → V)
    (hG : LipschitzWith 1 G) (t : ℝ) (ht : 0 ≤ t) (z : State V) :
    ‖lieStep Q G t z - flow Q G hG t z‖ ≤
      (3 / 2 : ℝ) * ‖Q‖ * t ^ 2 * Real.exp (‖Q‖ * t) * ‖field Q G z‖ := by
  have he := flow_euler_error_le (field_lipschitz Q G hG) t ht z
  have hs := lieStep_euler_error_le Q G hG t ht z
  have htriangle := dist_triangle (lieStep Q G t z) (z + t • field Q G z)
    (flow Q G hG t z)
  simp only [dist_eq_norm] at htriangle
  rw [norm_sub_rev (z + t • field Q G z)] at htriangle
  have hexp : 1 ≤ Real.exp (‖Q‖ * t) := Real.one_le_exp_iff.mpr (mul_nonneg (norm_nonneg _) ht)
  have hbase : 0 ≤ ‖Q‖ * t ^ 2 * ‖field Q G z‖ := by positivity
  have hh := mul_le_mul_of_nonneg_right hexp hbase
  change ‖flow Q G hG t z - (z + t • field Q G z)‖ ≤
    (1 / 2 : ℝ) * ‖Q‖ * t ^ 2 * Real.exp (‖Q‖ * t) * ‖field Q G z‖ at he
  nlinarith

end

end KerrKoopman.HilbertError
