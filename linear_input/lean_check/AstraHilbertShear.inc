
/-!
# Actual shear stability in the Hilbert product norm

The state space uses Mathlib's `WithLp 2`, not the default max product norm.
The nonlinear map G is an actual supplied 1-Lipschitz map, and Q is an actual
bounded linear operator. No shear stability estimate is taken as an assumption.
-/

namespace KerrKoopman.HilbertShear

noncomputable section

/-- Sharp exponential bound for the real two-by-two shear majorant. -/
theorem scalar_shear_sq_bound (a b q : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hq : 0 ≤ q) :
    (a + q * b) ^ 2 + b ^ 2 ≤ Real.exp q * (a ^ 2 + b ^ 2) := by
  let r := Real.exp (q / 2)
  have hr : 0 < r := Real.exp_pos _
  have hrne : r ≠ 0 := ne_of_gt hr
  have hr1 : 1 ≤ r := by
    dsimp [r]
    exact Real.one_le_exp_iff.mpr (by linarith)
  have hqr : q ≤ r - r⁻¹ := by
    have hs := Real.self_le_sinh_iff.mpr (show 0 ≤ q / 2 by linarith)
    rw [Real.sinh_eq, Real.exp_neg] at hs
    dsimp [r]
    linarith
  have hid : r ^ 2 * (a ^ 2 + b ^ 2) -
      ((a + (r - r⁻¹) * b) ^ 2 + b ^ 2) =
        (r ^ 2 - 1) * (a - b / r) ^ 2 := by
    field_simp
    ring
  have hn : 0 ≤ (r ^ 2 - 1) * (a - b / r) ^ 2 :=
    mul_nonneg (by nlinarith) (sq_nonneg _)
  have hsq : (a + q * b) ^ 2 ≤ (a + (r - r⁻¹) * b) ^ 2 := by
    gcongr
  have hr2 : r ^ 2 = Real.exp q := by
    dsimp [r]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  nlinarith

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

abbrev State (V : Type*) := WithLp 2 (V × V)

def shearA (Q : V →L[ℝ] V) (t : ℝ) (z : State V) : State V :=
  WithLp.toLp 2 (z.fst - t • Q z.snd, z.snd)

def shearB (Q : V →L[ℝ] V) (G : V → V) (t : ℝ) (z : State V) : State V :=
  WithLp.toLp 2 (z.fst, z.snd - t • Q (G z.fst))

def lieStep (Q : V →L[ℝ] V) (G : V → V) (t : ℝ) (z : State V) : State V :=
  shearB Q G t (shearA Q t z)

omit [InnerProductSpace ℝ V] in
theorem l2_bound_from_fst_shear (u v : State V) (q : ℝ) (hq : 0 ≤ q)
    (hfst : ‖u.fst‖ ≤ ‖v.fst‖ + q * ‖v.snd‖)
    (hsnd : ‖u.snd‖ ≤ ‖v.snd‖) :
    ‖u‖ ≤ Real.exp (q / 2) * ‖v‖ := by
  have hf : ‖u.fst‖ ^ 2 ≤ (‖v.fst‖ + q * ‖v.snd‖) ^ 2 := by gcongr
  have hs : ‖u.snd‖ ^ 2 ≤ ‖v.snd‖ ^ 2 := by gcongr
  have hm := scalar_shear_sq_bound ‖v.fst‖ ‖v.snd‖ q
    (norm_nonneg _) (norm_nonneg _) hq
  have hu := WithLp.prod_norm_sq_eq_of_L2 u
  have hv := WithLp.prod_norm_sq_eq_of_L2 v
  have he : Real.exp (q / 2) ^ 2 = Real.exp q := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hp : 0 ≤ Real.exp (q / 2) * ‖v‖ := by positivity
  nlinarith [norm_nonneg u]

omit [InnerProductSpace ℝ V] in
theorem l2_bound_from_snd_shear (u v : State V) (q : ℝ) (hq : 0 ≤ q)
    (hfst : ‖u.fst‖ ≤ ‖v.fst‖)
    (hsnd : ‖u.snd‖ ≤ ‖v.snd‖ + q * ‖v.fst‖) :
    ‖u‖ ≤ Real.exp (q / 2) * ‖v‖ := by
  have hf : ‖u.fst‖ ^ 2 ≤ ‖v.fst‖ ^ 2 := by gcongr
  have hs : ‖u.snd‖ ^ 2 ≤ (‖v.snd‖ + q * ‖v.fst‖) ^ 2 := by gcongr
  have hm := scalar_shear_sq_bound ‖v.snd‖ ‖v.fst‖ q
    (norm_nonneg _) (norm_nonneg _) hq
  have hu := WithLp.prod_norm_sq_eq_of_L2 u
  have hv := WithLp.prod_norm_sq_eq_of_L2 v
  have he : Real.exp (q / 2) ^ 2 = Real.exp q := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hp : 0 ≤ Real.exp (q / 2) * ‖v‖ := by positivity
  nlinarith [norm_nonneg u]

theorem norm_linear_shear (Q : V →L[ℝ] V) (t : ℝ) (x y : V) :
    ‖x - t • Q y‖ ≤ ‖x‖ + (‖Q‖ * |t|) * ‖y‖ := by
  calc
    ‖x - t • Q y‖ ≤ ‖x‖ + ‖t • Q y‖ := norm_sub_le _ _
    _ = ‖x‖ + |t| * ‖Q y‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ‖x‖ + |t| * (‖Q‖ * ‖y‖) := by
      gcongr
      exact Q.le_opNorm y
    _ = ‖x‖ + (‖Q‖ * |t|) * ‖y‖ := by ring

/-- The actual A shear has the Hilbert exponential half-step bound. -/
theorem shearA_norm_sub_le (Q : V →L[ℝ] V) (t : ℝ) (z w : State V) :
    ‖shearA Q t z - shearA Q t w‖ ≤
      Real.exp (‖Q‖ * |t| / 2) * ‖z - w‖ := by
  apply l2_bound_from_fst_shear _ _ _ (by positivity)
  · have hf : (shearA Q t z - shearA Q t w).fst =
        (z.fst - w.fst) - t • Q (z.snd - w.snd) := by
      change (z.fst - t • Q z.snd) - (w.fst - t • Q w.snd) = _
      rw [map_sub, smul_sub]
      abel
    rw [hf, WithLp.sub_fst, WithLp.sub_snd]
    exact norm_linear_shear Q t _ _
  · exact le_rfl

/-- A supplied global nonexpansive G suffices for the actual nonlinear B shear. -/
theorem shearB_norm_sub_le (Q : V →L[ℝ] V) (G : V → V)
    (hG : LipschitzWith 1 G) (t : ℝ) (z w : State V) :
    ‖shearB Q G t z - shearB Q G t w‖ ≤
      Real.exp (‖Q‖ * |t| / 2) * ‖z - w‖ := by
  apply l2_bound_from_snd_shear _ _ _ (by positivity)
  · exact le_rfl
  · have hs : (shearB Q G t z - shearB Q G t w).snd =
        (z.snd - w.snd) - t • Q (G z.fst - G w.fst) := by
      change (z.snd - t • Q (G z.fst)) - (w.snd - t • Q (G w.fst)) = _
      rw [map_sub, smul_sub]
      abel
    have hg : ‖G z.fst - G w.fst‖ ≤ ‖z.fst - w.fst‖ := by
      simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using hG.dist_le_mul z.fst w.fst
    rw [hs, WithLp.sub_fst, WithLp.sub_snd]
    exact (norm_linear_shear Q t _ _).trans (by gcongr)

/-- The composed physical-time splitting step has growth exp(||Q||*|t|). -/
theorem lieStep_norm_sub_le (Q : V →L[ℝ] V) (G : V → V)
    (hG : LipschitzWith 1 G) (t : ℝ) (z w : State V) :
    ‖lieStep Q G t z - lieStep Q G t w‖ ≤
      Real.exp (‖Q‖ * |t|) * ‖z - w‖ := by
  have hA := shearA_norm_sub_le Q t z w
  have hB := shearB_norm_sub_le Q G hG t (shearA Q t z) (shearA Q t w)
  have hprod : Real.exp (‖Q‖ * |t| / 2) *
      (Real.exp (‖Q‖ * |t| / 2) * ‖z - w‖) =
        Real.exp (‖Q‖ * |t|) * ‖z - w‖ := by
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  exact hB.trans (by
    rw [← hprod]
    exact mul_le_mul_of_nonneg_left hA (Real.exp_nonneg _))

/-- The projection of a nonexpansive material map is again nonexpansive. -/
theorem projected_nonlinearity_lipschitz (P : V →L[ℝ] V) (hP : ‖P‖ ≤ 1)
    (g : V → V) (hg : LipschitzWith 1 g) :
    LipschitzWith 1 (fun x => P (g x)) := by
  apply lipschitzWith_iff_norm_sub_le.mpr
  intro x y
  change ‖P (g x) - P (g y)‖ ≤ 1 * ‖x - y‖
  have hxy : ‖g x - g y‖ ≤ ‖x - y‖ := by
    simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using hg.dist_le_mul x y
  rw [← map_sub]
  calc
    ‖P (g x - g y)‖ ≤ ‖P‖ * ‖g x - g y‖ := P.le_opNorm _
    _ ≤ 1 * ‖x - y‖ := by gcongr

def field (Q : V →L[ℝ] V) (G : V → V) (z : State V) : State V :=
  WithLp.toLp 2 (-Q z.snd, -Q (G z.fst))

/-- The actual coupled vector field has global Lipschitz constant ||Q||. -/
theorem field_norm_sub_le (Q : V →L[ℝ] V) (G : V → V)
    (hG : LipschitzWith 1 G) (z w : State V) :
    ‖field Q G z - field Q G w‖ ≤ ‖Q‖ * ‖z - w‖ := by
  have hf : (field Q G z - field Q G w).fst = -Q (z.snd - w.snd) := by
    change -Q z.snd - -Q w.snd = _
    rw [map_sub]
    abel
  have hs : (field Q G z - field Q G w).snd = -Q (G z.fst - G w.fst) := by
    change -Q (G z.fst) - -Q (G w.fst) = _
    rw [map_sub]
    abel
  have hgn : ‖G z.fst - G w.fst‖ ≤ ‖z.fst - w.fst‖ := by
    simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using hG.dist_le_mul z.fst w.fst
  have hfn : ‖(field Q G z - field Q G w).fst‖ ≤ ‖Q‖ * ‖(z - w).snd‖ := by
    rw [hf, norm_neg, WithLp.sub_snd]
    exact Q.le_opNorm _
  have hsn : ‖(field Q G z - field Q G w).snd‖ ≤ ‖Q‖ * ‖(z - w).fst‖ := by
    rw [hs, norm_neg, WithLp.sub_fst]
    exact (Q.le_opNorm _).trans (by gcongr)
  have hf2 : ‖(field Q G z - field Q G w).fst‖ ^ 2 ≤
      (‖Q‖ * ‖(z - w).snd‖) ^ 2 := by gcongr
  have hs2 : ‖(field Q G z - field Q G w).snd‖ ^ 2 ≤
      (‖Q‖ * ‖(z - w).fst‖) ^ 2 := by gcongr
  have hsq : ‖field Q G z - field Q G w‖ ^ 2 ≤ (‖Q‖ * ‖z - w‖) ^ 2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2, mul_pow, WithLp.prod_norm_sq_eq_of_L2]
    nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq

theorem field_lipschitz (Q : V →L[ℝ] V) (G : V → V)
    (hG : LipschitzWith 1 G) : LipschitzWith ‖Q‖₊ (field Q G) := by
  exact lipschitzWith_iff_norm_sub_le.mpr (field_norm_sub_le Q G hG)

theorem field_norm_le (Q : V →L[ℝ] V) (G : V → V)
    (hG : LipschitzWith 1 G) (hG0 : G 0 = 0) (z : State V) :
    ‖field Q G z‖ ≤ ‖Q‖ * ‖z‖ := by
  have hz : field Q G 0 = 0 := by
    change WithLp.toLp 2 (-Q 0, -Q (G 0)) = 0
    simp only [hG0, map_zero, neg_zero]
    rfl
  simpa only [hz, sub_zero] using field_norm_sub_le Q G hG z 0

/-- Growth of any actual differentiable solution on the stated time interval.
Existence of such a curve is not asserted or hidden in a stability hypothesis. -/
theorem solution_growth (Q : V →L[ℝ] V) (G : V → V)
    (hG : LipschitzWith 1 G) (hG0 : G 0 = 0)
    (u : ℝ → State V) (T : ℝ)
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivAt u (field Q G (u t)) t)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ‖u t‖ ≤ Real.exp (‖Q‖ * t) * ‖u 0‖ := by
  have hc : ContinuousOn u (Set.Icc (0 : ℝ) T) :=
    fun s hs => (hu s hs).continuousAt.continuousWithinAt
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := u) (f' := fun s => field Q G (u s)) (δ := ‖u 0‖) (K := ‖Q‖) (ε := 0)
    hc (fun s hs => (hu s ⟨hs.1, hs.2.le⟩).hasDerivWithinAt) le_rfl
    (fun s _ => by simpa using field_norm_le Q G hG hG0 (u s)) t ht
  simpa only [gronwallBound_ε0, sub_zero, mul_comm] using hg

end

end KerrKoopman.HilbertShear
