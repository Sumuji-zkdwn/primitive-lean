import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
Spatial convergence to the actual target energy level, with an explicit bound.
The metric on the real product is its standard maximum metric. The conclusion
is distance to the entire level, not convergence to one point on that level.
-/
noncomputable section
namespace LinearInputLevelConvergence

open Set Filter
open scoped Topology
open LinearInputDesign LinearInputCoercivity LinearInputLevelGeometry
open LinearInputRegularBand LinearInputInvariance LinearInputGradientBound

/-- An explicit bound for the product norm on an energy sublevel. -/
def bandRadius (lam r u upper : ℝ) : ℝ :=
  2 * Real.sqrt (max (upper + lowerBoundConstant lam r u) 0)

theorem bandRadius_nonneg (lam r u upper : ℝ) : 0 ≤ bandRadius lam r u upper := by
  unfold bandRadius
  positivity

theorem norm_le_bandRadius {lam r u upper : ℝ} (hlam : 0 < lam) {z : ℝ × ℝ}
    (he : E lam r u z.1 z.2 ≤ upper) : ‖z‖ ≤ bandRadius lam r u upper := by
  let S := max (upper + lowerBoundConstant lam r u) 0
  have hS : 0 ≤ S := le_max_right _ _
  have hmax : upper + lowerBoundConstant lam r u ≤ S := le_max_left _ _
  have hc := coercive_lower_bound hlam r u z.1 z.2
  have hx : z.1 ^ 2 ≤ S := by
    nlinarith [sq_nonneg (z.2 - Real.sqrt 2 * z.1)]
  have hi : 4 * (z.1 ^ 2 + (z.2 - Real.sqrt 2 * z.1) ^ 2 / 2) - z.2 ^ 2 =
      (z.2 - 2 * Real.sqrt 2 * z.1) ^ 2 := by
    ring_nf
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  have hy : z.2 ^ 2 ≤ 4 * S := by
    nlinarith [sq_nonneg (z.2 - 2 * Real.sqrt 2 * z.1)]
  have hR : 0 ≤ 2 * Real.sqrt S := by positivity
  have hRsq : (2 * Real.sqrt S) ^ 2 = 4 * S := by
    rw [mul_pow, Real.sq_sqrt hS]
    ring
  change max |z.1| |z.2| ≤ 2 * Real.sqrt S
  apply max_le
  · apply abs_le_of_sq_le_sq _ hR
    rw [hRsq]
    linarith
  · apply abs_le_of_sq_le_sq _ hR
    rwa [hRsq]

theorem target_level_nonempty {lam r u target : ℝ} (hlam : 0 < lam)
    (htarget : (max (-r) 0) ^ 2 / (12 * lam) < target) :
    {p : ℝ × ℝ | E lam r u p.1 p.2 = target}.Nonempty := by
  obtain ⟨a, ha, _⟩ := existsUnique_positive_radius (r := r) (u := u) (x := 1) (y := 0)
    hlam htarget (Or.inl one_ne_zero)
  exact ⟨(a*1, a*0), ha.2⟩

/-- Move inward along the same positive ray to the target level. The displacement
fraction is controlled by the actual energy error, without a root formula. -/
theorem exists_radial_target_point {lam r u target : ℝ} (hlam : 0 < lam)
    (htarget : (max (-r) 0) ^ 2 / (12 * lam) < target)
    {z : ℝ × ℝ} (he : target ≤ E lam r u z.1 z.2) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ E lam r u (a*z.1) (a*z.2) = target ∧
      (1-a) * (target - (max (-r) 0) ^ 2 / (12 * lam)) ≤
        E lam r u z.1 z.2 - target := by
  have hz : z.1 ≠ 0 ∨ z.2 ≠ 0 := by
    by_contra h
    push Not at h
    have hB : 0 ≤ (max (-r) 0) ^ 2 / (12 * lam) := by positivity
    simp [h.1, h.2, E, f] at he
    linarith
  obtain ⟨a, ha, _⟩ := existsUnique_positive_radius hlam htarget hz
  have ha1 : a ≤ 1 := by
    by_contra h
    have hs := energy_outward_strict hlam (lt_of_lt_of_le htarget he) (lt_of_not_ge h)
    rw [ha.2] at hs
    linarith
  have hscale := energy_outward_scaling hlam r u (a*z.1) (a*z.2)
    ((le_div_iff₀ ha.1).2 (by simpa using ha1))
  have hx : (1/a)*(a*z.1) = z.1 := by field_simp [ne_of_gt ha.1]
  have hy : (1/a)*(a*z.2) = z.2 := by field_simp [ne_of_gt ha.1]
  rw [hx, hy, ha.2] at hscale
  have hm := mul_le_mul_of_nonneg_left hscale ha.1.le
  have hi : a * (1/a * (target - (max (-r) 0) ^ 2 / (12 * lam))) =
      target - (max (-r) 0) ^ 2 / (12 * lam) := by field_simp [ne_of_gt ha.1]
  rw [hi] at hm
  refine ⟨a, ha.1, ha1, ha.2, ?_⟩
  have hgap := mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr he)
  nlinarith

theorem dist_radial_multiple (z : ℝ × ℝ) (a : ℝ) :
    dist z (a*z.1, a*z.2) = |1-a| * ‖z‖ := by
  change dist z (a • z) = _
  have hi : z - a • z = (1-a) • z := by rw [sub_smul, one_smul]
  rw [dist_eq_norm, hi, norm_smul, Real.norm_eq_abs]

/-- An actual point on the target level obeys a computed spatial error bound. -/
theorem exists_level_point_distance_bound {lam r u target upper : ℝ} (hlam : 0 < lam)
    (htarget : (max (-r) 0) ^ 2 / (12 * lam) < target)
    {z : ℝ × ℝ} (hlo : target ≤ E lam r u z.1 z.2)
    (hhi : E lam r u z.1 z.2 ≤ upper) :
    ∃ p : ℝ × ℝ, E lam r u p.1 p.2 = target ∧
      dist z p ≤ bandRadius lam r u upper /
        (target - (max (-r) 0) ^ 2 / (12 * lam)) * (E lam r u z.1 z.2 - target) := by
  obtain ⟨a, ha, ha1, hp, hgap⟩ := exists_radial_target_point hlam htarget hlo
  have hnorm := norm_le_bandRadius hlam hhi
  have hR := bandRadius_nonneg lam r u upper
  have hd : 0 < target - (max (-r) 0) ^ 2 / (12 * lam) := sub_pos.mpr htarget
  refine ⟨(a*z.1, a*z.2), hp, ?_⟩
  calc
    dist z (a*z.1, a*z.2) = (1-a) * ‖z‖ := by
      rw [dist_radial_multiple, abs_of_nonneg (sub_nonneg.mpr ha1)]
    _ ≤ (1-a) * bandRadius lam r u upper :=
      mul_le_mul_of_nonneg_left hnorm (sub_nonneg.mpr ha1)
    _ ≤ bandRadius lam r u upper * (E lam r u z.1 z.2 - target) /
        (target - (max (-r) 0) ^ 2 / (12 * lam)) := by
      apply (le_div_iff₀ hd).2
      have hm := mul_le_mul_of_nonneg_left hgap hR
      nlinarith
    _ = _ := by ring

theorem infDist_level_bound {lam r u target upper : ℝ} (hlam : 0 < lam)
    (htarget : (max (-r) 0) ^ 2 / (12 * lam) < target)
    {z : ℝ × ℝ} (hlo : target ≤ E lam r u z.1 z.2)
    (hhi : E lam r u z.1 z.2 ≤ upper) :
    Metric.infDist z {p : ℝ × ℝ | E lam r u p.1 p.2 = target} ≤
      bandRadius lam r u upper / (target - (max (-r) 0) ^ 2 / (12 * lam)) *
        (E lam r u z.1 z.2 - target) := by
  obtain ⟨p, hp, hdist⟩ := exists_level_point_distance_bound hlam htarget hlo hhi
  have hmem : p ∈ {q : ℝ × ℝ | E lam r u q.1 q.2 = target} := hp
  exact (Metric.infDist_le_dist_of_mem (x := z) hmem).trans hdist

/-- Exponential approach to the target level as a set in the product metric. -/
theorem spatial_error_exponential_of_initial {lam r u gamma target : ℝ}
    (hlam : 0 < lam) (hgamma : 0 ≤ gamma)
    (htarget : (max (-r) 0) ^ 2 / (12 * lam) < target)
    {x y b : ℝ → ℝ} (htraj : IsTrajectory lam r u gamma target x y b)
    (hinit : target ≤ E lam r u (x 0) (y 0)) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ Metric.infDist (x t, y t) {p : ℝ × ℝ | E lam r u p.1 p.2 = target} ∧
      Metric.infDist (x t, y t) {p : ℝ × ℝ | E lam r u p.1 p.2 = target} ≤
        bandRadius lam r u (E lam r u (x 0) (y 0)) /
          (target - (max (-r) 0) ^ 2 / (12 * lam)) *
          (E lam r u (x 0) (y 0) - target) *
          Real.exp (-(gamma * gradientLowerBound lam r u target (E lam r u (x 0) (y 0))) * t) := by
  have hb := energy_band_of_trajectory hgamma htraj hinit t ht
  have hd := infDist_level_bound (z := (x t, y t)) hlam htarget hb.1 hb.2
  have he := energy_error_exponential_of_initial hlam hgamma htarget htraj hinit ht
  have hC : 0 ≤ bandRadius lam r u (E lam r u (x 0) (y 0)) /
      (target - (max (-r) 0) ^ 2 / (12 * lam)) :=
    div_nonneg (bandRadius_nonneg _ _ _ _) (sub_nonneg.mpr htarget.le)
  refine ⟨Metric.infDist_nonneg, ?_⟩
  calc
    _ ≤ _ := hd
    _ ≤ _ := mul_le_mul_of_nonneg_left he.2 hC
    _ = _ := by ring

/-- The spatial distance to the actual nonempty target level tends to zero.
No point limit or periodic limiting trajectory is asserted. -/
theorem spatial_convergence_of_initial {lam r u gamma target : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (htarget : (max (-r) 0) ^ 2 / (12 * lam) < target)
    {x y b : ℝ → ℝ} (htraj : IsTrajectory lam r u gamma target x y b)
    (hinit : target ≤ E lam r u (x 0) (y 0)) :
    Tendsto (fun t => Metric.infDist (x t, y t)
      {p : ℝ × ℝ | E lam r u p.1 p.2 = target}) atTop (𝓝 0) := by
  let C := bandRadius lam r u (E lam r u (x 0) (y 0)) /
    (target - (max (-r) 0) ^ 2 / (12 * lam))
  obtain ⟨_, _, _, hE⟩ := energy_convergence_of_initial hlam hgamma htarget htraj hinit
  have hlim : Tendsto (fun t => C * (E lam r u (x t) (y t) - target)) atTop (𝓝 0) := by
    simpa only [sub_self, mul_zero] using (hE.sub_const target).const_mul C
  apply squeeze_zero' (Eventually.of_forall (fun _ => Metric.infDist_nonneg)) _ hlim
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  have hb := energy_band_of_trajectory hgamma.le htraj hinit t ht
  exact infDist_level_bound (z := (x t, y t)) hlam htarget hb.1 hb.2

end LinearInputLevelConvergence
