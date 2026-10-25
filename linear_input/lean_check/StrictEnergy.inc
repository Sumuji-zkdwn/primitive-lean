import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
Exact energy-gap evolution, finite-time nonarrival, and injectivity of a
supplied trajectory.  These statements do not assert solution existence.
-/

noncomputable section
namespace LinearInputStrictEnergy

open Real Set MeasureTheory
open LinearInputDesign LinearInputGradient LinearInputRegularBand

/-- The exact integrating-factor formula only needs continuity of the actual
coefficient on nonnegative time.  No positivity of the damping is assumed. -/
theorem error_eq_initial_mul_exp_integral {e g : ℝ → ℝ} {gamma : ℝ}
    (hg : ContinuousOn g (Ici (0 : ℝ)))
    (hd : ∀ t ∈ Ici (0 : ℝ), HasDerivAt e (-gamma * e t * g t) t)
    {t : ℝ} (ht : 0 ≤ t) :
    e t = e 0 * Real.exp (-gamma * (∫ s in 0..t, g s)) := by
  let q : ℝ → ℝ := fun s => g (max s 0)
  have hq : Continuous q := hg.comp_continuous
    (continuous_id.max continuous_const) (fun s => le_max_right s 0)
  have hqe (s : ℝ) (hs : 0 ≤ s) : q s = g s := by
    simp only [q, max_eq_left hs]
  let G : ℝ → ℝ := fun s => ∫ v in 0..s, q v
  have hG (s : ℝ) : HasDerivAt G (q s) s :=
    (hq.integral_hasStrictDerivAt 0 s).hasDerivAt
  let w : ℝ → ℝ := fun s => e s * Real.exp (gamma * G s)
  have hw (s : ℝ) (hs : s ∈ Ici (0 : ℝ)) : HasDerivAt w 0 s := by
    convert (hd s hs).mul ((hG s).const_mul gamma).exp using 1
    rw [hqe s hs]
    ring
  have hc : ContinuousOn w (Ici (0 : ℝ)) :=
    fun s hs => (hw s hs).continuousAt.continuousWithinAt
  have hanti : AntitoneOn w (Ici (0 : ℝ)) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici (0 : ℝ)) hc
      (fun s hs => (hw s (interior_subset hs)).hasDerivWithinAt)
      (fun _ _ => le_refl 0)
  have hmono : MonotoneOn w (Ici (0 : ℝ)) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (0 : ℝ)) hc
      (fun s hs => (hw s (interior_subset hs)).hasDerivWithinAt)
      (fun _ _ => le_refl 0)
  have hconst : w t = w 0 := le_antisymm
    (hanti (show (0 : ℝ) ∈ Ici 0 by simp) ht ht)
    (hmono (show (0 : ℝ) ∈ Ici 0 by simp) ht ht)
  have hvalue : e t * Real.exp (gamma * G t) = e 0 := by
    simpa only [w, G, intervalIntegral.integral_same, mul_zero, Real.exp_zero, mul_one] using hconst
  have hGt : G t = ∫ s in 0..t, g s := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht] at hs
    exact hqe s hs.1
  have he : e t = e 0 / Real.exp (gamma * G t) :=
    (eq_div_iff (Real.exp_ne_zero _)).2 hvalue
  rw [he, hGt]
  simp only [div_eq_mul_inv, ← Real.exp_neg, neg_mul]

/-- A positive initial scalar gap cannot become zero at a finite time. -/
theorem error_pos {e g : ℝ → ℝ} {gamma : ℝ}
    (hg : ContinuousOn g (Ici (0 : ℝ)))
    (hd : ∀ t ∈ Ici (0 : ℝ), HasDerivAt e (-gamma * e t * g t) t)
    (he0 : 0 < e 0) {t : ℝ} (ht : 0 ≤ t) : 0 < e t := by
  rw [error_eq_initial_mul_exp_integral hg hd ht]
  exact mul_pos he0 (Real.exp_pos _)

/-- The coefficient in the energy law is continuous along the actual curve;
no continuity of b is needed once both actual coordinate derivatives exist. -/
theorem continuousOn_gradient_coefficient {lam r u gamma target : ℝ}
    {x y b : ℝ → ℝ} (htraj : IsTrajectory lam r u gamma target x y b) :
    ContinuousOn (fun t => gSq lam r u (x t) (y t)) (Ici (0 : ℝ)) := by
  intro t ht
  have hx : ContinuousAt x t := (htraj t ht).1.continuousAt
  have hy : ContinuousAt y t := (htraj t ht).2.continuousAt
  have hxy : ContinuousAt (fun s => (x s, y s)) t := hx.prodMk hy
  exact ((continuous_gSq lam r u).continuousAt.comp hxy).continuousWithinAt

/-- Exact gap evolution along a supplied trajectory, with its actual gradient
coefficient inside the integral. -/
theorem energy_gap_exact {lam r u gamma target : ℝ} {x y b : ℝ → ℝ}
    (htraj : IsTrajectory lam r u gamma target x y b)
    {t : ℝ} (ht : 0 ≤ t) :
    E lam r u (x t) (y t) - target =
      (E lam r u (x 0) (y 0) - target) *
        Real.exp (-gamma * (∫ s in 0..t, gSq lam r u (x s) (y s))) := by
  exact error_eq_initial_mul_exp_integral (continuousOn_gradient_coefficient htraj)
    (fun s hs => hasDerivAt_gap_of_trajectory htraj hs) ht

/-- Reaching the target at a finite time is equivalent to starting there.
Thus the strict-gap hypothesis in the no-return results is substantive. -/
theorem energy_eq_target_iff {lam r u gamma target : ℝ} {x y b : ℝ → ℝ}
    (htraj : IsTrajectory lam r u gamma target x y b)
    {t : ℝ} (ht : 0 ≤ t) :
    E lam r u (x t) (y t) = target ↔ E lam r u (x 0) (y 0) = target := by
  rw [← sub_eq_zero, energy_gap_exact htraj ht, mul_eq_zero]
  simp only [Real.exp_ne_zero, or_false, sub_eq_zero]

/-- Strict separation from the target is preserved at every finite time.
Unlike strict decay, this conclusion needs no sign assumption on gamma. -/
theorem energy_strictly_above_target {lam r u gamma target : ℝ} {x y b : ℝ → ℝ}
    (htraj : IsTrajectory lam r u gamma target x y b)
    (hinit : target < E lam r u (x 0) (y 0))
    {t : ℝ} (ht : 0 ≤ t) : target < E lam r u (x t) (y t) := by
  have hpos := error_pos (continuousOn_gradient_coefficient htraj)
    (fun s hs => hasDerivAt_gap_of_trajectory htraj hs) (sub_pos.mpr hinit) ht
  exact sub_pos.mp hpos

/-- Above all critical values the actual energy derivative is strictly
negative along a trajectory starting strictly above its target. -/
theorem energy_deriv_neg {lam r u gamma target : ℝ} {x y b : ℝ → ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (htarget : (max (-r) 0) ^ 2 / (12 * lam) < target)
    (htraj : IsTrajectory lam r u gamma target x y b)
    (hinit : target < E lam r u (x 0) (y 0))
    {t : ℝ} (ht : 0 ≤ t) :
    deriv (fun s => E lam r u (x s) (y s)) t < 0 := by
  have he := energy_strictly_above_target htraj hinit ht
  have hg := gSq_pos_on_band hlam htarget he.le
  have hd := hasDerivAt_energy_fixed_input lam r u gamma target (b t)
    (htraj t ht).1 (htraj t ht).2
  rw [hd.deriv]
  have hpos := mul_pos (mul_pos hgamma (sub_pos.mpr he)) hg
  nlinarith

/-- The actual energy is strictly antitone on the entire nonnegative time axis. -/
theorem energy_strictAntiOn {lam r u gamma target : ℝ} {x y b : ℝ → ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (htarget : (max (-r) 0) ^ 2 / (12 * lam) < target)
    (htraj : IsTrajectory lam r u gamma target x y b)
    (hinit : target < E lam r u (x 0) (y 0)) :
    StrictAntiOn (fun t => E lam r u (x t) (y t)) (Ici (0 : ℝ)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici (0 : ℝ))
  · intro t ht
    exact (hasDerivAt_energy_fixed_input lam r u gamma target (b t)
      (htraj t ht).1 (htraj t ht).2).continuousAt.continuousWithinAt
  · intro t ht
    exact energy_deriv_neg hlam hgamma htarget htraj hinit (interior_subset ht)

/-- No two distinct nonnegative times visit the same spatial state. -/
theorem trajectory_injOn {lam r u gamma target : ℝ} {x y b : ℝ → ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (htarget : (max (-r) 0) ^ 2 / (12 * lam) < target)
    (htraj : IsTrajectory lam r u gamma target x y b)
    (hinit : target < E lam r u (x 0) (y 0)) :
    InjOn (fun t => (x t, y t)) (Ici (0 : ℝ)) := by
  intro s hs t ht heq
  have hxs : x s = x t := congrArg Prod.fst heq
  have hys : y s = y t := congrArg Prod.snd heq
  have hE : E lam r u (x s) (y s) = E lam r u (x t) (y t) := by rw [hxs, hys]
  exact (energy_strictAntiOn hlam hgamma htarget htraj hinit).injOn hs ht hE

/-- In particular, no spatial return occurs after a strictly positive time. -/
theorem trajectory_no_return {lam r u gamma target : ℝ} {x y b : ℝ → ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (htarget : (max (-r) 0) ^ 2 / (12 * lam) < target)
    (htraj : IsTrajectory lam r u gamma target x y b)
    (hinit : target < E lam r u (x 0) (y 0))
    {s T : ℝ} (hs : 0 ≤ s) (hT : 0 < T) :
    (x (s + T), y (s + T)) ≠ (x s, y s) := by
  intro heq
  have h := trajectory_injOn hlam hgamma htarget htraj hinit
    (add_nonneg hs hT.le) hs heq
  linarith

/-- A positive finite period is impossible under the same strict initial gap. -/
theorem trajectory_not_periodic {lam r u gamma target : ℝ} {x y b : ℝ → ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (htarget : (max (-r) 0) ^ 2 / (12 * lam) < target)
    (htraj : IsTrajectory lam r u gamma target x y b)
    (hinit : target < E lam r u (x 0) (y 0))
    {T : ℝ} (hT : 0 < T) :
    ¬ Function.Periodic (fun t => (x t, y t)) T := by
  intro hp
  exact trajectory_no_return hlam hgamma htarget htraj hinit (le_refl 0) hT (hp 0)

/-- A local version of the exact scalar formula uses only data on a finite
closed interval.  It is suitable for an actually constructed local solution. -/
theorem error_eq_initial_mul_exp_integral_on_Icc {e g : ℝ → ℝ} {gamma T : ℝ}
    (hg : ContinuousOn g (Icc (0 : ℝ) T)) (hT : 0 ≤ T)
    (hd : ∀ s ∈ Icc (0 : ℝ) T, HasDerivAt e (-gamma * e s * g s) s)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    e t = e 0 * Real.exp (-gamma * (∫ s in 0..t, g s)) := by
  let q : ℝ → ℝ := fun s => g (max 0 (min s T))
  have hq : Continuous q := hg.comp_continuous
    (continuous_const.max (continuous_id.min continuous_const))
    (fun s => ⟨le_max_left 0 (min s T), max_le hT (min_le_right s T)⟩)
  have hqe (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) : q s = g s := by
    simp only [q, min_eq_left hs.2, max_eq_right hs.1]
  let G : ℝ → ℝ := fun s => ∫ v in 0..s, q v
  have hG (s : ℝ) : HasDerivAt G (q s) s :=
    (hq.integral_hasStrictDerivAt 0 s).hasDerivAt
  let w : ℝ → ℝ := fun s => e s * Real.exp (gamma * G s)
  have hw (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) : HasDerivAt w 0 s := by
    convert (hd s hs).mul ((hG s).const_mul gamma).exp using 1
    rw [hqe s hs]
    ring
  have hc : ContinuousOn w (Icc (0 : ℝ) T) :=
    fun s hs => (hw s hs).continuousAt.continuousWithinAt
  have hanti : AntitoneOn w (Icc (0 : ℝ) T) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc (0 : ℝ) T) hc
      (fun s hs => (hw s (interior_subset hs)).hasDerivWithinAt)
      (fun _ _ => le_refl 0)
  have hmono : MonotoneOn w (Icc (0 : ℝ) T) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) T) hc
      (fun s hs => (hw s (interior_subset hs)).hasDerivWithinAt)
      (fun _ _ => le_refl 0)
  have hzero : (0 : ℝ) ∈ Icc 0 T := ⟨le_refl 0, hT⟩
  have hconst : w t = w 0 :=
    le_antisymm (hanti hzero ht ht.1) (hmono hzero ht ht.1)
  have hvalue : e t * Real.exp (gamma * G t) = e 0 := by
    simpa only [w, G, intervalIntegral.integral_same, mul_zero, Real.exp_zero, mul_one] using hconst
  have hGt : G t = ∫ s in 0..t, g s := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    exact hqe s ⟨hs.1, hs.2.trans ht.2⟩
  have he : e t = e 0 / Real.exp (gamma * G t) :=
    (eq_div_iff (Real.exp_ne_zero _)).2 hvalue
  rw [he, hGt]
  simp only [div_eq_mul_inv, ← Real.exp_neg, neg_mul]

/-- Exact energy evolution on a finite interval follows from coordinate ODEs
on that interval alone; no global trajectory premise is required. -/
theorem energy_gap_exact_on_Icc {lam r u gamma target T : ℝ} {x y b : ℝ → ℝ}
    (hT : 0 ≤ T)
    (hode : ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivAt x
        (-gamma * (E lam r u (x s) (y s) - target) * gx lam r u (x s) (y s)
          - b s * gy (x s) (y s)) s ∧
      HasDerivAt y
        (-gamma * (E lam r u (x s) (y s) - target) * gy (x s) (y s)
          + b s * gx lam r u (x s) (y s)) s)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    E lam r u (x t) (y t) - target =
      (E lam r u (x 0) (y 0) - target) *
        Real.exp (-gamma * (∫ s in 0..t, gSq lam r u (x s) (y s))) := by
  have hg : ContinuousOn (fun s => gSq lam r u (x s) (y s)) (Icc (0 : ℝ) T) := by
    intro s hs
    have hxy : ContinuousAt (fun v => (x v, y v)) s :=
      (hode s hs).1.continuousAt.prodMk (hode s hs).2.continuousAt
    exact ((continuous_gSq lam r u).continuousAt.comp hxy).continuousWithinAt
  apply error_eq_initial_mul_exp_integral_on_Icc hg hT ?_ ht
  intro s hs
  exact (hasDerivAt_energy_fixed_input lam r u gamma target (b s)
    (hode s hs).1 (hode s hs).2).sub_const target

end LinearInputStrictEnergy
