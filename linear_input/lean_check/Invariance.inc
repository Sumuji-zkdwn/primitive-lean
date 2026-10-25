/-!
Forward energy-band invariance for a supplied globally defined trajectory.
No solution existence or confinement premise is used in this deduction.
-/
noncomputable section
namespace LinearInputInvariance

open LinearInputDesign LinearInputGradient LinearInputRegularBand

/-- Nonnegative damping makes the squared error antitone on nonnegative time. -/
theorem squared_error_antitone {e g : ℝ → ℝ} {gamma : ℝ}
    (hgamma : 0 ≤ gamma)
    (hd : ∀ t ∈ Set.Ici (0 : ℝ), HasDerivAt e (-gamma * e t * g t) t)
    (hg : ∀ t ∈ Set.Ici (0 : ℝ), 0 ≤ g t) :
    AntitoneOn (fun t => (e t) ^ 2) (Set.Ici (0 : ℝ)) := by
  have hsq : ∀ t ∈ Set.Ici (0 : ℝ),
      HasDerivAt (fun s => (e s) ^ 2) (-2 * gamma * (e t) ^ 2 * g t) t := by
    intro t ht
    convert (hd t ht).pow 2 using 1
    ring
  exact antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici (0 : ℝ))
    (fun t ht => (hsq t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hsq t (interior_subset ht)).hasDerivWithinAt)
    (fun t ht => by
      have hn : 0 ≤ 2 * gamma * (e t) ^ 2 * g t := by
        exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hgamma)
          (sq_nonneg _)) (hg t (interior_subset ht))
      nlinarith)

/-- A zero crossing cannot be followed by a negative error: its square would grow. -/
theorem error_nonneg {e g : ℝ → ℝ} {gamma : ℝ}
    (hgamma : 0 ≤ gamma)
    (hd : ∀ t ∈ Set.Ici (0 : ℝ), HasDerivAt e (-gamma * e t * g t) t)
    (hg : ∀ t ∈ Set.Ici (0 : ℝ), 0 ≤ g t)
    (he0 : 0 ≤ e 0) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ e t := by
  by_contra hn
  have hneg : e t < 0 := lt_of_not_ge hn
  have hc : ContinuousOn e (Set.Icc (0 : ℝ) t) :=
    fun s hs => (hd s hs.1).continuousAt.continuousWithinAt
  obtain ⟨s, hs, hz⟩ := intermediate_value_Icc' ht hc
    (show (0 : ℝ) ∈ Set.Icc (e t) (e 0) from ⟨le_of_lt hneg, he0⟩)
  have hbound := squared_error_antitone hgamma hd hg hs.1 ht hs.2
  dsimp only at hbound
  rw [hz] at hbound
  nlinarith [sq_pos_of_neg hneg]

theorem error_le_initial {e g : ℝ → ℝ} {gamma : ℝ}
    (hgamma : 0 ≤ gamma)
    (hd : ∀ t ∈ Set.Ici (0 : ℝ), HasDerivAt e (-gamma * e t * g t) t)
    (hg : ∀ t ∈ Set.Ici (0 : ℝ), 0 ≤ g t)
    (he0 : 0 ≤ e 0) {t : ℝ} (ht : 0 ≤ t) : e t ≤ e 0 := by
  have he := error_nonneg hgamma hd hg he0 ht
  have hs := squared_error_antitone hgamma hd hg
    (show (0 : ℝ) ∈ Set.Ici 0 by simp) ht ht
  nlinarith

/-- The original energy band follows from the actual ODE and the initial energy. -/
theorem energy_band_of_trajectory {lam r u gamma target : ℝ} {x y b : ℝ → ℝ}
    (hgamma : 0 ≤ gamma) (htraj : IsTrajectory lam r u gamma target x y b)
    (hinit : target ≤ E lam r u (x 0) (y 0)) :
    ∀ t ∈ Set.Ici (0 : ℝ),
      target ≤ E lam r u (x t) (y t) ∧
        E lam r u (x t) (y t) ≤ E lam r u (x 0) (y 0) := by
  have hd : ∀ t ∈ Set.Ici (0 : ℝ),
      HasDerivAt (fun s => E lam r u (x s) (y s) - target)
        (-gamma * (E lam r u (x t) (y t) - target) *
          gSq lam r u (x t) (y t)) t :=
    fun _ ht => hasDerivAt_gap_of_trajectory htraj ht
  have hg : ∀ t ∈ Set.Ici (0 : ℝ), 0 ≤ gSq lam r u (x t) (y t) :=
    fun t _ => gSq_nonneg lam r u (x t) (y t)
  intro t ht
  have hlo := error_nonneg hgamma hd hg (sub_nonneg.mpr hinit) ht
  have hhi := error_le_initial hgamma hd hg (sub_nonneg.mpr hinit) ht
  constructor <;> linarith

/-- Exponential energy convergence now needs an initial condition, not assumed confinement.
The coordinate trajectory is still supplied, so global existence remains separate. -/
theorem energy_convergence_of_initial {lam r u gamma target : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (htarget : (max (-r) 0) ^ 2 / (12 * lam) < target)
    {x y b : ℝ → ℝ} (htraj : IsTrajectory lam r u gamma target x y b)
    (hinit : target ≤ E lam r u (x 0) (y 0)) :
    ∃ m : ℝ, 0 < m ∧
      (∀ t : ℝ, 0 ≤ t →
        (E lam r u (x t) (y t) - target) ^ 2 ≤
          (E lam r u (x 0) (y 0) - target) ^ 2 * Real.exp (-(2 * gamma * m) * t)) ∧
      Filter.Tendsto (fun t => E lam r u (x t) (y t)) Filter.atTop (nhds target) := by
  exact energy_convergence_in_band hlam hgamma htarget htraj
    (energy_band_of_trajectory (le_of_lt hgamma) htraj hinit)

end LinearInputInvariance
