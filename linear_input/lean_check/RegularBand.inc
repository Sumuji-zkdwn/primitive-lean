/-!
Connections from actual compact sublevels and actual partial derivatives to
static existence and conditional energy convergence. No invariance or solution
existence is included in the trajectory predicate.
-/
noncomputable section
namespace LinearInputRegularBand
open LinearInputDesign LinearInputGradient

theorem band_nonempty {lam r u lo hi : ℝ} (hlo : 0 ≤ lo) (horder : lo ≤ hi) :
    {z : ℝ × ℝ | lo ≤ E lam r u z.1 z.2 ∧ E lam r u z.1 z.2 ≤ hi}.Nonempty := by
  have he : E lam r u 0 (Real.sqrt (2 * lo)) = lo := by
    simp only [E, f, zero_pow (by decide : 4 ≠ 0), zero_pow (by decide : 2 ≠ 0),
      mul_zero, zero_div, zero_add, sub_zero]
    rw [Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hlo)]
    ring
  refine ⟨(0, Real.sqrt (2 * lo)), ?_⟩
  change lo ≤ E lam r u 0 (Real.sqrt (2 * lo)) ∧ E lam r u 0 (Real.sqrt (2 * lo)) ≤ hi
  rw [he]
  exact ⟨le_refl lo, horder⟩

/-- The positive lower bound depends on the fixed input and the fixed band. -/
theorem exists_positive_gradient_bound {lam r u lo hi : ℝ} (hlam : 0 < lam)
    (hlo : (max (-r) 0) ^ 2 / (12 * lam) < lo) :
    ∃ m : ℝ, 0 < m ∧ ∀ z : ℝ × ℝ,
      (lo ≤ E lam r u z.1 z.2 ∧ E lam r u z.1 z.2 ≤ hi) →
      m ≤ gSq lam r u z.1 z.2 := by
  exact (LinearInputCoercivity.isCompact_band hlam r u lo hi).exists_forall_le'
    (continuous_gSq lam r u).continuousOn
    (fun z hz => gSq_pos_on_band hlam hlo hz.1)

/-- For every fixed input the global minimum exists on the valley y = sqrt(2) x. -/
theorem exists_valley_global_minimum {lam : ℝ} (hlam : 0 < lam) (r u : ℝ) :
    ∃ a : ℝ, ∀ x y : ℝ, E lam r u a (Real.sqrt 2 * a) ≤ E lam r u x y := by
  obtain ⟨z, hz⟩ := LinearInputCoercivity.exists_global_minimum hlam r u
  have hc := hz (z.1, Real.sqrt 2 * z.1)
  have hy : z.2 = Real.sqrt 2 * z.1 := by
    simp only [E, sub_self, zero_pow (by decide : 2 ≠ 0), zero_div, add_zero] at hc
    nlinarith [sq_nonneg (z.2 - Real.sqrt 2 * z.1)]
  refine ⟨z.1, fun x y => ?_⟩
  simpa only [hy] using hz (x, y)

theorem exists_minimizing_stationary_root {lam : ℝ} (hlam : 0 < lam) (r u : ℝ) :
    ∃ a : ℝ, u = input lam r a ∧ 0 ≤ lam * a ^ 2 + r ∧
      ∀ x y : ℝ, E lam r u a (Real.sqrt 2 * a) ≤ E lam r u x y := by
  obtain ⟨a, ha⟩ := exists_valley_global_minimum hlam r u
  obtain ⟨hu, hm⟩ := (LinearInputConsequences.global_minimum_iff_input_and_margin hlam).mp ha
  exact ⟨a, hu, hm, ha⟩

/-- Every nonzero fixed input has a unique full-plane global minimizer. -/
theorem exists_unique_global_minimum_of_input_ne_zero {lam r u : ℝ}
    (hlam : 0 < lam) (hu : u ≠ 0) :
    ∃! z : ℝ × ℝ, ∀ w : ℝ × ℝ, E lam r u z.1 z.2 ≤ E lam r u w.1 w.2 := by
  obtain ⟨a, hui, hm, ha⟩ := exists_minimizing_stationary_root hlam r u
  have hp : 0 < lam * a ^ 2 + r := by
    by_contra hn
    have hz : lam * a ^ 2 + r = 0 := le_antisymm (le_of_not_gt hn) hm
    apply hu
    rw [hui]
    unfold input
    nlinarith [congrArg (fun s : ℝ => s * a) hz]
  refine ⟨(a, Real.sqrt 2 * a), fun w => ha w.1 w.2, ?_⟩
  intro z hz
  have he : E lam r (input lam r a) z.1 z.2 =
      E lam r (input lam r a) a (Real.sqrt 2 * a) := by
    rw [← hui]
    exact le_antisymm (hz (a, Real.sqrt 2 * a)) (ha z.1 z.2)
  obtain ⟨hx, hy⟩ := unique_of_margin_pos (le_of_lt hlam) hp he
  exact Prod.ext hx hy

/-- A curve satisfies the actual two coordinate ODEs on nonnegative time.
This definition asserts neither existence nor confinement of such a curve. -/
def IsTrajectory (lam r u gamma target : ℝ) (x y b : ℝ → ℝ) : Prop :=
  ∀ t ∈ Set.Ici (0 : ℝ),
    HasDerivAt x
      (-gamma * (E lam r u (x t) (y t) - target) * gx lam r u (x t) (y t)
        - b t * gy (x t) (y t)) t ∧
    HasDerivAt y
      (-gamma * (E lam r u (x t) (y t) - target) * gy (x t) (y t)
        + b t * gx lam r u (x t) (y t)) t

theorem hasDerivAt_gap_of_trajectory {lam r u gamma target : ℝ} {x y b : ℝ → ℝ}
    (htraj : IsTrajectory lam r u gamma target x y b) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s => E lam r u (x s) (y s) - target)
      (-gamma * (E lam r u (x t) (y t) - target) * gSq lam r u (x t) (y t)) t :=
  (hasDerivAt_energy_fixed_input lam r u gamma target (b t)
    (htraj t ht).1 (htraj t ht).2).sub_const target

/-- Energy convergence along a supplied globally defined trajectory in the band.
The band assumption and the coordinate ODE are explicit premises. -/
theorem energy_convergence_in_band {lam r u gamma target upper : ℝ}
    (hlam : 0 < lam) (hgamma : 0 < gamma)
    (htarget : (max (-r) 0) ^ 2 / (12 * lam) < target)
    {x y b : ℝ → ℝ} (htraj : IsTrajectory lam r u gamma target x y b)
    (hband : ∀ t ∈ Set.Ici (0 : ℝ),
      target ≤ E lam r u (x t) (y t) ∧ E lam r u (x t) (y t) ≤ upper) :
    ∃ m : ℝ, 0 < m ∧
      (∀ t : ℝ, 0 ≤ t →
        (E lam r u (x t) (y t) - target) ^ 2 ≤
          (E lam r u (x 0) (y 0) - target) ^ 2 * Real.exp (-(2 * gamma * m) * t)) ∧
      Filter.Tendsto (fun t => E lam r u (x t) (y t)) Filter.atTop (nhds target) := by
  obtain ⟨m, hm, hbound⟩ := exists_positive_gradient_bound
    (r := r) (u := u) (hi := upper) hlam htarget
  have hge : ∀ t ∈ Set.Ici (0 : ℝ), m ≤ gSq lam r u (x t) (y t) :=
    fun t ht => hbound (x t, y t) (hband t ht)
  have hde : ∀ t ∈ Set.Ici (0 : ℝ),
      HasDerivAt (fun s => E lam r u (x s) (y s) - target)
        (-gamma * (E lam r u (x t) (y t) - target) * gSq lam r u (x t) (y t)) t :=
    fun _ ht => hasDerivAt_gap_of_trajectory htraj ht
  refine ⟨m, hm, fun t ht => ?_, ?_⟩
  · exact LinearInputDissipation.squared_error_exponential (le_of_lt hgamma) hde hge ht
  · have he := LinearInputDissipation.error_tendsto_zero hgamma hm hde hge
    simpa only [sub_add_cancel, zero_add] using he.add_const target

end LinearInputRegularBand
