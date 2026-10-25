import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
Conditional estimates for supplied differentiable real functions on nonnegative
time. These theorems do not assert existence of an ODE solution.
-/
noncomputable section
namespace LinearInputDissipation

/-- Integrating-factor estimate; no sign assumption on v or the rate is needed. -/
theorem exponential_bound {v q : ℝ → ℝ} {k : ℝ}
    (hd : ∀ t ∈ Set.Ici (0 : ℝ), HasDerivAt v (q t) t)
    (hi : ∀ t ∈ Set.Ici (0 : ℝ), q t ≤ -k * v t)
    {t : ℝ} (ht : 0 ≤ t) :
    v t ≤ v 0 * Real.exp (-k * t) := by
  let w : ℝ → ℝ := fun s => Real.exp (k * s) * v s
  let dw : ℝ → ℝ := fun s => Real.exp (k * s) * (k * v s + q s)
  have hw : ∀ s ∈ Set.Ici (0 : ℝ), HasDerivAt w (dw s) s := by
    intro s hs
    convert (((hasDerivAt_id s).const_mul k).exp.mul (hd s hs)) using 1
    dsimp [w, dw]
    ring
  have hc : ContinuousOn w (Set.Ici (0 : ℝ)) := fun s hs =>
    (hw s hs).continuousAt.continuousWithinAt
  have ha : AntitoneOn w (Set.Ici (0 : ℝ)) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici (0 : ℝ)) hc
      (fun s hs => (hw s (interior_subset hs)).hasDerivWithinAt)
      (fun s hs => by
        dsimp [dw]
        apply mul_nonpos_of_nonneg_of_nonpos (le_of_lt (Real.exp_pos _))
        have h := hi s (interior_subset hs)
        linarith)
  have hvalue : Real.exp (k * t) * v t ≤ v 0 := by
    simpa [w] using ha (show (0 : ℝ) ∈ Set.Ici 0 by simp) ht ht
  have hdiv : v t ≤ v 0 / Real.exp (k * t) := by
    apply (le_div_iff₀ (Real.exp_pos _)).2
    simpa only [mul_comm] using hvalue
  simpa only [div_eq_mul_inv, ← Real.exp_neg, neg_mul] using hdiv

/-- A nonnegative damping coefficient gives a square-energy exponential bound
whenever a supplied solution has a common positive (or zero) damping bound. -/
theorem squared_error_exponential {e g : ℝ → ℝ} {gamma m : ℝ}
    (hgamma : 0 ≤ gamma)
    (hd : ∀ t ∈ Set.Ici (0 : ℝ),
      HasDerivAt e (-gamma * e t * g t) t)
    (hg : ∀ t ∈ Set.Ici (0 : ℝ), m ≤ g t)
    {t : ℝ} (ht : 0 ≤ t) :
    (e t) ^ 2 ≤ (e 0) ^ 2 * Real.exp (-(2 * gamma * m) * t) := by
  apply exponential_bound
    (v := fun s => (e s) ^ 2) (k := 2 * gamma * m) (t := t)
    (q := fun s => -2 * gamma * (e s) ^ 2 * g s)
  · intro s hs
    convert (hd s hs).pow 2 using 1
    ring
  · intro s hs
    have hp : 0 ≤ gamma * (e s) ^ 2 * (g s - m) :=
      mul_nonneg (mul_nonneg hgamma (sq_nonneg _)) (sub_nonneg.mpr (hg s hs))
    nlinarith
  · exact ht

/-- Squared error tends to zero for a supplied trajectory with positive rate. -/
theorem squared_error_tendsto_zero {e g : ℝ → ℝ} {gamma m : ℝ}
    (hgamma : 0 < gamma) (hm : 0 < m)
    (hd : ∀ t ∈ Set.Ici (0 : ℝ),
      HasDerivAt e (-gamma * e t * g t) t)
    (hg : ∀ t ∈ Set.Ici (0 : ℝ), m ≤ g t) :
    Filter.Tendsto (fun t => (e t) ^ 2) Filter.atTop (nhds 0) := by
  have hc : Filter.Tendsto (fun t : ℝ => (2 * gamma * m) * t)
      Filter.atTop Filter.atTop :=
    Filter.tendsto_id.const_mul_atTop (by positivity)
  have hb : Filter.Tendsto
      (fun t : ℝ => (e 0) ^ 2 * Real.exp (-(2 * gamma * m) * t))
      Filter.atTop (nhds 0) := by
    simpa only [Function.comp_def, neg_mul, mul_zero] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp hc).const_mul ((e 0) ^ 2)
  apply squeeze_zero' (Filter.Eventually.of_forall (fun t => sq_nonneg (e t))) _ hb
  exact (Filter.eventually_ge_atTop (0 : ℝ)).mono
    (fun t ht => squared_error_exponential (le_of_lt hgamma) hd hg ht)

theorem error_tendsto_zero {e g : ℝ → ℝ} {gamma m : ℝ}
    (hgamma : 0 < gamma) (hm : 0 < m)
    (hd : ∀ t ∈ Set.Ici (0 : ℝ),
      HasDerivAt e (-gamma * e t * g t) t)
    (hg : ∀ t ∈ Set.Ici (0 : ℝ), m ≤ g t) :
    Filter.Tendsto e Filter.atTop (nhds 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  simpa only [Real.sqrt_sq_eq_abs, Real.sqrt_zero] using
    (squared_error_tendsto_zero hgamma hm hd hg).sqrt

end LinearInputDissipation
