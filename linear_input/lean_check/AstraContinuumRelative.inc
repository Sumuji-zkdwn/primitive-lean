
/-!
# Continuum relative energy on a periodic real interval

These are real functions of physical time and position, integrated with
Lebesgue measure. Supplied classical component equations imply the actual
time derivative of the integral, with periodic integration by parts. The
comparison magnetic equation has an explicit residual. No existence result,
Fourier projection construction, or mesh limit is assumed to be proved here.
-/

namespace KerrKoopman.ContinuumRelative

noncomputable section

open Riccati RelativeEnergy RelativeDynamics ContinuumCalculus MeasureTheory Set Filter
open scoped Topology Interval

/-- Pointwise time rate computed from the four physical component equations. -/
def densityRate (e h v j ex hx vx jx r : ℝ) : ℝ :=
  (v - e) * (1 + v ^ 2) * (-jx / (1 + v ^ 2)) -
    (constitutive v - constitutive e) * (-hx / (1 + e ^ 2)) +
    (j - h) * ((-vx + r) - -ex)

theorem densityRate_eq (e h v j ex hx vx jx r : ℝ) :
    densityRate e h v j ex hx vx jx r =
      -((vx - ex) * (j - h) + (v - e) * (jx - hx)) +
      ((-hx) * nonlinearRemainder e v + (j - h) * r) := by
  rw [densityRate, relativeRate_decomposition]
  ring

theorem nonlinearRemainder_continuous (E V : ℝ → ℝ)
    (hE : Continuous E) (hV : Continuous V) :
    Continuous (fun x => nonlinearRemainder (E x) (V x)) := by
  unfold nonlinearRemainder constitutive
  have hn : ∀ x, 1 + E x ^ 2 ≠ 0 :=
    fun x => ne_of_gt (FiniteEnergy.constitutive_denominator_pos (E x))
  fun_prop (disch := assumption)

/-- The spatial cross terms are the derivative of the product of the two
physical errors. They cancel by actual periodic integration by parts. -/
theorem integrated_densityRate_eq
    (E H V J Ex Hx Vx Jx r : ℝ → ℝ) (a b : ℝ)
    (hE : ∀ x, HasDerivAt E (Ex x) x) (hH : ∀ x, HasDerivAt H (Hx x) x)
    (hV : ∀ x, HasDerivAt V (Vx x) x) (hJ : ∀ x, HasDerivAt J (Jx x) x)
    (cEx : Continuous Ex) (cHx : Continuous Hx)
    (cVx : Continuous Vx) (cJx : Continuous Jx) (cr : Continuous r)
    (pE : E b = E a) (pH : H b = H a) (pV : V b = V a) (pJ : J b = J a) :
    (∫ x in a..b, densityRate (E x) (H x) (V x) (J x)
      (Ex x) (Hx x) (Vx x) (Jx x) (r x)) =
    ∫ x in a..b, (-Hx x) * nonlinearRemainder (E x) (V x) + (J x - H x) * r x := by
  have cE : Continuous E := continuous_iff_continuousAt.mpr (fun x => (hE x).continuousAt)
  have cH : Continuous H := continuous_iff_continuousAt.mpr (fun x => (hH x).continuousAt)
  have cV : Continuous V := continuous_iff_continuousAt.mpr (fun x => (hV x).continuousAt)
  have cJ : Continuous J := continuous_iff_continuousAt.mpr (fun x => (hJ x).continuousAt)
  have hp := periodic_product_integral (fun x => V x - E x) (fun x => J x - H x)
    (fun x => Vx x - Ex x) (fun x => Jx x - Hx x) a b
    (fun x => (hV x).sub (hE x)) (fun x => (hJ x).sub (hH x))
    (cVx.sub cEx) (cJx.sub cHx) (by rw [pV, pE]) (by rw [pJ, pH])
  have hc : Continuous (fun x => -((Vx x - Ex x) * (J x - H x) +
      (V x - E x) * (Jx x - Hx x))) := by fun_prop
  have hn := nonlinearRemainder_continuous E V cE cV
  have hr : Continuous (fun x => (-Hx x) * nonlinearRemainder (E x) (V x) +
      (J x - H x) * r x) := by fun_prop
  simp_rw [densityRate_eq]
  rw [intervalIntegral.integral_add (hc.intervalIntegrable a b) (hr.intervalIntegrable a b),
    intervalIntegral.integral_neg, hp, neg_zero, zero_add]

/-- Two supplied classical fields on a common spatial period, with a residual
in the comparison magnetic equation. These are component equations and
regularity assumptions, not an assumed relative-energy evolution identity. -/
structure ClassicalKerrPair (a b : ℝ) (s : Set ℝ) where
  E : ℝ → ℝ → ℝ
  H : ℝ → ℝ → ℝ
  V : ℝ → ℝ → ℝ
  J : ℝ → ℝ → ℝ
  Ex : ℝ → ℝ → ℝ
  Hx : ℝ → ℝ → ℝ
  Vx : ℝ → ℝ → ℝ
  Jx : ℝ → ℝ → ℝ
  residual : ℝ → ℝ → ℝ
  continuous_E : ∀ t, Continuous (E t)
  continuous_H : ∀ t, Continuous (H t)
  continuous_V : ∀ t, Continuous (V t)
  continuous_J : ∀ t, Continuous (J t)
  continuous_Ex : ∀ t, Continuous (Ex t)
  continuous_Hx : ∀ t, Continuous (Hx t)
  continuous_Vx : ∀ t, Continuous (Vx t)
  continuous_Jx : ∀ t, Continuous (Jx t)
  continuous_residual : ∀ t, Continuous (residual t)
  spatial_E : ∀ t ∈ s, ∀ x, HasDerivAt (E t) (Ex t x) x
  spatial_H : ∀ t ∈ s, ∀ x, HasDerivAt (H t) (Hx t x) x
  spatial_V : ∀ t ∈ s, ∀ x, HasDerivAt (V t) (Vx t x) x
  spatial_J : ∀ t ∈ s, ∀ x, HasDerivAt (J t) (Jx t x) x
  time_E : ∀ t ∈ s, ∀ x,
    HasDerivAt (fun z => E z x) (-Hx t x / (1 + (E t x) ^ 2)) t
  time_H : ∀ t ∈ s, ∀ x, HasDerivAt (fun z => H z x) (-Ex t x) t
  time_V : ∀ t ∈ s, ∀ x,
    HasDerivAt (fun z => V z x) (-Jx t x / (1 + (V t x) ^ 2)) t
  time_J : ∀ t ∈ s, ∀ x,
    HasDerivAt (fun z => J z x) (-Vx t x + residual t x) t
  periodic_E : ∀ t ∈ s, E t b = E t a
  periodic_H : ∀ t ∈ s, H t b = H t a
  periodic_V : ∀ t ∈ s, V t b = V t a
  periodic_J : ∀ t ∈ s, J t b = J t a

namespace ClassicalKerrPair

variable {a b : ℝ} {s : Set ℝ} (u : ClassicalKerrPair a b s)

def density (t x : ℝ) : ℝ := relativeDensity (u.E t x) (u.H t x) (u.V t x) (u.J t x)

def rate (t x : ℝ) : ℝ := densityRate (u.E t x) (u.H t x) (u.V t x) (u.J t x)
  (u.Ex t x) (u.Hx t x) (u.Vx t x) (u.Jx t x) (u.residual t x)

/-- The unnormalized physical relative-energy integral over one period. -/
def energy (t : ℝ) : ℝ := ∫ x in a..b, u.density t x

theorem density_continuous (t : ℝ) : Continuous (u.density t) := by
  change Continuous (fun x => relativeDensity (u.E t x) (u.H t x) (u.V t x) (u.J t x))
  unfold relativeDensity electricGap FiniteEnergy.density constitutive
  have hE := u.continuous_E t
  have hH := u.continuous_H t
  have hV := u.continuous_V t
  have hJ := u.continuous_J t
  fun_prop

theorem rate_continuous (t : ℝ) : Continuous (u.rate t) := by
  change Continuous (fun x => densityRate (u.E t x) (u.H t x) (u.V t x) (u.J t x)
    (u.Ex t x) (u.Hx t x) (u.Vx t x) (u.Jx t x) (u.residual t x))
  unfold densityRate constitutive
  have hE := u.continuous_E t
  have hH := u.continuous_H t
  have hV := u.continuous_V t
  have hJ := u.continuous_J t
  have hEx := u.continuous_Ex t
  have hHx := u.continuous_Hx t
  have hVx := u.continuous_Vx t
  have hJx := u.continuous_Jx t
  have hr := u.continuous_residual t
  have hnE : ∀ x, 1 + u.E t x ^ 2 ≠ 0 :=
    fun x => ne_of_gt (FiniteEnergy.constitutive_denominator_pos (u.E t x))
  have hnV : ∀ x, 1 + u.V t x ^ 2 ≠ 0 :=
    fun x => ne_of_gt (FiniteEnergy.constitutive_denominator_pos (u.V t x))
  fun_prop (disch := assumption)

theorem density_hasDerivAt (t x : ℝ) (ht : t ∈ s) :
    HasDerivAt (fun z => u.density z x) (u.rate t x) t := by
  exact relativeDensity_hasDerivAt (fun z => u.E z x) (fun z => u.H z x)
    (fun z => u.V z x) (fun z => u.J z x) _ _ _ _ t
    (u.time_E t ht x) (u.time_H t ht x) (u.time_V t ht x) (u.time_J t ht x)

/-- Actual differentiation under the spatial integral, followed by periodic
IBP. The local dominating function controls the explicitly computed density
rate, not the desired energy identity. -/
theorem energy_hasDerivAt (t : ℝ) (hs : s ∈ 𝓝 t) (bound : ℝ → ℝ)
    (hb : IntervalIntegrable bound volume a b)
    (hbound : ∀ x ∈ Set.uIcc a b, ∀ z ∈ s, |u.rate z x| ≤ bound x) :
    HasDerivAt u.energy
      (∫ x in a..b, (-u.Hx t x) * nonlinearRemainder (u.E t x) (u.V t x) +
        (u.J t x - u.H t x) * u.residual t x) t := by
  have ht : t ∈ s := mem_of_mem_nhds hs
  have hd := integral_hasDerivAt_of_continuous_slices u.density u.rate a b t s bound
    hs u.density_continuous (u.rate_continuous t) hb hbound
    (fun x _ z hz => u.density_hasDerivAt z x hz)
  have hi := integrated_densityRate_eq (u.E t) (u.H t) (u.V t) (u.J t)
    (u.Ex t) (u.Hx t) (u.Vx t) (u.Jx t) (u.residual t) a b
    (u.spatial_E t ht) (u.spatial_H t ht) (u.spatial_V t ht) (u.spatial_J t ht)
    (u.continuous_Ex t) (u.continuous_Hx t) (u.continuous_Vx t)
    (u.continuous_Jx t) (u.continuous_residual t)
    (u.periodic_E t ht) (u.periodic_H t ht) (u.periodic_V t ht) (u.periodic_J t ht)
  change (∫ x in a..b, u.rate t x) = _ at hi
  rw [hi] at hd
  exact hd

theorem energy_nonneg (t : ℝ) (hab : a ≤ b) : 0 ≤ u.energy t := by
  exact intervalIntegral.integral_nonneg_of_forall hab
    (fun x => relativeDensity_nonneg (u.E t x) (u.H t x) (u.V t x) (u.J t x))

/-- The actual integral controls reconstruction of both real fields in
squared L2, before any spatial truncation is introduced. -/
theorem squared_error_integral_le (t : ℝ) (hab : a ≤ b) :
    (∫ x in a..b, (u.V t x - u.E t x) ^ 2 + (u.J t x - u.H t x) ^ 2) ≤
      2 * u.energy t := by
  have hE := u.continuous_E t
  have hH := u.continuous_H t
  have hV := u.continuous_V t
  have hJ := u.continuous_J t
  have cf : Continuous (fun x => (u.V t x - u.E t x) ^ 2 +
      (u.J t x - u.H t x) ^ 2) := by fun_prop
  have cg : Continuous (fun x => 2 * u.density t x) := (u.density_continuous t).const_mul 2
  have hi := intervalIntegral.integral_mono_on (μ := volume) hab (cf.intervalIntegrable a b)
    (cg.intervalIntegrable a b) (fun x _ => show
      (u.V t x - u.E t x) ^ 2 + (u.J t x - u.H t x) ^ 2 ≤ 2 * u.density t x from by
        dsimp [density, relativeDensity]
        linarith [square_error_le_gap (u.E t x) (u.V t x)])
  rw [intervalIntegral.integral_const_mul] at hi
  exact hi

/-- The continuum derivative inequality is obtained by integrating the
proved pointwise bound. M bounds the base magnetic spatial derivative. -/
theorem deriv_energy_le (t M : ℝ) (hs : s ∈ 𝓝 t) (hab : a ≤ b) (hM : 0 ≤ M)
    (bound : ℝ → ℝ) (hb : IntervalIntegrable bound volume a b)
    (hbound : ∀ x ∈ Set.uIcc a b, ∀ z ∈ s, |u.rate z x| ≤ bound x)
    (hHx : ∀ x ∈ Set.Icc a b, |u.Hx t x| ≤ M) :
    deriv u.energy t ≤ (3 * M + 1) * u.energy t +
      (∫ x in a..b, (u.residual t x) ^ 2) / 2 := by
  rw [(u.energy_hasDerivAt t hs bound hb hbound).deriv]
  have hH := u.continuous_H t
  have hJ := u.continuous_J t
  have hHx' := u.continuous_Hx t
  have hr := u.continuous_residual t
  have hn := nonlinearRemainder_continuous (u.E t) (u.V t)
    (u.continuous_E t) (u.continuous_V t)
  have cf : Continuous (fun x => (-u.Hx t x) * nonlinearRemainder (u.E t x) (u.V t x) +
      (u.J t x - u.H t x) * u.residual t x) := by fun_prop
  have cg : Continuous (fun x => (3 * M + 1) * u.density t x +
      (u.residual t x) ^ 2 / 2) :=
    ((u.density_continuous t).const_mul _).add ((hr.pow 2).div_const 2)
  have hi := intervalIntegral.integral_mono_on (μ := volume) hab (cf.intervalIntegrable a b)
    (cg.intervalIntegrable a b) (fun x hx =>
      relativeRate_le (u.E t x) (u.H t x) (u.V t x) (u.J t x)
        (-u.Hx t x) (u.residual t x) M hM (by simpa only [abs_neg] using hHx x hx))
  have c₁ := (u.density_continuous t).const_mul (3 * M + 1)
  have c₂ : Continuous (fun x => u.residual t x ^ 2 / 2) := by fun_prop
  rw [intervalIntegral.integral_add (c₁.intervalIntegrable a b) (c₂.intervalIntegrable a b),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_div] at hi
  exact hi

/-- The residual term of the actual continuum derivative becomes the
projection tail of the base magnetic derivative. The projection's operator
laws are visible hypotheses and are not replaced by the target energy law. -/
theorem energy_hasDerivAt_projection
    (t : ℝ) (hs : s ∈ 𝓝 t) (bound : ℝ → ℝ)
    (hb : IntervalIntegrable bound volume a b)
    (hbound : ∀ x ∈ Set.uIcc a b, ∀ z ∈ s, |u.rate z x| ≤ bound x)
    (P : (ℝ → ℝ) → (ℝ → ℝ)) (PVx : ℝ → ℝ)
    (hPcont : ∀ f, Continuous f → Continuous (P f))
    (hself : ∀ f g, Continuous f → Continuous g →
      (∫ x in a..b, P f x * g x) = ∫ x in a..b, f x * P g x)
    (hPJ : P (u.J t) = u.J t) (hPr : P (u.residual t) = fun _ => 0)
    (hPV : ∀ x, HasDerivAt (P (u.V t)) (PVx x) x) (cPVx : Continuous PVx)
    (pPV : P (u.V t) b = P (u.V t) a)
    (hr : ∀ x, u.residual t x = u.Vx t x - PVx x) :
    HasDerivAt u.energy
      (∫ x in a..b, (-u.Hx t x) * nonlinearRemainder (u.E t x) (u.V t x) +
        (u.Hx t x - P (u.Hx t) x) * u.V t x) t := by
  have ht : t ∈ s := mem_of_mem_nhds hs
  have hp := projection_residual_pairing P (u.H t) (u.J t) (u.V t) (u.Hx t)
    (u.Vx t) PVx (u.residual t) a b hPcont hself hPJ hPr
    (u.continuous_J t) (u.continuous_residual t)
    (u.spatial_H t ht) (u.spatial_V t ht) hPV (u.continuous_Hx t)
    (u.continuous_Vx t) cPVx (u.periodic_H t ht) (u.periodic_V t ht) pPV hr
  have hn : Continuous (fun x => (-u.Hx t x) *
      nonlinearRemainder (u.E t x) (u.V t x)) :=
    (u.continuous_Hx t).neg.mul (nonlinearRemainder_continuous (u.E t) (u.V t)
      (u.continuous_E t) (u.continuous_V t))
  have hc : Continuous (fun x => (u.J t x - u.H t x) * u.residual t x) :=
    ((u.continuous_J t).sub (u.continuous_H t)).mul (u.continuous_residual t)
  have hp' : Continuous (fun x => (u.Hx t x - P (u.Hx t) x) * u.V t x) :=
    ((u.continuous_Hx t).sub (hPcont (u.Hx t) (u.continuous_Hx t))).mul (u.continuous_V t)
  have hi₁ : (∫ x in a..b, (-u.Hx t x) * nonlinearRemainder (u.E t x) (u.V t x) +
      (u.J t x - u.H t x) * u.residual t x) =
      (∫ x in a..b, (-u.Hx t x) * nonlinearRemainder (u.E t x) (u.V t x)) +
      ∫ x in a..b, (u.J t x - u.H t x) * u.residual t x :=
    intervalIntegral.integral_add (hn.intervalIntegrable a b) (hc.intervalIntegrable a b)
  have hi₂ : (∫ x in a..b, (-u.Hx t x) * nonlinearRemainder (u.E t x) (u.V t x) +
      (u.Hx t x - P (u.Hx t) x) * u.V t x) =
      (∫ x in a..b, (-u.Hx t x) * nonlinearRemainder (u.E t x) (u.V t x)) +
      ∫ x in a..b, (u.Hx t x - P (u.Hx t) x) * u.V t x :=
    intervalIntegral.integral_add (hn.intervalIntegrable a b) (hp'.intervalIntegrable a b)
  have hd := u.energy_hasDerivAt t hs bound hb hbound
  rw [hi₁, hp, ← hi₂] at hd
  exact hd

end ClassicalKerrPair

end

end KerrKoopman.ContinuumRelative
