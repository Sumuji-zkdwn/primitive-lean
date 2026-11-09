
/-!
# Projected continuum relative-energy rate and normalization

The energy derivative is derived from the supplied classical component PDEs
by the existing actual interval-integral theorem. Projection orthogonality is
derived from self-adjointness and idempotence. The concrete Fourier projection
and construction of the comparison fields from GalerkinFlow are separate bridges.
-/

namespace KerrKoopman.ContinuumGalerkin

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter
open scoped Topology Interval
open RelativeEnergy RelativeDynamics ContinuumRelative IntegralTail

/-- Only operator laws are bundled here, not an energy evolution identity. -/
structure IntervalProjection (a b : ℝ) where
  apply : (ℝ → ℝ) → (ℝ → ℝ)
  continuous : ∀ f, Continuous f → Continuous (apply f)
  selfadjoint : ∀ f g, Continuous f → Continuous g →
    (∫ x in a..b, apply f x * g x) = ∫ x in a..b, f x * apply g x
  idempotent : ∀ f, Continuous f → apply (apply f) = apply f

theorem projection_tail_orthogonal {a b : ℝ} (P : IntervalProjection a b)
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    (∫ x in a..b, (f x - P.apply f x) * P.apply g x) = 0 := by
  have hcg := P.continuous g hg
  have hcf := P.continuous f hf
  have hi := P.selfadjoint f (P.apply g) hf hcg
  rw [P.idempotent g hg] at hi
  have he : (fun x => (f x - P.apply f x) * P.apply g x) =
      (fun x => f x * P.apply g x - P.apply f x * P.apply g x) := by
    funext x
    ring
  have hsub : (∫ x in a..b, f x * P.apply g x - P.apply f x * P.apply g x) =
      (∫ x in a..b, f x * P.apply g x) - ∫ x in a..b, P.apply f x * P.apply g x :=
    intervalIntegral.integral_sub ((hf.mul hcg).intervalIntegrable a b)
      ((hcf.mul hcg).intervalIntegrable a b)
  rw [he, hsub, hi, sub_self]

theorem electricGap_integral_le_energy {a b : ℝ} {s : Set ℝ}
    (u : ClassicalKerrPair a b s) (t : ℝ) (hab : a ≤ b) :
    (∫ x in a..b, electricGap (u.E t x) (u.V t x)) ≤ u.energy t := by
  have hE := u.continuous_E t
  have hV := u.continuous_V t
  have cg : Continuous (fun x => electricGap (u.E t x) (u.V t x)) := by
    unfold electricGap FiniteEnergy.density Riccati.constitutive
    fun_prop
  exact intervalIntegral.integral_mono_on (μ := volume) hab (cg.intervalIntegrable a b)
    ((u.density_continuous t).intervalIntegrable a b) (fun x _ => by
      change electricGap (u.E t x) (u.V t x) ≤
        electricGap (u.E t x) (u.V t x) + (u.J t x - u.H t x)^2 / 2
      linarith [sq_nonneg (u.J t x - u.H t x)])

/-- The projected integral rate only needs true-field tails, not Vx or Jx bounds. -/
theorem projected_rate_le {a b : ℝ} {s : Set ℝ}
    (u : ClassicalKerrPair a b s) (P : IntervalProjection a b)
    (t M A B : ℝ) (hab : a ≤ b) (hM : 0 ≤ M) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hHx : ∀ x ∈ Icc a b, |u.Hx t x| ≤ M)
    (hA2 : (∫ x in a..b, (u.Hx t x - P.apply (u.Hx t) x)^2) ≤ A^2)
    (hB2 : (∫ x in a..b, (u.E t x - P.apply (u.E t) x)^2) ≤ B^2) :
    (∫ x in a..b, (-u.Hx t x) * nonlinearRemainder (u.E t x) (u.V t x) +
      (u.Hx t x - P.apply (u.Hx t) x) * u.V t x) ≤
      (3*M+1) * u.energy t + A^2/2 + A*B := by
  have hE := u.continuous_E t
  have hV := u.continuous_V t
  have hH := u.continuous_Hx t
  have hPH := P.continuous (u.Hx t) hH
  have hPE := P.continuous (u.E t) hE
  have hn := nonlinearRemainder_continuous (u.E t) (u.V t) hE hV
  have cn : Continuous (fun x => (-u.Hx t x) * nonlinearRemainder (u.E t x) (u.V t x)) := by
    fun_prop
  have cg : Continuous (fun x => electricGap (u.E t x) (u.V t x)) := by
    unfold electricGap FiniteEnergy.density Riccati.constitutive
    fun_prop
  have ct : Continuous (fun x => (u.Hx t x - P.apply (u.Hx t) x) * u.V t x) := by
    fun_prop
  have hnon := intervalIntegral.integral_mono_on (μ := volume) hab
    (cn.intervalIntegrable a b) ((cg.const_mul (3*M)).intervalIntegrable a b)
    (fun x hx => nonlinear_term_le (u.E t x) (u.V t x) (-u.Hx t x) M hM
      (by simpa only [abs_neg] using hHx x hx))
  rw [intervalIntegral.integral_const_mul] at hnon
  have htail := tail_field_le (fun x => u.Hx t x - P.apply (u.Hx t) x)
    (u.E t) (u.V t) (P.apply (u.E t)) a b A B hab (hH.sub hPH) hE hV hPE hA hB
    hA2 hB2 (projection_tail_orthogonal P (u.Hx t) (u.E t) hH hE)
  rw [intervalIntegral.integral_add (cn.intervalIntegrable a b) (ct.intervalIntegrable a b)]
  have hgap := electricGap_integral_le_energy u t hab
  nlinarith

namespace ClassicalKerrPair

variable {a b : ℝ} {s : Set ℝ} (u : ContinuumRelative.ClassicalKerrPair a b s)

/-- Mean relative energy, with the same normalization as probability-Haar L2. -/
def normalizedEnergy (t : ℝ) : ℝ := u.energy t / (b-a)

theorem normalizedEnergy_nonneg (t : ℝ) (hab : a < b) :
    0 ≤ normalizedEnergy u t := div_nonneg (u.energy_nonneg t hab.le) (sub_nonneg.mpr hab.le)

theorem normalized_squared_error_le (t : ℝ) (hab : a < b) :
    (∫ x in a..b, (u.V t x-u.E t x)^2 + (u.J t x-u.H t x)^2) / (b-a) ≤
      2 * normalizedEnergy u t := by
  have hi := div_le_div_of_nonneg_right (u.squared_error_integral_le t hab.le)
    (sub_nonneg.mpr hab.le)
  simpa only [normalizedEnergy, mul_div_assoc] using hi

/-- Actual PDE differentiation plus constructed operator orthogonality and tail estimates. -/
theorem deriv_energy_le_projection
    (t M A B : ℝ) (hs : s ∈ 𝓝 t) (hab : a ≤ b) (hM : 0 ≤ M) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (bound : ℝ → ℝ) (hb : IntervalIntegrable bound volume a b)
    (hbound : ∀ x ∈ uIcc a b, ∀ z ∈ s, |u.rate z x| ≤ bound x)
    (P : IntervalProjection a b) (PVx : ℝ → ℝ)
    (hPJ : P.apply (u.J t) = u.J t) (hPr : P.apply (u.residual t) = fun _ => 0)
    (hPV : ∀ x, HasDerivAt (P.apply (u.V t)) (PVx x) x)
    (cPVx : Continuous PVx) (pPV : P.apply (u.V t) b = P.apply (u.V t) a)
    (hr : ∀ x, u.residual t x = u.Vx t x - PVx x)
    (hHx : ∀ x ∈ Icc a b, |u.Hx t x| ≤ M)
    (hA2 : (∫ x in a..b, (u.Hx t x-P.apply (u.Hx t) x)^2) ≤ A^2)
    (hB2 : (∫ x in a..b, (u.E t x-P.apply (u.E t) x)^2) ≤ B^2) :
    deriv u.energy t ≤ (3*M+1)*u.energy t + A^2/2 + A*B := by
  rw [(u.energy_hasDerivAt_projection t hs bound hb hbound P.apply PVx
    P.continuous P.selfadjoint hPJ hPr hPV cPVx pPV hr).deriv]
  exact projected_rate_le u P t M A B hab hM hA hB hHx hA2 hB2

/-- Normalized tails produce the normalized physical-time rate without a missing period factor. -/
theorem deriv_normalizedEnergy_le_projection
    (t M A B : ℝ) (hs : s ∈ 𝓝 t) (hab : a < b) (hM : 0 ≤ M) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (bound : ℝ → ℝ) (hb : IntervalIntegrable bound volume a b)
    (hbound : ∀ x ∈ uIcc a b, ∀ z ∈ s, |u.rate z x| ≤ bound x)
    (P : IntervalProjection a b) (PVx : ℝ → ℝ)
    (hPJ : P.apply (u.J t) = u.J t) (hPr : P.apply (u.residual t) = fun _ => 0)
    (hPV : ∀ x, HasDerivAt (P.apply (u.V t)) (PVx x) x)
    (cPVx : Continuous PVx) (pPV : P.apply (u.V t) b = P.apply (u.V t) a)
    (hr : ∀ x, u.residual t x = u.Vx t x - PVx x)
    (hHx : ∀ x ∈ Icc a b, |u.Hx t x| ≤ M)
    (hA2 : (∫ x in a..b, (u.Hx t x-P.apply (u.Hx t) x)^2)/(b-a) ≤ A^2)
    (hB2 : (∫ x in a..b, (u.E t x-P.apply (u.E t) x)^2)/(b-a) ≤ B^2) :
    deriv (normalizedEnergy u) t ≤ (3*M+1)*normalizedEnergy u t + A^2/2 + A*B := by
  have hL : 0 < b-a := sub_pos.mpr hab
  have hsq : Real.sqrt (b-a)^2 = b-a := Real.sq_sqrt hL.le
  have hA' : (∫ x in a..b, (u.Hx t x-P.apply (u.Hx t) x)^2) ≤
      (Real.sqrt (b-a)*A)^2 := by
    rw [mul_pow, hsq]
    nlinarith [(div_le_iff₀ hL).mp hA2]
  have hB' : (∫ x in a..b, (u.E t x-P.apply (u.E t) x)^2) ≤
      (Real.sqrt (b-a)*B)^2 := by
    rw [mul_pow, hsq]
    nlinarith [(div_le_iff₀ hL).mp hB2]
  have hi := deriv_energy_le_projection u t M (Real.sqrt (b-a)*A) (Real.sqrt (b-a)*B)
    hs hab.le hM (mul_nonneg (Real.sqrt_nonneg _) hA) (mul_nonneg (Real.sqrt_nonneg _) hB)
    bound hb hbound P PVx hPJ hPr hPV cPVx pPV hr hHx hA' hB'
  have hd := u.energy_hasDerivAt t hs bound hb hbound
  have hderiv : deriv (normalizedEnergy u) t = deriv u.energy t / (b-a) := by
    exact (hd.div_const (b-a)).deriv.trans (by rw [hd.deriv])
  rw [hderiv, normalizedEnergy]
  apply (div_le_iff₀ hL).mpr
  have he : ((3*M+1)*(u.energy t/(b-a)) + A^2/2 + A*B)*(b-a) =
      (3*M+1)*u.energy t + (Real.sqrt (b-a)*A)^2/2 +
        (Real.sqrt (b-a)*A)*(Real.sqrt (b-a)*B) := by
    field_simp
    rw [hsq]
    ring
  rw [he]
  exact hi

end ClassicalKerrPair
end
end KerrKoopman.ContinuumGalerkin
