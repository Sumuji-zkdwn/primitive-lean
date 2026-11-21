import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Projective coordinates for a separately chosen synchronization law

This module studies the explicit homogeneous linear field
`u' = K*u/2 - δ*v/2`, `v' = δ*u/2 - K*v/2`.
It is an additional model, not a consequence of the elastica variational problem.
Its finite chart `q = v/u` has a Riccati equation.  The rational observations of
that chart are exactly `cos (2 * arctan q)` and `sin (2 * arctan q)`, and their
derivatives give the corresponding Adler phase equation.

Every trajectory theorem below takes its differential equation as a hypothesis
or differentiates an explicitly defined trajectory.  No general existence,
uniqueness, global attraction, celestial mechanism, or quantum interpretation is
claimed.  In particular `u = 0` is outside the finite chart; the field's tangency
to that axis at zero detuning is recorded separately.  The two sample slopes are local algebraic
data, not a formal stability theorem.
-/

noncomputable section

namespace ProjectiveLock

def fieldU (K δ u v : ℝ) : ℝ := K / 2 * u - δ / 2 * v

def fieldV (K δ u v : ℝ) : ℝ := δ / 2 * u - K / 2 * v

def riccati (K δ q : ℝ) : ℝ := δ / 2 * (1 + q ^ 2) - K * q

def reciprocalField (K δ p : ℝ) : ℝ := K * p - δ / 2 * (1 + p ^ 2)

def cosReadout (q : ℝ) : ℝ := (1 - q ^ 2) / (1 + q ^ 2)

def sinReadout (q : ℝ) : ℝ := 2 * q / (1 + q ^ 2)

def phase (q : ℝ) : ℝ := 2 * Real.arctan q

def decay (K q₀ t : ℝ) : ℝ := q₀ * Real.exp (-K * t)

theorem denominator_pos (q : ℝ) : 0 < 1 + q ^ 2 := by
  nlinarith [sq_nonneg q]

/-- The actual quotient derivative of the homogeneous linear field. -/
theorem quotient_hasDerivAt (K δ : ℝ) (u v : ℝ → ℝ) (t : ℝ)
    (hu : HasDerivAt u (fieldU K δ (u t) (v t)) t)
    (hv : HasDerivAt v (fieldV K δ (u t) (v t)) t)
    (hu₀ : u t ≠ 0) :
    HasDerivAt (fun z => v z / u z) (riccati K δ (v t / u t)) t := by
  convert hv.div hu hu₀ using 1
  dsimp [fieldU, fieldV, riccati]
  field_simp [hu₀]
  ring

/-- The other affine chart has the opposite Riccati field. -/
theorem reciprocal_field (K δ q : ℝ) (hq : q ≠ 0) :
    -(riccati K δ q) / q ^ 2 = reciprocalField K δ q⁻¹ := by
  dsimp [riccati, reciprocalField]
  field_simp [hq]
  ring

theorem reciprocal_hasDerivAt (K δ : ℝ) (q : ℝ → ℝ) (t : ℝ)
    (hq : HasDerivAt q (riccati K δ (q t)) t) (hq₀ : q t ≠ 0) :
    HasDerivAt (fun z => (q z)⁻¹) (reciprocalField K δ (q t)⁻¹) t := by
  convert hq.inv hq₀ using 1
  exact (reciprocal_field K δ (q t) hq₀).symm

theorem zero_detuning (K q : ℝ) : riccati K 0 q = -K * q := by
  simp [riccati]

theorem decay_initial (K q₀ : ℝ) : decay K q₀ 0 = q₀ := by
  simp [decay]

/-- An explicit finite-chart solution at zero detuning. -/
theorem decay_hasDerivAt (K q₀ t : ℝ) :
    HasDerivAt (decay K q₀) (riccati K 0 (decay K q₀ t)) t := by
  have he : HasDerivAt (fun z : ℝ => Real.exp (-K * z))
      (Real.exp (-K * t) * (-K)) t := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id t).const_mul (-K)).exp
  convert! he.const_mul q₀ using 1
  dsimp [decay, riccati]
  ring

theorem decay_ne_zero (K q₀ t : ℝ) (hq₀ : q₀ ≠ 0) : decay K q₀ t ≠ 0 := by
  exact mul_ne_zero hq₀ (Real.exp_ne_zero _)

/-- This algebraic identity uses totalized division and holds for all `u`.
Its interpretation as a finite projective chart requires `u ≠ 0`: shrinking
only `v` then gives the explicit zero-detuning chart trajectory. -/
theorem plane_contraction_ratio (K u v t : ℝ) :
    (Real.exp (-K * t) * v) / u = decay K (v / u) t := by
  dsimp [decay]
  ring

theorem readout_on_unit_circle (q : ℝ) :
    cosReadout q ^ 2 + sinReadout q ^ 2 = 1 := by
  have hden : 1 + q ^ 2 ≠ 0 := ne_of_gt (denominator_pos q)
  dsimp [cosReadout, sinReadout]
  field_simp [hden]
  ring

theorem cosReadout_hasDerivAt (q : ℝ) :
    HasDerivAt cosReadout (-4 * q / (1 + q ^ 2) ^ 2) q := by
  have hpow := (hasDerivAt_id q).pow 2
  have hn := (hasDerivAt_const q (1 : ℝ)).sub hpow
  have hd := (hasDerivAt_const q (1 : ℝ)).add hpow
  convert! hn.div hd (ne_of_gt (denominator_pos q)) using 1
  dsimp
  ring

theorem sinReadout_hasDerivAt (q : ℝ) :
    HasDerivAt sinReadout (2 * (1 - q ^ 2) / (1 + q ^ 2) ^ 2) q := by
  have hn := (hasDerivAt_id q).const_mul 2
  have hd := (hasDerivAt_const q (1 : ℝ)).add ((hasDerivAt_id q).pow 2)
  convert! hn.div hd (ne_of_gt (denominator_pos q)) using 1
  dsimp
  ring

theorem observed_cos_hasDerivAt (K δ : ℝ) (q : ℝ → ℝ) (t : ℝ)
    (hq : HasDerivAt q (riccati K δ (q t)) t) :
    HasDerivAt (fun z => cosReadout (q z))
      (-δ * sinReadout (q t) + K * sinReadout (q t) ^ 2) t := by
  convert! (cosReadout_hasDerivAt (q t)).comp t hq using 1
  have hden : 1 + q t ^ 2 ≠ 0 := ne_of_gt (denominator_pos (q t))
  dsimp [sinReadout, riccati]
  field_simp [hden]
  ring

theorem observed_sin_hasDerivAt (K δ : ℝ) (q : ℝ → ℝ) (t : ℝ)
    (hq : HasDerivAt q (riccati K δ (q t)) t) :
    HasDerivAt (fun z => sinReadout (q z))
      (δ * cosReadout (q t) - K * cosReadout (q t) * sinReadout (q t)) t := by
  convert! (sinReadout_hasDerivAt (q t)).comp t hq using 1
  have hden : 1 + q t ^ 2 ≠ 0 := ne_of_gt (denominator_pos (q t))
  dsimp [cosReadout, sinReadout, riccati]
  field_simp [hden]

/-- First coordinate of `M² = (K² - δ²) / 4 * I`. -/
theorem fieldU_squared (K δ u v : ℝ) :
    fieldU K δ (fieldU K δ u v) (fieldV K δ u v) = (K ^ 2 - δ ^ 2) / 4 * u := by
  dsimp [fieldU, fieldV]
  ring

/-- Second coordinate of the same homogeneous identity. -/
theorem fieldV_squared (K δ u v : ℝ) :
    fieldV K δ (fieldU K δ u v) (fieldV K δ u v) = (K ^ 2 - δ ^ 2) / 4 * v := by
  dsimp [fieldU, fieldV]
  ring

/-- The nonzero vertical axis is tangent to the field precisely at `δ = 0`. -/
theorem infinity_axis_tangent_iff (K δ v : ℝ) (hv : v ≠ 0) :
    fieldU K δ 0 v = 0 ↔ δ = 0 := by
  simp [fieldU, hv]

theorem infinity_zero_detuning (K v : ℝ) :
    fieldU K 0 0 v = 0 ∧ fieldV K 0 0 v = -K / 2 * v := by
  constructor <;> dsimp [fieldU, fieldV] <;> ring

/-- An explicit trajectory on the omitted axis.  If `v₀ ≠ 0`, `decay_ne_zero`
shows that it represents the projective point at infinity for every real time. -/
theorem infinity_trajectory_hasDerivAt (K v₀ t : ℝ) :
    HasDerivAt (fun _ : ℝ => 0) (fieldU K 0 0 (decay (K / 2) v₀ t)) t ∧
    HasDerivAt (decay (K / 2) v₀) (fieldV K 0 0 (decay (K / 2) v₀ t)) t := by
  constructor
  · simpa [fieldU] using hasDerivAt_const t (0 : ℝ)
  · convert decay_hasDerivAt (K / 2) v₀ t using 1
    dsimp [fieldV, riccati]
    ring

theorem discriminant_identity (K δ q : ℝ) :
    (δ * q - K) ^ 2 - (K ^ 2 - δ ^ 2) = 2 * δ * riccati K δ q := by
  dsimp [riccati]
  ring

theorem root_discriminant_nonneg (K δ q : ℝ) (hq : riccati K δ q = 0) :
    0 ≤ K ^ 2 - δ ^ 2 := by
  have h := discriminant_identity K δ q
  rw [hq] at h
  nlinarith [sq_nonneg (δ * q - K)]

theorem no_root_beyond_threshold (K δ : ℝ) (h : K ^ 2 < δ ^ 2) (q : ℝ) :
    riccati K δ q ≠ 0 := by
  intro hq
  have hn := root_discriminant_nonneg K δ q hq
  linarith

theorem threshold_double_root (K q : ℝ) :
    riccati K K q = K / 2 * (q - 1) ^ 2 := by
  dsimp [riccati]
  ring

theorem sample_root_small : riccati 1 (3 / 5) (1 / 3) = 0 := by
  norm_num [riccati]

theorem sample_root_large : riccati 1 (3 / 5) 3 = 0 := by
  norm_num [riccati]

theorem riccati_hasDerivAt (K δ q : ℝ) :
    HasDerivAt (riccati K δ) (δ * q - K) q := by
  have hquad := ((hasDerivAt_const q (1 : ℝ)).add
    ((hasDerivAt_id q).pow 2)).const_mul (δ / 2)
  have hlin := (hasDerivAt_id q).const_mul K
  convert! hquad.sub hlin using 1
  dsimp
  ring

theorem sample_slope_small :
    HasDerivAt (riccati 1 (3 / 5)) (-4 / 5) (1 / 3) := by
  convert riccati_hasDerivAt 1 (3 / 5) (1 / 3) using 1
  norm_num

theorem sample_slope_large :
    HasDerivAt (riccati 1 (3 / 5)) (4 / 5) 3 := by
  convert riccati_hasDerivAt 1 (3 / 5) 3 using 1
  norm_num

/-- The rational sine readout is the sine of the reconstructed finite phase. -/
theorem sin_phase (q : ℝ) : Real.sin (phase q) = sinReadout q := by
  have hs : Real.sin (Real.arctan q) = q * Real.cos (Real.arctan q) := by
    have ht := Real.tan_arctan q
    rw [Real.tan_eq_sin_div_cos] at ht
    exact (div_eq_iff (ne_of_gt (Real.cos_arctan_pos q))).mp ht
  dsimp [phase]
  rw [Real.sin_two_mul, hs]
  calc
    2 * (q * Real.cos (Real.arctan q)) * Real.cos (Real.arctan q) =
        2 * q * Real.cos (Real.arctan q) ^ 2 := by ring
    _ = 2 * q * (1 / (1 + q ^ 2)) := by rw [Real.cos_sq_arctan]
    _ = sinReadout q := by dsimp [sinReadout]; ring

theorem cos_phase (q : ℝ) : Real.cos (phase q) = cosReadout q := by
  have hden : 1 + q ^ 2 ≠ 0 := ne_of_gt (denominator_pos q)
  dsimp [phase]
  rw [Real.cos_two_mul, Real.cos_sq_arctan]
  dsimp [cosReadout]
  field_simp [hden]
  ring

theorem phase_hasDerivAt (q : ℝ) :
    HasDerivAt phase (2 / (1 + q ^ 2)) q := by
  convert! (Real.hasDerivAt_arctan q).const_mul 2 using 1
  ring

/-- A supplied Riccati trajectory induces the Adler ODE on its finite chart. -/
theorem phase_ode_hasDerivAt (K δ : ℝ) (q : ℝ → ℝ) (t : ℝ)
    (hq : HasDerivAt q (riccati K δ (q t)) t) :
    HasDerivAt (fun z => phase (q z))
      (δ - K * Real.sin (phase (q t))) t := by
  convert! (phase_hasDerivAt (q t)).comp t hq using 1
  rw [sin_phase]
  have hden : 1 + q t ^ 2 ≠ 0 := ne_of_gt (denominator_pos (q t))
  dsimp [sinReadout, riccati]
  field_simp [hden]

end ProjectiveLock
