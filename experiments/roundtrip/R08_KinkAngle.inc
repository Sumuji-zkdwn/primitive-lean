import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# Round trip 8: soliton curvature → pendulum kink of the angle → stationary elastica

Input: round 7 (`κ = 2c sech(cs)`). Translation: integrate the curvature to the tangent
angle `θ(s) = 4 arctan(e^{cs})`, the kink of the stationary sine-Gordon (pendulum)
equation `θ'' = c² sin θ`. Back-translation into the baseline angle equation
`deriv (k θ') = -λ sin θ + μ cos θ` with `λ = -k c²`, `μ = 0`, and then, through the
baseline variational theorems, the kink is a genuine `Elastica.Stationary` angle for the
quadratic density on every segment `[0, ℓ]`. The baseline first integral has the value
`σ = k c²`, the same constant that round 7 needed in the curvature equation.
-/

noncomputable section
namespace RoundTrip08
open Real RoundTrip07

/-- The kink angle. -/
def kink (c s : ℝ) : ℝ := 4 * arctan (exp (c * s))

theorem cosh_eq_exp (x : ℝ) : cosh x = (exp x ^ 2 + 1) / (2 * exp x) := by
  rw [cosh_eq, exp_neg]
  field_simp

theorem sinh_eq_exp (x : ℝ) : sinh x = (exp x ^ 2 - 1) / (2 * exp x) := by
  rw [sinh_eq, exp_neg]
  field_simp

theorem hasDerivAt_kink (c s : ℝ) : HasDerivAt (kink c) (soliton c s) s := by
  have hl : HasDerivAt (fun t => c * t) c s := (hasDerivAt_id s).const_mul c |>.congr_deriv (by simp)
  have he : HasDerivAt (fun t => exp (c * t)) (exp (c * s) * c) s := (hasDerivAt_exp _).comp s hl
  have h := ((hasDerivAt_arctan (exp (c * s))).comp s he).const_mul 4
  unfold kink soliton
  convert h using 1
  rw [cosh_eq_exp]
  have hpos := exp_pos (c * s)
  field_simp
  ring

theorem deriv_kink (c : ℝ) : deriv (kink c) = soliton c :=
  funext fun s => (hasDerivAt_kink c s).deriv

/-- The curvature of the kink (baseline `Elastica.curvature`) is the soliton. -/
theorem curvature_kink (c : ℝ) : Elastica.curvature (kink c) = soliton c := deriv_kink c

theorem contDiff_kink (c : ℝ) {n : WithTop ℕ∞} : ContDiff ℝ n (kink c) := by
  unfold kink
  exact contDiff_const.mul (contDiff_arctan.comp (contDiff_exp.comp (contDiff_const.mul contDiff_id)))

theorem cos_two_arctan (w : ℝ) : cos (2 * arctan w) = (1 - w ^ 2) / (1 + w ^ 2) := by
  rw [cos_two_mul, cos_sq_arctan]
  field_simp
  ring

theorem sin_two_arctan (w : ℝ) : sin (2 * arctan w) = 2 * w / (1 + w ^ 2) := by
  rw [sin_two_mul, sin_arctan, cos_arctan,
    show 2 * (w / √(1 + w ^ 2)) * (1 / √(1 + w ^ 2)) = 2 * w / (√(1 + w ^ 2) * √(1 + w ^ 2)) by ring,
    Real.mul_self_sqrt (by positivity)]

theorem cos_kink (c s : ℝ) : cos (kink c s) = 1 - 2 / cosh (c * s) ^ 2 := by
  unfold kink
  rw [show 4 * arctan (exp (c * s)) = 2 * (2 * arctan (exp (c * s))) by ring, cos_two_mul,
    cos_two_arctan, cosh_eq_exp]
  have hpos := exp_pos (c * s)
  field_simp
  ring

theorem sin_kink (c s : ℝ) : sin (kink c s) = -2 * sinh (c * s) / cosh (c * s) ^ 2 := by
  unfold kink
  rw [show 4 * arctan (exp (c * s)) = 2 * (2 * arctan (exp (c * s))) by ring, sin_two_mul,
    cos_two_arctan, sin_two_arctan, cosh_eq_exp, sinh_eq_exp]
  have hpos := exp_pos (c * s)
  field_simp
  ring

/-- Baseline angle equation (pendulum form) with `λ = -k c²`, `μ = 0`. -/
theorem kink_angleEquation (k c s : ℝ) :
    deriv (fun t => k * soliton c t) s = -(-(k * c ^ 2)) * sin (kink c s) + 0 * cos (kink c s) := by
  rw [((hasDerivAt_soliton c s).const_mul k).deriv, sin_kink]
  unfold solitonDeriv
  ring

/-- The kink is a genuine stationary angle of the actual quadratic elastic energy on every
segment, obtained from the baseline variational theorems (not assumed). -/
theorem kink_stationary (k c : ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Elastica.Stationary (fun q => k * q ^ 2 / 2) (kink c) ℓ := by
  have hε : ContDiff ℝ 1 (fun q : ℝ => k * q ^ 2 / 2) := by fun_prop
  rw [Elastica.stationary_iff_firstVariation hℓ.le hε (contDiff_kink c)]
  have hM : ContDiff ℝ 1 (fun t => k * soliton c t) :=
    contDiff_const.mul ((contDiff_soliton c).of_le (by norm_num))
  have h := Elastica.stationary_of_angleEquation hℓ (contDiff_kink c (n := 0)).continuous hM
    (fun s _ => kink_angleEquation k c s)
  intro η hx hy
  have hrw : (fun s => deriv (fun q : ℝ => k * q ^ 2 / 2) (deriv (kink c) s) * deriv η.val s) =
      fun s => k * soliton c s * deriv η.val s := by
    funext s
    rw [(Elastica.quadratic_density_hasDerivAt k (deriv (kink c) s)).deriv, deriv_kink]
  simp only [hrw]
  exact h η hx hy

/-- The baseline first integral along the kink takes the value `σ = k c²`. -/
theorem kink_first_integral (k c s : ℝ) :
    soliton c s * (k * soliton c s) - k * soliton c s ^ 2 / 2 -
      (-(k * c ^ 2)) * cos (kink c s) - 0 * sin (kink c s) = k * c ^ 2 := by
  rw [cos_kink]
  unfold soliton
  have hc0 : cosh (c * s) ≠ 0 := (cosh_pos _).ne'
  field_simp
  ring

end RoundTrip08
