/-!
# Gravity observation descent and finite multipole witnesses

This supplement connects the verified gravity pair-cocycle model with F0
idempotent forgetting.  The exact F0 descent condition is a universal
statement for any observer.  For the symmetric two-body one-dimensional
family, the forgetful map keeps total mass and first moment but loses
the second moment and the external inverse-distance potential.

The physical potential uses a chosen 1/r kernel, away from the sources;
the statements are NOT three-dimensional multipole uniqueness claims.
-/

noncomputable section

namespace LinearInputGravityObservations

/-- An observation is well-defined on the fibers of a forgetful map. -/
def FactorsThrough {α β : Type*} (K : α → α) (O : α → β) : Prop :=
  ∀ x y, K x = K y → O x = O y

/-- Exact F0 criterion: the observer is constant on each fiber iff
it is unchanged by applying the idempotent retraction. -/
theorem factors_iff_invariant {α β : Type*} (K : α → α) (O : α → β)
    (hK : LinearInputF0.Idempotent K) :
    FactorsThrough K O ↔ ∀ x, O (K x) = O x := by
  constructor
  · intro h x
    exact (h x (K x) (hK x).symm).symm
  · intro h x y hxy
    calc
      O x = O (K x) := (h x).symm
      _ = O (K y) := congrArg O hxy
      _ = O y := h y

/-- If the observer is injective, exact forgetting must be trivial. -/
theorem injective_observer_forces_identity {α β : Type*}
    (K : α → α) (O : α → β)
    (hK : LinearInputF0.Idempotent K) (hO : Function.Injective O)
    (hFactor : FactorsThrough K O) : K = id := by
  funext x
  exact hO ((factors_iff_invariant K O hK).mp hFactor x)

/-- A state consists of the mass m of each of two equal bodies,
and their positive or signed half-separation a. -/
def forgetSeparation (s : ℝ × ℝ) : ℝ × ℝ := (s.1, 0)

theorem forgetSeparation_idempotent :
    LinearInputF0.Idempotent forgetSeparation := by
  intro s
  rfl

/-- Mass moments of the two point sources at -a and +a. -/
def symmetricMoment (s : ℝ × ℝ) (n : ℕ) : ℝ :=
  s.1 * ((-s.2) ^ n + s.2 ^ n)

/-- After forgetting separation both equal sources are placed at zero.
Equivalently the exterior model has a single effective source of mass 2m. -/
def lowMoments (s : ℝ × ℝ) : ℝ × ℝ :=
  (symmetricMoment s 0, symmetricMoment s 1)

theorem moment_zero_formula (m a : ℝ) :
    symmetricMoment (m, a) 0 = 2 * m := by
  simp [symmetricMoment]
  ring

theorem moment_one_formula (m a : ℝ) :
    symmetricMoment (m, a) 1 = 0 := by
  simp [symmetricMoment]
  ring

theorem moment_two_formula (m a : ℝ) :
    symmetricMoment (m, a) 2 = 2 * m * a ^ 2 := by
  simp [symmetricMoment]
  ring

/-- Forgetting separation preserves the monopole and dipole observations. -/
theorem lowMoments_invariant (s : ℝ × ℝ) :
    lowMoments (forgetSeparation s) = lowMoments s := by
  rcases s with ⟨m, a⟩
  simp [lowMoments, forgetSeparation, moment_zero_formula,
    moment_one_formula]

theorem lowMoments_factors :
    FactorsThrough forgetSeparation lowMoments := by
  exact (factors_iff_invariant forgetSeparation lowMoments
    forgetSeparation_idempotent).mpr lowMoments_invariant

/-- The first moment not conserved by merging is order two. -/
theorem moment_two_loss (m a : ℝ) :
    symmetricMoment (m, a) 2 -
      symmetricMoment (forgetSeparation (m, a)) 2 =
        2 * m * a ^ 2 := by
  simp [forgetSeparation, moment_two_formula]

theorem moment_two_detects_separation (m a : ℝ)
    (hm : m ≠ 0) (ha : a ≠ 0) :
    symmetricMoment (m, a) 2 ≠
      symmetricMoment (forgetSeparation (m, a)) 2 := by
  have hgap := moment_two_loss m a
  have hnon : 2 * m * a ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hm) (pow_ne_zero 2 ha)
  intro h
  rw [h, sub_self] at hgap
  exact hnon hgap.symm

/-- External inverse-distance profile on the ray beyond the two masses.
Only R>|a| is interpreted as a physical measurement. -/
def symmetricProfile (s : ℝ × ℝ) (R : ℝ) : ℝ :=
  s.1 / (R - s.2) + s.1 / (R + s.2)

theorem profile_after_forgetting (m a R : ℝ) :
    symmetricProfile (forgetSeparation (m, a)) R = 2 * m / R := by
  simp [symmetricProfile, forgetSeparation]
  ring

/-- The order-two correction is exact, not merely an asymptotic expansion. -/
theorem exact_quadrupole_correction
    (m a R : ℝ) (ha : 0 < a) (hR : a < R) :
    symmetricProfile (m, a) R -
      symmetricProfile (forgetSeparation (m, a)) R =
        (2 * m * a ^ 2) / (R * (R ^ 2 - a ^ 2)) := by
  have hRa : R - a ≠ 0 := ne_of_gt (sub_pos.mpr hR)
  have hRp : R + a ≠ 0 :=
    ne_of_gt (add_pos (lt_trans ha hR) ha)
  have hR0 : R ≠ 0 := ne_of_gt (lt_trans ha hR)
  have hquad : R ^ 2 - a ^ 2 ≠ 0 := by
    have hh : (R - a) * (R + a) ≠ 0 := mul_ne_zero hRa hRp
    have hfactor : (R - a) * (R + a) = R ^ 2 - a ^ 2 := by ring
    rw [hfactor] at hh
    exact hh
  rw [profile_after_forgetting]
  unfold symmetricProfile
  field_simp [hRa, hRp, hR0, hquad]
  ring

/-- Positive mass and nonzero separation make the correction nonzero. -/
theorem external_profile_detects_separation
    (m a R : ℝ) (hm : m ≠ 0) (ha : 0 < a) (hR : a < R) :
    symmetricProfile (m, a) R ≠
      symmetricProfile (forgetSeparation (m, a)) R := by
  intro h
  have hdiff := exact_quadrupole_correction m a R ha hR
  rw [h, sub_self] at hdiff
  have hR0 : R ≠ 0 := ne_of_gt (lt_trans ha hR)
  have hquad : R ^ 2 - a ^ 2 ≠ 0 := by
    have hminus : 0 < R - a := sub_pos.mpr hR
    have hplus : 0 < R + a :=
      add_pos (lt_trans ha hR) ha
    have hprod : 0 < (R - a) * (R + a) :=
      mul_pos hminus hplus
    have hfactor : (R - a) * (R + a) = R ^ 2 - a ^ 2 := by ring
    rw [hfactor] at hprod
    exact ne_of_gt hprod
  have hnon : (2 * m * a ^ 2) / (R * (R ^ 2 - a ^ 2)) ≠ 0 :=
    div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hm)
      (pow_ne_zero 2 ha.ne')) (mul_ne_zero hR0 hquad)
  exact hnon hdiff.symm

/-- The complete exterior profile does not factor through monopole/dipole
forgetting, even though the two lower moments factor exactly. -/
theorem full_profile_not_factors :
    ¬ FactorsThrough forgetSeparation
        (fun s : ℝ × ℝ => symmetricProfile s) := by
  intro h
  have hinv := (factors_iff_invariant
    forgetSeparation (fun s : ℝ × ℝ => symmetricProfile s)
    forgetSeparation_idempotent).mp h
  have hfun := hinv ((1 : ℝ), (1 / 2 : ℝ))
  have hpoint := congrFun hfun (2 : ℝ)
  have hne := external_profile_detects_separation
    1 (1 / 2) 2 (by norm_num) (by norm_num) (by norm_num)
  exact hne hpoint.symm

end LinearInputGravityObservations
