import Mathlib.Tactic

/-!
# A passive delayed-gel toy model: energy law and static obstruction

This is a finite-dimensional constitutive model, NOT an Einstein equation,
a proof of a Skyrmion, or a demonstration of Lorentz invariance.

On each oriented edge, strain is the difference of endpoint displacements.
The internal memory variable relaxes by a gradient-flow rule. Lean proves
the algebraic edge energy law, positivity and the no-lump result for a
relaxed three-site chain. The arbitrary finite-graph identity and the
3D cube simulation are treated in the accompanying independent checker.
-/

namespace PassiveGelDelay

/-- Restoring drive from the lag strain-memory; quartic hardening. -/
def drive (b quartic lag : ℝ) : ℝ :=
  b * lag + quartic * lag ^ 3

/-- Edge stress, with relaxed quadratic elasticity and lag hardening. -/
def stress (a b quartic strain memory : ℝ) : ℝ :=
  a * strain + drive b quartic (strain - memory)

/-- Stored edge energy; kinetic energy belongs to vertices. -/
def stored (a b quartic strain memory : ℝ) : ℝ :=
  a * strain ^ 2 / 2 +
    b * (strain - memory) ^ 2 / 2 +
    quartic * (strain - memory) ^ 4 / 4

theorem stored_nonnegative
    (a b quartic strain memory : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hq : 0 ≤ quartic) :
    0 ≤ stored a b quartic strain memory := by
  unfold stored
  positivity

/-- The static stress once the internal lag has fully relaxed. -/
theorem stress_relaxed (a b quartic strain : ℝ) :
    stress a b quartic strain strain = a * strain := by
  simp [stress, drive]

/-- The nonlinearity always raises instantaneous tangent stiffness. -/
theorem hardening_tangent_lower_bound
    (a b quartic lag : ℝ) (hq : 0 ≤ quartic) :
    a + b ≤ a + b + 3 * quartic * lag ^ 2 := by
  have h : 0 ≤ quartic * lag ^ 2 := mul_nonneg hq (sq_nonneg lag)
  nlinarith

/-- For b>0 and quartic>=0 the internal relaxation drive vanishes
    precisely when the memory has caught up with the strain. -/
theorem drive_zero_iff
    (b quartic lag : ℝ) (hb : 0 < b) (hq : 0 ≤ quartic) :
    drive b quartic lag = 0 ↔ lag = 0 := by
  constructor
  · intro he
    have hnonneg : 0 ≤ quartic * lag ^ 2 := mul_nonneg hq (sq_nonneg lag)
    have hfactor : b + quartic * lag ^ 2 ≠ 0 :=
      ne_of_gt (by linarith)
    have hprod : lag * (b + quartic * lag ^ 2) = 0 := by
      unfold drive at he
      nlinarith [he]
    exact (mul_eq_zero.mp hprod).resolve_right hfactor
  · intro he
    subst lag
    simp [drive]

/-- The exact algebraic energy identity on one edge, given
    compatible mechanical kinetic exchange and internal relaxation.
    The graph incidence cancellation supplies hkin upon summation. -/
theorem edge_dissipation_identity
    (a b quartic gamma strain memory strainRate memoryRate kineticRate : ℝ)
    (hkin :
      kineticRate + stress a b quartic strain memory * strainRate = 0)
    (hrel : memoryRate = gamma * drive b quartic (strain - memory)) :
    kineticRate + a * strain * strainRate +
        drive b quartic (strain - memory) * (strainRate - memoryRate)
      = -gamma * (drive b quartic (strain - memory)) ^ 2 := by
  rw [hrel]
  calc
    _ = (kineticRate + stress a b quartic strain memory * strainRate) -
          gamma * (drive b quartic (strain - memory)) ^ 2 := by
      unfold stress drive
      ring
    _ = -gamma * (drive b quartic (strain - memory)) ^ 2 := by
      rw [hkin]
      ring

/-- The energy production is nonpositive for nonnegative mobility. -/
theorem edge_dissipation_nonpositive
    (a b quartic gamma strain memory strainRate memoryRate kineticRate : ℝ)
    (hg : 0 ≤ gamma)
    (hkin :
      kineticRate + stress a b quartic strain memory * strainRate = 0)
    (hrel : memoryRate = gamma * drive b quartic (strain - memory)) :
    kineticRate + a * strain * strainRate +
        drive b quartic (strain - memory) * (strainRate - memoryRate) ≤ 0 := by
  rw [edge_dissipation_identity a b quartic gamma strain memory
        strainRate memoryRate kineticRate hkin hrel]
  have h : 0 ≤ gamma * (drive b quartic (strain - memory)) ^ 2 :=
    mul_nonneg hg (sq_nonneg _)
  linarith

/-- A relaxed three-site chain cannot support an isolated static
    displacement contrast when a>0 and no external forces act.
    Endpoint force balance demands zero edge stresses. -/
theorem relaxed_three_site_no_lump
    (a b quartic x0 x1 x2 : ℝ) (ha : 0 < a)
    (hleft : stress a b quartic (x1 - x0) (x1 - x0) = 0)
    (hright : stress a b quartic (x2 - x1) (x2 - x1) = 0) :
    x0 = x1 ∧ x1 = x2 := by
  have h01 : a * (x1 - x0) = 0 := by
    simpa only [stress_relaxed] using hleft
  have h12 : a * (x2 - x1) = 0 := by
    simpa only [stress_relaxed] using hright
  constructor
  · have he : x1 - x0 = 0 :=
      (mul_eq_zero.mp h01).resolve_left (ne_of_gt ha)
    exact (sub_eq_zero.mp he).symm
  · have he : x2 - x1 = 0 :=
      (mul_eq_zero.mp h12).resolve_left (ne_of_gt ha)
    exact (sub_eq_zero.mp he).symm

end PassiveGelDelay
