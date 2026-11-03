/-!
Viscous state rewriting inside the existing primitive-lean polynomial E.

DRAFT: Prepared against the verified names in the PR #3 research branch,
but NOT compiled by Lean in this environment.  This file is intended to be
appended to the joint proof assembly AFTER VariablePairObservations.inc.
It makes no claim that viscosity is forced by the earlier axioms.

The quadratic rewrite penalty is an exact parameter shift of the ORIGINAL
energy family.  Global proximal minimality (an explicit hypothesis) implies
energy descent and, by differentiation, the viscous force law.
-/

noncomputable section

namespace LinearInputViscousRewrite

open LinearInputVariablePairs

/-- E(z) plus the quadratic cost of rewriting old -> z.  The coefficient
alpha equals eta/h when viscosity eta and timestep h are positive. -/
def proximalEnergy (k lam a c y u alpha old z : ℝ) : ℝ :=
  energy k lam a c z y u + alpha / 2 * (z - old) ^ 2

/-- Viscous rewriting closes EXACTLY inside primitive's polynomial E family. -/
theorem proximal_is_parameter_shift
    (k lam a c y u alpha old z : ℝ) :
    proximalEnergy k lam a c y u alpha old z =
      energy (k + alpha) lam a c z y (u + alpha * old) +
        alpha * old ^ 2 / 2 := by
  unfold proximalEnergy energy
  ring

/-- The actual energy gradient, reused from the existing proof. -/
theorem energy_x_derivative (k lam a c x y u : ℝ) :
    deriv (fun z => energy k lam a c z y u) x =
      k * x + lam * x ^ 3 - c * y - u := by
  exact (hasDerivAt_energy_x k lam a c x y u).deriv

/-- Derivative of the new objective; no postulated force is used. -/
theorem proximal_hasDerivAt
    (k lam a c y u alpha old z : ℝ) :
    HasDerivAt (fun w => proximalEnergy k lam a c y u alpha old w)
      (k * z + lam * z ^ 3 - c * y - u + alpha * (z - old)) z := by
  have hE := hasDerivAt_energy_x k lam a c z y u
  have hP : HasDerivAt (fun w : ℝ => alpha / 2 * (w - old) ^ 2)
      (alpha * (z - old)) z := by
    convert ((((hasDerivAt_id z).sub_const old).pow 2).const_mul (alpha / 2))
      using 1 <;> ring
  simpa only [proximalEnergy] using hE.add hP

/-- The resisting force emerges from minimization, not as an independent law. -/
theorem viscous_force_from_global_minimum
    (k lam a c y u alpha old z : ℝ)
    (hmin : ∀ w : ℝ,
      proximalEnergy k lam a c y u alpha old z ≤
        proximalEnergy k lam a c y u alpha old w) :
    u - (k * z + lam * z ^ 3 - c * y) = alpha * (z - old) := by
  have hlocal : IsLocalMin
      (fun w => proximalEnergy k lam a c y u alpha old w) z :=
    Filter.Eventually.of_forall hmin
  have hd : deriv (fun w => proximalEnergy k lam a c y u alpha old w) z = 0 :=
    hlocal.deriv_eq_zero
  rw [(proximal_hasDerivAt k lam a c y u alpha old z).deriv] at hd
  linarith

/-- The strong discrete energy inequality, without any convexity assumption. -/
theorem proximal_energy_bound
    (k lam a c y u alpha old z : ℝ)
    (hmin : ∀ w : ℝ,
      proximalEnergy k lam a c y u alpha old z ≤
        proximalEnergy k lam a c y u alpha old w) :
    energy k lam a c z y u + alpha / 2 * (z - old) ^ 2 ≤
      energy k lam a c old y u := by
  have h := hmin old
  simpa [proximalEnergy] using h

/-- Energy is nonincreasing when the rewrite resistance is nonnegative. -/
theorem proximal_energy_descent
    (k lam a c y u alpha old z : ℝ) (halpha : 0 ≤ alpha)
    (hmin : ∀ w : ℝ,
      proximalEnergy k lam a c y u alpha old z ≤
        proximalEnergy k lam a c y u alpha old w) :
    energy k lam a c z y u ≤ energy k lam a c old y u := by
  have hb := proximal_energy_bound k lam a c y u alpha old z hmin
  have hp : 0 ≤ alpha / 2 * (z - old) ^ 2 :=
    mul_nonneg (div_nonneg halpha (by norm_num)) (sq_nonneg _)
  linarith

/-- Quadratic dissipation potential and its candidate dual. -/
def dissipation (eta v : ℝ) : ℝ := eta * v ^ 2 / 2

def dualDissipation (eta f : ℝ) : ℝ := f ^ 2 / (2 * eta)

/-- The exact Fenchel--Young gap is a square. -/
theorem fenchel_young_gap (eta v f : ℝ) (heta : eta ≠ 0) :
    dissipation eta v + dualDissipation eta f - f * v =
      (eta * v - f) ^ 2 / (2 * eta) := by
  dsimp [dissipation, dualDissipation]
  field_simp [heta]
  ring

/-- A positive viscosity gives a nonnegative Fenchel--Young gap. -/
theorem fenchel_young_inequality (eta v f : ℝ) (heta : 0 < eta) :
    f * v ≤ dissipation eta v + dualDissipation eta f := by
  have hg := fenchel_young_gap eta v f (ne_of_gt heta)
  have hn : 0 ≤ (eta * v - f) ^ 2 / (2 * eta) := by
    exact div_nonneg (sq_nonneg _) (by linarith)
  linarith

/-- The dual value is attained by the viscosity-induced velocity. -/
theorem dualDissipation_attained (eta f : ℝ) (heta : eta ≠ 0) :
    f * (f / eta) - dissipation eta (f / eta) =
      dualDissipation eta f := by
  dsimp [dissipation, dualDissipation]
  field_simp [heta]
  ring


/-! ### A genuinely nonconvex, two-valued viscous rewrite. -/

/-- With old=0 and alpha=3/4, the original double-well potential has
exactly two distinct choices of globally minimizing next state. -/
theorem concrete_double_well_square (z : ℝ) :
    proximalEnergy (-1) 1 (1 / 2) 0 1 0 (3 / 4) 0 z =
      (z ^ 2 - 1 / 4) ^ 2 / 4 + 15 / 64 := by
  unfold proximalEnergy energy
  ring

/-- Both ±1/2 are optimal.  Hence viscosity alone does NOT select a
single branch in a nonconvex model. -/
theorem double_well_two_proximal_branches :
    (∀ z : ℝ,
      proximalEnergy (-1) 1 (1 / 2) 0 1 0 (3 / 4) 0 (1 / 2) ≤
        proximalEnergy (-1) 1 (1 / 2) 0 1 0 (3 / 4) 0 z) ∧
    (∀ z : ℝ,
      proximalEnergy (-1) 1 (1 / 2) 0 1 0 (3 / 4) 0 (-1 / 2) ≤
        proximalEnergy (-1) 1 (1 / 2) 0 1 0 (3 / 4) 0 z) ∧
    (1 / 2 : ℝ) ≠ -1 / 2 := by
  have hbound (z : ℝ) :
      (15 / 64 : ℝ) ≤
        proximalEnergy (-1) 1 (1 / 2) 0 1 0 (3 / 4) 0 z := by
    rw [concrete_double_well_square]
    nlinarith [sq_nonneg (z ^ 2 - 1 / 4)]
  have hpos :
      proximalEnergy (-1) 1 (1 / 2) 0 1 0 (3 / 4) 0 (1 / 2) =
        (15 / 64 : ℝ) := by
    rw [concrete_double_well_square]
    norm_num
  have hneg :
      proximalEnergy (-1) 1 (1 / 2) 0 1 0 (3 / 4) 0 (-1 / 2) =
        (15 / 64 : ℝ) := by
    rw [concrete_double_well_square]
    norm_num
  constructor
  · intro z
    rw [hpos]
    exact hbound z
  constructor
  · intro z
    rw [hneg]
    exact hbound z
  · norm_num


/-! ### A constrained bridge to the actual F16 two-by-two blocks. -/

/-- Add a non-dissipative rotational part taken from a genuine F16
normalized block; eta is the symmetric viscous coefficient. -/
def f16RotationResistance (eta beta : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  (eta * v.1 + beta * (LinearInputF16UnexpectedBridges.signedAction 1 v).1,
   eta * v.2 + beta * (LinearInputF16UnexpectedBridges.signedAction 1 v).2)

/-- F16's quarter-turn block contributes zero to the velocity pairing;
all dissipation here comes from the chosen positive scalar eta. -/
theorem f16_rotation_resistance_work (eta beta : ℝ) (v : ℝ × ℝ) :
    v.1 * (f16RotationResistance eta beta v).1 +
      v.2 * (f16RotationResistance eta beta v).2 =
        eta * (v.1 ^ 2 + v.2 ^ 2) := by
  rcases v with ⟨x, y⟩
  simp [f16RotationResistance, LinearInputF16UnexpectedBridges.quarter_sample]
  ring

theorem f16_rotation_resistance_dissipative
    (eta beta : ℝ) (heta : 0 ≤ eta) (v : ℝ × ℝ) :
    0 ≤ v.1 * (f16RotationResistance eta beta v).1 +
      v.2 * (f16RotationResistance eta beta v).2 := by
  rw [f16_rotation_resistance_work]
  exact mul_nonneg heta (add_nonneg (sq_nonneg _) (sq_nonneg _))

/-- The distinct actual F16 reflection block has an indefinite pairing:
positive on (1,1) and negative on (1,-1).  It cannot itself be a
nonnegative viscosity operator on all velocities. -/
theorem f16_reflection_indefinite :
    ((1 : ℝ) * (LinearInputF16UnexpectedBridges.signedAction 5 (1, 1)).1 +
      (1 : ℝ) * (LinearInputF16UnexpectedBridges.signedAction 5 (1, 1)).2 = 2) ∧
    ((1 : ℝ) * (LinearInputF16UnexpectedBridges.signedAction 5 (1, -1)).1 +
      (-1 : ℝ) * (LinearInputF16UnexpectedBridges.signedAction 5 (1, -1)).2 = -2) := by
  constructor <;> norm_num [LinearInputF16UnexpectedBridges.reflection_sample]

end LinearInputViscousRewrite