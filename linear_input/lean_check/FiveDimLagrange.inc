/-!
# Five-coordinate constrained stationarity derived from primitive-lean

The ambient record has (energy, constraint residual), (x,y), and a scalar
rewriting coefficient q: 2 confirmed + 2 undecided + 1 rewrite.

This is an explicit realization, not a theorem that five-dimensional physical
space or a noncommutative rewrite law follows from constrained calculus.
The energy derivatives are imported from the verified primitive E, and the
multiplier existence is specialized from Elastica's kernel-annihilator theorem.
-/
noncomputable section
namespace LinearInputFiveDimLagrange

open LinearInputDesign LinearInputGradient

abbrev FiveState := (ℝ × ℝ) × ((ℝ × ℝ) × ℝ)

def lift (lam r u a x y q : ℝ) : FiveState :=
  ((E lam r u x y, x - y - a), ((x, y), q))

def rewriteValue (z : FiveState) : ℝ :=
  z.1.1 - z.2.2 * z.1.2

theorem lift_rewriteValue (lam r u a x y q : ℝ) :
    rewriteValue (lift lam r u a x y q) =
      E lam r u x y - q * (x - y - a) := rfl

/-- The actual first variation, not a postulated force. -/
def energyVariation (lam r u x y : ℝ) : (ℝ × ℝ) →ₗ[ℝ] ℝ where
  toFun v := gx lam r u x y * v.1 + gy x y * v.2
  map_add' v w := by
    dsimp
    ring
  map_smul' t v := by
    dsimp
    ring

/-- The differential of the regular constraint x-y-a. -/
def constraintVariation : (ℝ × ℝ) →ₗ[ℝ] ℝ where
  toFun v := v.1 - v.2
  map_add' v w := by
    dsimp
    ring
  map_smul' t v := by
    dsimp
    ring

theorem energyVariation_from_primitive (lam r u x y : ℝ) (v : ℝ × ℝ) :
    energyVariation lam r u x y v =
      deriv (fun t : ℝ => E lam r u t y) x * v.1 +
        deriv (fun t : ℝ => E lam r u x t) y * v.2 := by
  rw [deriv_E_x, deriv_E_y]
  rfl

/-- One multiplier from the existing two-constraint Elastica kernel theorem,
with the second constraint specialized to the zero functional. -/
theorem one_multiplier_of_kernel
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (f c : V →ₗ[ℝ] ℝ)
    (h : ∀ v, c v = 0 → f v = 0) :
    ∃ q : ℝ, ∀ v, f v - q * c v = 0 := by
  obtain ⟨lam, mu, hm⟩ :=
    Elastica.exists_multipliers_of_kernel f c (0 : V →ₗ[ℝ] ℝ)
      (by
        intro v hv _
        exact h v hv)
  refine ⟨-lam, ?_⟩
  intro v
  have hv : f v + lam * c v = 0 := by
    simpa using hm v
  calc
    f v - (-lam) * c v = f v + lam * c v := by ring
    _ = 0 := hv

/-- Tangent stationarity gives a rewrite coefficient, not merely a rank test. -/
theorem tangent_stationarity_iff_multiplier (lam r u x y : ℝ) :
    (∀ v : ℝ × ℝ, constraintVariation v = 0 →
      energyVariation lam r u x y v = 0) ↔
    ∃ q : ℝ, gx lam r u x y = q ∧ gy x y = -q := by
  constructor
  · intro h
    obtain ⟨q, hq⟩ := one_multiplier_of_kernel
      (energyVariation lam r u x y) constraintVariation h
    have hx := hq ((1 : ℝ), 0)
    have hy := hq ((0 : ℝ), 1)
    change gx lam r u x y * 1 + gy x y * 0 - q * (1 - 0) = 0 at hx
    change gx lam r u x y * 0 + gy x y * 1 - q * (0 - 1) = 0 at hy
    refine ⟨q, ?_, ?_⟩ <;> nlinarith
  · rintro ⟨q, hx, hy⟩ v hv
    change v.1 - v.2 = 0 at hv
    have heq : v.1 = v.2 := by linarith
    change gx lam r u x y * v.1 + gy x y * v.2 = 0
    rw [hx, hy, heq]
    ring

/-- The Jacobian of the two confirmed observations has rank < 2 exactly
when their determinant vanishes. The constraint gradient is (1,-1) everywhere. -/
theorem confirmed_jacobian (lam r u x y : ℝ) :
    LinearInputVariablePairs.jacobianPair
      (fun v w => E lam r u v w) (fun v w : ℝ => v - w) x y =
        -(gx lam r u x y + gy x y) := by
  have hx : HasDerivAt (fun t : ℝ => t - y) 1 x :=
    (hasDerivAt_id x).sub_const y
  have hy : HasDerivAt (fun t : ℝ => x - t) (-1) y :=
    (hasDerivAt_id y).const_sub x
  unfold LinearInputVariablePairs.jacobianPair
  rw [deriv_E_x, deriv_E_y, hx.deriv, hy.deriv]
  ring

/-- Singular confirmed-output Jacobian iff a multiplier exists for this
regular one-constraint slice. This equivalence is NOT valid for arbitrary g. -/
theorem multiplier_iff_singular_jacobian (lam r u x y : ℝ) :
    (∃ q : ℝ, gx lam r u x y = q ∧ gy x y = -q) ↔
      LinearInputVariablePairs.jacobianPair
        (fun v w => E lam r u v w) (fun v w : ℝ => v - w) x y = 0 := by
  rw [confirmed_jacobian]
  constructor
  · rintro ⟨q, hx, hy⟩
    rw [hx, hy]
    ring
  · intro h
    refine ⟨gx lam r u x y, rfl, ?_⟩
    linarith

theorem stationary_iff_singular_jacobian (lam r u x y : ℝ) :
    (∀ v : ℝ × ℝ, constraintVariation v = 0 →
      energyVariation lam r u x y v = 0) ↔
      LinearInputVariablePairs.jacobianPair
        (fun v w => E lam r u v w) (fun v w : ℝ => v - w) x y = 0 := by
  exact (tangent_stationarity_iff_multiplier lam r u x y).trans
    (multiplier_iff_singular_jacobian lam r u x y)

/-- A fully explicit constrained stationary-input equation for the old E. -/
theorem constrained_stationary_input (lam r u a x : ℝ) :
    gx lam r u x (x - a) + gy x (x - a) = 0 ↔
      u = lam * x ^ 3 + (r + 3 - 2 * Real.sqrt 2) * x +
        (Real.sqrt 2 - 1) * a := by
  dsimp [gx, gy]
  constructor <;> intro h <;> nlinarith

/-- The multiplier is uniquely fixed by the second energy derivative. -/
theorem constrained_multiplier_value (x a q : ℝ)
    (h : gy x (x - a) = -q) :
    q = (Real.sqrt 2 - 1) * x + a := by
  dsimp [gy] at h
  linarith

/-- A nonzero-multiplier example: x=y=1, lambda=1, r=0,
input u=4-2 sqrt 2, and multiplier sqrt 2-1. -/
theorem nonzero_multiplier_example :
    gx 1 0 (4 - 2 * Real.sqrt 2) 1 1 = Real.sqrt 2 - 1 ∧
      gy 1 1 = -(Real.sqrt 2 - 1) := by
  constructor <;> dsimp [gx, gy] <;> ring

/-- The rewrite coefficient is observationally invisible on the constraint. -/
theorem rewrite_invisible_on_constraint
    (lam r u a x y q : ℝ) (h : x - y = a) :
    rewriteValue (lift lam r u a x y q) = E lam r u x y := by
  rw [lift_rewriteValue]
  have hzero : x - y - a = 0 := by linarith
  rw [hzero]
  ring

end LinearInputFiveDimLagrange
