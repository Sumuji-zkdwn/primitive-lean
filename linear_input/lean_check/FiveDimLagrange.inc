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

/-!
# A contact-geometric continuation of the verified five-coordinate multiplier bridge

The same 2+2+1 tuple has TWO non-equivalent roles:
 * constraint lift: (energy, residual), (x,y), multiplier q;
 * first jet: (momentum_x, momentum_y), (x,y), action value.
The second is a 1-jet contact model, not an identification of the two roles.
No physical spacetime dimension or Lie-algebra isomorphism is inferred.
-/

def jetLift (lam r u a x y q : ℝ) : FiveState :=
  ((gx lam r u x y - q, gy x y + q),
    ((x, y), E lam r u x y - q * (x - y - a)))

/-- The original kernel multiplier is precisely zero momentum of the jet lift. -/
theorem tangent_stationarity_iff_zero_jet_momentum (lam r u a x y : ℝ) :
    (∀ v : ℝ × ℝ, constraintVariation v = 0 →
      energyVariation lam r u x y v = 0) ↔
      ∃ q : ℝ, (jetLift lam r u a x y q).1 = (0, 0) := by
  rw [tangent_stationarity_iff_multiplier]
  constructor
  · rintro ⟨q, hx, hy⟩
    refine ⟨q, ?_⟩
    change (gx lam r u x y - q, gy x y + q) = (0, 0)
    apply Prod.ext <;> dsimp <;> linarith
  · rintro ⟨q, hq⟩
    have hx := congrArg Prod.fst hq
    have hy := congrArg Prod.snd hq
    change gx lam r u x y - q = 0 at hx
    change gy x y + q = 0 at hy
    exact ⟨q, by linarith, by linarith⟩

/-- A genuine directional derivative of the old primitive energy plus rewrite term. -/
theorem hasDerivAt_rewrite_line
    (lam r u a x y q dx dy dq : ℝ) :
    HasDerivAt
      (fun t : ℝ =>
        E lam r u (x + t * dx) (y + t * dy) -
          (q + t * dq) * ((x + t * dx) - (y + t * dy) - a))
      ((gx lam r u x y - q) * dx + (gy x y + q) * dy -
        (x - y - a) * dq) 0 := by
  have hx : HasDerivAt (fun t : ℝ => x + t * dx) dx 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).mul_const dx).const_add x)
  have hy : HasDerivAt (fun t : ℝ => y + t * dy) dy 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).mul_const dy).const_add y)
  have hq : HasDerivAt (fun t : ℝ => q + t * dq) dq 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).mul_const dq).const_add q)
  have hu : HasDerivAt (fun _ : ℝ => u) 0 0 := hasDerivAt_const 0 u
  have he := LinearInputGradient.hasDerivAt_energy_curve lam r hx hy hu
  have hg : HasDerivAt
      (fun t : ℝ => (x + t * dx) - (y + t * dy) - a)
      (dx - dy) 0 := (hx.sub hy).sub_const a
  have htotal := he.sub (hq.mul hg)
  convert htotal using 1; simp only [zero_mul, add_zero, mul_zero, sub_zero]; ring

/-- Contact form alpha = dz - p_1 dx - p_2 dy on the 5D first jet. -/
def contactForm (jet tangent : FiveState) : ℝ :=
  tangent.2.2 - jet.1.1 * tangent.2.1.1 - jet.1.2 * tangent.2.1.2

/-- Tangent direction: only the value derivative is needed for the contact form.
The momentum-coordinate derivatives are irrelevant to alpha's evaluation. -/
def rewriteDirection
    (lam r u a x y q dx dy dq : ℝ) : FiveState :=
  ((0, 0), ((dx, dy),
    (gx lam r u x y - q) * dx + (gy x y + q) * dy -
      (x - y - a) * dq))

/-- The contact defect in the full (x,y,q) family is exactly -g(x,y)*dq. -/
theorem contact_defect
    (lam r u a x y q dx dy dq : ℝ) :
    contactForm (jetLift lam r u a x y q)
      (rewriteDirection lam r u a x y q dx dy dq) =
        -(x - y - a) * dq := by
  dsimp [contactForm, jetLift, rewriteDirection]
  ring

/-- Thus the entire feasible tangent family is contact-horizontal. -/
theorem contact_vanishes_on_constraint
    (lam r u a x y q dx dy dq : ℝ) (h : x - y = a) :
    contactForm (jetLift lam r u a x y q)
      (rewriteDirection lam r u a x y q dx dy dq) = 0 := by
  rw [contact_defect]
  have hg : x - y - a = 0 := by linarith
  rw [hg]
  ring

/-- The original rewrite direction transports the confirmed pair by s*u. -/
def originalRewriteShift (s : ℝ) (z : FiveState) : FiveState :=
  ((z.1.1 + s * z.2.1.1, z.1.2 + s * z.2.1.2),
    (z.2.1, z.2.2 + s))

def undecidedShift (v : ℝ × ℝ) (z : FiveState) : FiveState :=
  (z.1, ((z.2.1.1 + v.1, z.2.1.2 + v.2), z.2.2))

def confirmedShift (w : ℝ × ℝ) (z : FiveState) : FiveState :=
  ((z.1.1 + w.1, z.1.2 + w.2), z.2)

/-- Old convention: [rewrite, undecided] has a confirmed two-vector residue. -/
theorem original_bracket (s : ℝ) (v : ℝ × ℝ) (z : FiveState) :
    originalRewriteShift s (undecidedShift v z) =
      confirmedShift (s * v.1, s * v.2)
        (undecidedShift v (originalRewriteShift s z)) := by
  apply Prod.ext
  · apply Prod.ext <;> dsimp [originalRewriteShift, undecidedShift, confirmedShift] <;> ring
  · rfl

/-- Jet convention: a confirmed translation changes the action value by w*u. -/
def jetConfirmedShift (w : ℝ × ℝ) (z : FiveState) : FiveState :=
  ((z.1.1 + w.1, z.1.2 + w.2),
    (z.2.1, z.2.2 + w.1 * z.2.1.1 + w.2 * z.2.1.2))

def jetRewriteShift (s : ℝ) (z : FiveState) : FiveState :=
  (z.1, (z.2.1, z.2.2 + s))

/-- Contact convention: [confirmed, undecided] has a scalar rewrite residue. -/
theorem jet_bracket (v w : ℝ × ℝ) (z : FiveState) :
    jetConfirmedShift w (undecidedShift v z) =
      jetRewriteShift (w.1 * v.1 + w.2 * v.2)
        (undecidedShift v (jetConfirmedShift w z)) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · dsimp [jetConfirmedShift, undecidedShift, jetRewriteShift]
      ring

/-- The two residues are both nontrivial but land in different coordinates. -/
theorem original_bracket_nontrivial :
    originalRewriteShift 1
      (undecidedShift ((1 : ℝ), 0) ((0, 0), ((0, 0), 0))) ≠
    undecidedShift ((1 : ℝ), 0)
      (originalRewriteShift 1 ((0, 0), ((0, 0), 0))) := by
  norm_num [originalRewriteShift, undecidedShift]

theorem jet_bracket_nontrivial :
    jetConfirmedShift ((1 : ℝ), 0)
      (undecidedShift ((1 : ℝ), 0) ((0, 0), ((0, 0), 0))) ≠
    undecidedShift ((1 : ℝ), 0)
      (jetConfirmedShift ((1 : ℝ), 0) ((0, 0), ((0, 0), 0))) := by
  norm_num [jetConfirmedShift, undecidedShift]

/-!
# The old 3+2 and jet 4+1 horizontal distributions are jet geometries.

Old model: J^1(R, R^2), with confirmed function values c_i,
undecided first derivatives u_i, and scalar independent rewrite coordinate r.
The two Cartan forms are dc_i - u_i dr.

New model: J^1(R^2, R), with slope pair p_i and scalar function value z.
Its single contact form is dz - p_i du_i.
-/

def oldCartan (z tangent : FiveState) : ℝ × ℝ :=
  (tangent.1.1 - z.2.1.1 * tangent.2.2,
   tangent.1.2 - z.2.1.2 * tangent.2.2)

/-- The total rewrite derivative in J^1(R,R^2). -/
def rewriteTangent (z : FiveState) : FiveState :=
  (z.2.1, ((0, 0), 1))

/-- Vertical movement of the two undecided jet-derivative coordinates. -/
def undecidedTangent (v : ℝ × ℝ) : FiveState :=
  ((0, 0), (v, 0))

/-- The canonical rewrite direction is horizontal for both Cartan forms. -/
theorem old_cartan_rewrite_zero (z : FiveState) :
    oldCartan z (rewriteTangent z) = (0, 0) := by
  apply Prod.ext <;> dsimp [oldCartan, rewriteTangent] <;> ring

/-- Undecided derivative-coordinate changes are likewise horizontal. -/
theorem old_cartan_undecided_zero (z : FiveState) (v : ℝ × ℝ) :
    oldCartan z (undecidedTangent v) = (0, 0) := by
  apply Prod.ext <;> dsimp [oldCartan, undecidedTangent] <;> ring

/-- Pure slope-coordinate motion lies in the jet contact distribution.
This horizontal vector is different from a finite contactomorphism generator. -/
def confirmedTangent (w : ℝ × ℝ) : FiveState :=
  (w, ((0, 0), 0))

/-- Base-coordinate motion with the compensating scalar derivative p*du. -/
def jetUndecidedTangent (z : FiveState) (v : ℝ × ℝ) : FiveState :=
  ((0, 0), (v, z.1.1 * v.1 + z.1.2 * v.2))

/-- Both standard jet-horizontal families annihilate the contact form. -/
theorem jet_contact_confirmed_zero (z : FiveState) (w : ℝ × ℝ) :
    contactForm z (confirmedTangent w) = 0 := by
  dsimp [contactForm, confirmedTangent]
  ring

theorem jet_contact_undecided_zero (z : FiveState) (v : ℝ × ℝ) :
    contactForm z (jetUndecidedTangent z v) = 0 := by
  dsimp [contactForm, jetUndecidedTangent]
  ring

/-!
# Common horizontal plane, hidden rewrite witness, and Cartan bracket certificate

The common distribution of the two jet geometries is obtained by intersecting
both old Cartan forms with the new contact form on the same fixed 5D tuple.
The F0 transition is a separately chosen, exactly specified primitive-energy
re-evaluation: no unrestricted dynamics or physical interpretation is assumed.

The three candidate bracket columns below were obtained by symbolic real Lie
brackets of the two common-horizontal polynomial fields.  This supplement
certifies the bracket MINOR algebraically; identifying those columns as actual
Lie brackets still requires a separate verified derivative calculation.
-/

def commonDirection (z : FiveState) (v : ℝ × ℝ) : FiveState :=
  let dr : ℝ := z.1.1 * v.1 + z.1.2 * v.2
  ((z.2.1.1 * dr, z.2.1.2 * dr), (v, dr))

/-- Every common direction annihilates both old Cartan forms and the jet contact form. -/
theorem common_horizontal (z : FiveState) (v : ℝ × ℝ) :
    oldCartan z (commonDirection z v) = (0, 0) ∧
      contactForm z (commonDirection z v) = 0 := by
  constructor
  · apply Prod.ext <;> dsimp [oldCartan, commonDirection] <;> ring
  · dsimp [contactForm, commonDirection]
    ring

/-- No further common direction exists: the intersection is parameterized by v ∈ R². -/
theorem common_horizontal_unique (z w : FiveState)
    (hω : oldCartan z w = (0, 0)) (hα : contactForm z w = 0) :
    w = commonDirection z w.2.1 := by
  rcases z with ⟨⟨c1, c2⟩, ⟨⟨u1, u2⟩, r⟩⟩
  rcases w with ⟨⟨a1, a2⟩, ⟨⟨v1, v2⟩, t⟩⟩
  have h1 : a1 - u1 * t = 0 := by
    have h := congrArg Prod.fst hω
    simpa [oldCartan] using h
  have h2 : a2 - u2 * t = 0 := by
    have h := congrArg Prod.snd hω
    simpa [oldCartan] using h
  have ht : t = c1 * v1 + c2 * v2 := by
    dsimp [contactForm] at hα
    linarith
  have ha1 : a1 = u1 * t := by linarith
  have ha2 : a2 = u2 * t := by linarith
  apply Prod.ext
  · apply Prod.ext
    · change a1 = u1 * (c1 * v1 + c2 * v2)
      rw [ha1, ht]
    · change a2 = u2 * (c1 * v1 + c2 * v2)
      rw [ha2, ht]
  · apply Prod.ext
    · rfl
    · change t = c1 * v1 + c2 * v2
      exact ht

/-- Exact characterization of the common horizontal distribution. -/
theorem common_horizontal_iff (z w : FiveState) :
    (oldCartan z w = (0, 0) ∧ contactForm z w = 0) ↔
      ∃ v : ℝ × ℝ, w = commonDirection z v := by
  constructor
  · rintro ⟨hω, hα⟩
    exact ⟨w.2.1, common_horizontal_unique z w hω hα⟩
  · rintro ⟨v, rfl⟩
    exact common_horizontal z v

/-- The undecided increments are a faithful parameterization of common directions. -/
theorem common_direction_injective (z : FiveState) :
    Function.Injective (commonDirection z) := by
  intro v w h
  have hv := congrArg (fun a : FiveState => a.2.1) h
  simpa only [commonDirection] using hv

/-- A canonical F0 retraction records the rewritten value and erases q. -/
def forgetRewriteObservation (z : FiveState) : FiveState :=
  ((rewriteValue z, z.1.2), (z.2.1, 0))

theorem forgetRewriteObservation_idempotent :
    LinearInputF0.Idempotent forgetRewriteObservation := by
  intro z
  simp [forgetRewriteObservation, rewriteValue]

/-- All multiplier choices are currently indistinguishable on the constraint. -/
theorem forget_multiplier_on_constraint
    (lam r u a x y q q' : ℝ) (h : x - y = a) :
    forgetRewriteObservation (lift lam r u a x y q) =
      forgetRewriteObservation (lift lam r u a x y q') := by
  have hg : x - y - a = 0 := by linarith
  simp [forgetRewriteObservation, rewriteValue, lift, hg]

/-- A chosen update re-evaluates the genuine primitive energy after shifting x. -/
def primitiveShiftX (lam r u a δ : ℝ) (z : FiveState) : FiveState :=
  lift lam r u a (z.2.1.1 + δ) z.2.1.2 z.2.2

/-- The hidden difference in q reappears after moving transversely to the constraint. -/
theorem latent_multiplier_difference
    (lam r u a x y δ q q' : ℝ) (h : x - y = a) :
    rewriteValue (primitiveShiftX lam r u a δ (lift lam r u a x y q)) -
      rewriteValue (primitiveShiftX lam r u a δ (lift lam r u a x y q')) =
        -δ * (q - q') := by
  change (E lam r u (x + δ) y - q * (x + δ - y - a)) -
    (E lam r u (x + δ) y - q' * (x + δ - y - a)) = -δ * (q - q')
  have hg : x + δ - y - a = δ := by linarith
  rw [hg]
  ring

/-- F0 forgets a distinction that one primitive transverse update reveals. -/
theorem rewrite_probe_breaks_fibers (lam r u : ℝ) :
    ¬ LinearInputF0Descent.RespectsFibers forgetRewriteObservation
      (primitiveShiftX lam r u 0 1) := by
  intro hf
  have heq := forget_multiplier_on_constraint lam r u 0 0 0 0 1 (by norm_num)
  have hout := hf (lift lam r u 0 0 0 0) (lift lam r u 0 0 0 1) heq
  have hs :
      rewriteValue (primitiveShiftX lam r u 0 1 (lift lam r u 0 0 0 0)) =
      rewriteValue (primitiveShiftX lam r u 0 1 (lift lam r u 0 0 0 1)) := by
    have h' := congrArg (fun z : FiveState => z.1.1) hout
    exact h'
  have hdiff := latent_multiplier_difference lam r u 0 0 0 1 0 1 (by norm_num)
  norm_num at hdiff
  linarith

/-- Hence no deterministic update exists on this particular forgotten F0 state. -/
theorem rewrite_probe_not_descend (lam r u : ℝ) :
    ¬ LinearInputF0Descent.Descends forgetRewriteObservation
      (primitiveShiftX lam r u 0 1) := by
  intro h
  exact rewrite_probe_breaks_fibers lam r u
    ((LinearInputF0Descent.descends_iff_respects
      forgetRewriteObservation_idempotent).mp h)

/-- The future-observation quotient sees more than this instantaneous F0 map. -/
theorem rewrite_probe_future_distinguishes (lam r u : ℝ) :
    forgetRewriteObservation (lift lam r u 0 0 0 0) =
        forgetRewriteObservation (lift lam r u 0 0 0 1) ∧
      ¬ LinearInputFutureObservation.FutureEq forgetRewriteObservation
        (primitiveShiftX lam r u 0 1)
        (lift lam r u 0 0 0 0) (lift lam r u 0 0 0 1) := by
  constructor
  · exact forget_multiplier_on_constraint lam r u 0 0 0 0 1 (by norm_num)
  · intro hfuture
    have hout := hfuture 1
    have hs :
        rewriteValue (primitiveShiftX lam r u 0 1 (lift lam r u 0 0 0 0)) =
        rewriteValue (primitiveShiftX lam r u 0 1 (lift lam r u 0 0 0 1)) := by
      have h' := congrArg (fun z : FiveState => z.1.1)
        (by simpa only [Function.iterate_one] using hout)
      exact h'
    have hdiff := latent_multiplier_difference lam r u 0 0 0 1 0 1 (by norm_num)
    norm_num at hdiff
    linarith

/-- First Lie-bracket candidate in the order (c1,c2,r), from exact polynomial differentiation. -/
def cartanY (c1 c2 u1 u2 : ℝ) : ℝ × ℝ × ℝ :=
  (c1 * u1 * u2 - c2 * u1 ^ 2 + c2,
   c1 * u2 ^ 2 - c1 - c2 * u1 * u2,
   c1 * u2 - c2 * u1)

/-- Second-bracket candidate [X1,Y]. -/
def cartanZ1 (c1 c2 u1 u2 : ℝ) : ℝ × ℝ × ℝ :=
  (-c1 * u1 ^ 2 * u2 + 2*c1*u2 + c2*u1 ^ 3 - 3*c2*u1,
   -c1*u1*u2 ^ 2 - c1*u1 + c2*u1 ^ 2*u2 - 2*c2*u2,
   -c1*u1*u2 + c2*u1 ^ 2 - 2*c2)

/-- Second-bracket candidate [X2,Y]. -/
def cartanZ2 (c1 c2 u1 u2 : ℝ) : ℝ × ℝ × ℝ :=
  (-c1*u1*u2 ^ 2 + 2*c1*u1 + c2*u1 ^ 2*u2 + c2*u2,
   -c1*u2 ^ 3 + 3*c1*u2 + c2*u1*u2 ^ 2 - 2*c2*u1,
   -c1*u2 ^ 2 + 2*c1 + c2*u1*u2)

/-- A 3x3 minor, after eliminating the two identity columns of X1,X2. -/
def cartanMinor (a b c : ℝ × ℝ × ℝ) : ℝ :=
  a.1 * (b.2.1 * c.2.2 - b.2.2 * c.2.1) -
    b.1 * (a.2.1 * c.2.2 - a.2.2 * c.2.1) +
    c.1 * (a.2.1 * b.2.2 - a.2.2 * b.2.1)

/-- Exact factorization of the derived-bracket candidate minor. -/
theorem cartan_minor_factor (c1 c2 u1 u2 : ℝ) :
    cartanMinor (cartanY c1 c2 u1 u2)
      (cartanZ1 c1 c2 u1 u2) (cartanZ2 c1 c2 u1 u2) =
      4 * (c1 ^ 2 + c2 ^ 2) * (c1 * u2 - c2 * u1) := by
  dsimp [cartanMinor, cartanY, cartanZ1, cartanZ2]
  ring

/-- The candidate minor is nonzero away from the zero-confirmed and parallel strata. -/
theorem cartan_minor_nonzero {c1 c2 u1 u2 : ℝ}
    (hc : c1 ≠ 0 ∨ c2 ≠ 0) (hw : c1 * u2 - c2 * u1 ≠ 0) :
    cartanMinor (cartanY c1 c2 u1 u2)
      (cartanZ1 c1 c2 u1 u2) (cartanZ2 c1 c2 u1 u2) ≠ 0 := by
  rw [cartan_minor_factor]
  have hpos : 0 < c1 ^ 2 + c2 ^ 2 := by
    rcases hc with h1 | h2
    · have hs := sq_pos_of_ne_zero h1
      have ht := sq_nonneg c2
      linarith
    · have hs := sq_pos_of_ne_zero h2
      have ht := sq_nonneg c1
      linarith
  exact mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt hpos)) hw

/-- Exact nondegenerate numeric sample. -/
theorem cartan_minor_sample :
    cartanMinor (cartanY 1 0 0 1)
      (cartanZ1 1 0 0 1) (cartanZ2 1 0 0 1) = 4 := by
  rw [cartan_minor_factor]
  norm_num


/-!
# Genuine polynomial Lie derivatives in the common five-dimensional distribution

All coordinates below are real.  We use a free expression syntax for finite
multivariate polynomials in (c1,c2,u1,u2,r).  The first theorem derives the
directional-derivative evaluation from the actual HasDerivAt rules, so later
bracket formulas are not postulates about a formal substitution operator.
-/

inductive FivePoly where
  | const (a : ℝ)
  | c1 | c2 | u1 | u2 | rewrite
  | add (p q : FivePoly)
  | mul (p q : FivePoly)
  | neg (p : FivePoly)

instance : Add FivePoly := ⟨FivePoly.add⟩
instance : Mul FivePoly := ⟨FivePoly.mul⟩
instance : Neg FivePoly := ⟨FivePoly.neg⟩
instance : Sub FivePoly := ⟨fun p q => FivePoly.add p (FivePoly.neg q)⟩

def fiveLine (z v : FiveState) (t : ℝ) : FiveState :=
  ((z.1.1 + t * v.1.1, z.1.2 + t * v.1.2),
    ((z.2.1.1 + t * v.2.1.1, z.2.1.2 + t * v.2.1.2),
      z.2.2 + t * v.2.2))

theorem fiveLine_zero (z v : FiveState) : fiveLine z v 0 = z := by
  simp [fiveLine]

def fivePolyEval : FivePoly → FiveState → ℝ
  | .const a, _ => a
  | .c1, z => z.1.1
  | .c2, z => z.1.2
  | .u1, z => z.2.1.1
  | .u2, z => z.2.1.2
  | .rewrite, z => z.2.2
  | .add p q, z => fivePolyEval p z + fivePolyEval q z
  | .mul p q, z => fivePolyEval p z * fivePolyEval q z
  | .neg p, z => -fivePolyEval p z

def fivePolyDir : FivePoly → FiveState → FiveState → ℝ
  | .const _, _, _ => 0
  | .c1, _, v => v.1.1
  | .c2, _, v => v.1.2
  | .u1, _, v => v.2.1.1
  | .u2, _, v => v.2.1.2
  | .rewrite, _, v => v.2.2
  | .add p q, z, v => fivePolyDir p z v + fivePolyDir q z v
  | .mul p q, z, v =>
      fivePolyDir p z v * fivePolyEval q z +
        fivePolyEval p z * fivePolyDir q z v
  | .neg p, z, v => -fivePolyDir p z v

/-- The syntactic polynomial's directional differential IS the real derivative. -/
theorem fivePolyDir_hasDerivAt (p : FivePoly) (z v : FiveState) :
    HasDerivAt (fun t : ℝ => fivePolyEval p (fiveLine z v t))
      (fivePolyDir p z v) 0 := by
  induction p with
  | const a =>
      simpa [fivePolyEval, fivePolyDir] using (hasDerivAt_const (0 : ℝ) a)
  | c1 =>
      simpa [fivePolyEval, fivePolyDir, fiveLine] using
        (((hasDerivAt_id (0 : ℝ)).mul_const v.1.1).const_add z.1.1)
  | c2 =>
      simpa [fivePolyEval, fivePolyDir, fiveLine] using
        (((hasDerivAt_id (0 : ℝ)).mul_const v.1.2).const_add z.1.2)
  | u1 =>
      simpa [fivePolyEval, fivePolyDir, fiveLine] using
        (((hasDerivAt_id (0 : ℝ)).mul_const v.2.1.1).const_add z.2.1.1)
  | u2 =>
      simpa [fivePolyEval, fivePolyDir, fiveLine] using
        (((hasDerivAt_id (0 : ℝ)).mul_const v.2.1.2).const_add z.2.1.2)
  | rewrite =>
      simpa [fivePolyEval, fivePolyDir, fiveLine] using
        (((hasDerivAt_id (0 : ℝ)).mul_const v.2.2).const_add z.2.2)
  | add p q hp hq =>
      simpa [fivePolyEval, fivePolyDir] using hp.add hq
  | mul p q hp hq =>
      simpa [fivePolyEval, fivePolyDir, fiveLine_zero] using hp.mul hq
  | neg p hp =>
      simpa [fivePolyEval, fivePolyDir] using hp.neg

structure FivePolyField where
  fc1 : FivePoly
  fc2 : FivePoly
  fu1 : FivePoly
  fu2 : FivePoly
  fr : FivePoly

def fivePolyFieldEval (F : FivePolyField) (z : FiveState) : FiveState :=
  ((fivePolyEval F.fc1 z, fivePolyEval F.fc2 z),
    ((fivePolyEval F.fu1 z, fivePolyEval F.fu2 z), fivePolyEval F.fr z))

def fivePolyFieldDir (F : FivePolyField) (z v : FiveState) : FiveState :=
  ((fivePolyDir F.fc1 z v, fivePolyDir F.fc2 z v),
    ((fivePolyDir F.fu1 z v, fivePolyDir F.fu2 z v), fivePolyDir F.fr z v))

/-- Genuine directional derivative in all five coordinates, along a real affine line. -/
def actualDirectional (F : FiveState → FiveState) (z v : FiveState) : FiveState :=
  ((deriv (fun t : ℝ => (F (fiveLine z v t)).1.1) 0,
    deriv (fun t : ℝ => (F (fiveLine z v t)).1.2) 0),
    ((deriv (fun t : ℝ => (F (fiveLine z v t)).2.1.1) 0,
      deriv (fun t : ℝ => (F (fiveLine z v t)).2.1.2) 0),
      deriv (fun t : ℝ => (F (fiveLine z v t)).2.2) 0))

theorem actualDirectional_poly (F : FivePolyField) (z v : FiveState) :
    actualDirectional (fivePolyFieldEval F) z v = fivePolyFieldDir F z v := by
  apply Prod.ext
  · apply Prod.ext
    · exact (fivePolyDir_hasDerivAt F.fc1 z v).deriv
    · exact (fivePolyDir_hasDerivAt F.fc2 z v).deriv
  · apply Prod.ext
    · apply Prod.ext
      · exact (fivePolyDir_hasDerivAt F.fu1 z v).deriv
      · exact (fivePolyDir_hasDerivAt F.fu2 z v).deriv
    · exact (fivePolyDir_hasDerivAt F.fr z v).deriv

def fiveStateSub (v w : FiveState) : FiveState :=
  ((v.1.1 - w.1.1, v.1.2 - w.1.2),
    ((v.2.1.1 - w.2.1.1, v.2.1.2 - w.2.1.2), v.2.2 - w.2.2))

/-- Actual Lie bracket, not an algebraically assigned exchange rule. -/
def actualLieBracket (F G : FiveState → FiveState) (z : FiveState) : FiveState :=
  fiveStateSub (actualDirectional G z (F z)) (actualDirectional F z (G z))

def polyLieBracketEval (F G : FivePolyField) (z : FiveState) : FiveState :=
  fiveStateSub
    (fivePolyFieldDir G z (fivePolyFieldEval F z))
    (fivePolyFieldDir F z (fivePolyFieldEval G z))

/-- Polynomial bracket evaluation is the genuine bracket of the evaluated fields. -/
theorem actualLieBracket_poly (F G : FivePolyField) (z : FiveState) :
    actualLieBracket (fivePolyFieldEval F) (fivePolyFieldEval G) z =
      polyLieBracketEval F G z := by
  simp only [actualLieBracket, polyLieBracketEval, actualDirectional_poly]

def pc1 : FivePoly := .c1
def pc2 : FivePoly := .c2
def pu1 : FivePoly := .u1
def pu2 : FivePoly := .u2
def p2 : FivePoly := .const 2
def p3 : FivePoly := .const 3

def polyX1 : FivePolyField where
  fc1 := pc1 * pu1
  fc2 := pc1 * pu2
  fu1 := .const 1
  fu2 := .const 0
  fr := pc1

def polyX2 : FivePolyField where
  fc1 := pc2 * pu1
  fc2 := pc2 * pu2
  fu1 := .const 0
  fu2 := .const 1
  fr := pc2

def polyY : FivePolyField where
  fc1 := pc1 * pu1 * pu2 - pc2 * pu1 * pu1 + pc2
  fc2 := pc1 * pu2 * pu2 - pc1 - pc2 * pu1 * pu2
  fu1 := .const 0
  fu2 := .const 0
  fr := pc1 * pu2 - pc2 * pu1

def polyZ1 : FivePolyField where
  fc1 := -(pc1 * pu1 * pu1 * pu2) + p2 * pc1 * pu2 +
    pc2 * pu1 * pu1 * pu1 - p3 * pc2 * pu1
  fc2 := -(pc1 * pu1 * pu2 * pu2) - pc1 * pu1 +
    pc2 * pu1 * pu1 * pu2 - p2 * pc2 * pu2
  fu1 := .const 0
  fu2 := .const 0
  fr := -(pc1 * pu1 * pu2) + pc2 * pu1 * pu1 - p2 * pc2

def polyZ2 : FivePolyField where
  fc1 := -(pc1 * pu1 * pu2 * pu2) + p2 * pc1 * pu1 +
    pc2 * pu1 * pu1 * pu2 + pc2 * pu2
  fc2 := -(pc1 * pu2 * pu2 * pu2) + p3 * pc1 * pu2 +
    pc2 * pu1 * pu2 * pu2 - p2 * pc2 * pu1
  fu1 := .const 0
  fu2 := .const 0
  fr := -(pc1 * pu2 * pu2) + p2 * pc1 + pc2 * pu1 * pu2

/-- The polynomial fields are the already-proved two common horizontal directions. -/
theorem polyX1_eq_common (z : FiveState) :
    fivePolyFieldEval polyX1 z = commonDirection z (1, 0) := by
  apply Prod.ext
  · apply Prod.ext <;> dsimp [fivePolyFieldEval, polyX1,
      fivePolyEval, pc1, pu1, pu2, commonDirection] <;> ring
  · apply Prod.ext
    · apply Prod.ext <;> dsimp [fivePolyFieldEval, polyX1,
        fivePolyEval, pc1, pu1, pu2, commonDirection]
    · dsimp [fivePolyFieldEval, polyX1, fivePolyEval, pc1,
        commonDirection]
      ring

theorem polyX2_eq_common (z : FiveState) :
    fivePolyFieldEval polyX2 z = commonDirection z (0, 1) := by
  apply Prod.ext
  · apply Prod.ext <;> dsimp [fivePolyFieldEval, polyX2,
      fivePolyEval, pc2, pu1, pu2, commonDirection] <;> ring
  · apply Prod.ext
    · apply Prod.ext <;> dsimp [fivePolyFieldEval, polyX2,
        fivePolyEval, pc2, pu1, pu2, commonDirection]
    · dsimp [fivePolyFieldEval, polyX2, fivePolyEval, pc2,
        commonDirection]
      ring

/-- The first derived field is the genuine Lie bracket [X1,X2]. -/
theorem actual_bracket_X1_X2 (z : FiveState) :
    actualLieBracket (fivePolyFieldEval polyX1) (fivePolyFieldEval polyX2) z =
      fivePolyFieldEval polyY z := by
  rw [actualLieBracket_poly]
  apply Prod.ext
  · apply Prod.ext <;> dsimp [polyLieBracketEval, fiveStateSub,
      fivePolyFieldDir, fivePolyFieldEval, fivePolyDir, fivePolyEval,
      polyX1, polyX2, polyY, pc1, pc2, pu1, pu2] <;> ring
  · apply Prod.ext
    · apply Prod.ext <;> dsimp [polyLieBracketEval, fiveStateSub,
        fivePolyFieldDir, fivePolyFieldEval, fivePolyDir, fivePolyEval,
        polyX1, polyX2, polyY, pc1, pc2, pu1, pu2] <;> ring
    · dsimp [polyLieBracketEval, fiveStateSub,
        fivePolyFieldDir, fivePolyFieldEval, fivePolyDir, fivePolyEval,
        polyX1, polyX2, polyY, pc1, pc2, pu1, pu2]
      ring

/-- The first fourth-order candidate is the actual iterated bracket [X1,Y]. -/
theorem actual_bracket_X1_Y (z : FiveState) :
    actualLieBracket (fivePolyFieldEval polyX1) (fivePolyFieldEval polyY) z =
      fivePolyFieldEval polyZ1 z := by
  rw [actualLieBracket_poly]
  apply Prod.ext
  · apply Prod.ext <;> dsimp [polyLieBracketEval, fiveStateSub,
      fivePolyFieldDir, fivePolyFieldEval, fivePolyDir, fivePolyEval,
      polyX1, polyY, polyZ1, pc1, pc2, pu1, pu2, p2, p3] <;> ring
  · apply Prod.ext
    · apply Prod.ext <;> dsimp [polyLieBracketEval, fiveStateSub,
        fivePolyFieldDir, fivePolyFieldEval, fivePolyDir, fivePolyEval,
        polyX1, polyY, polyZ1, pc1, pc2, pu1, pu2, p2, p3] <;> ring
    · dsimp [polyLieBracketEval, fiveStateSub,
        fivePolyFieldDir, fivePolyFieldEval, fivePolyDir, fivePolyEval,
        polyX1, polyY, polyZ1, pc1, pc2, pu1, pu2, p2, p3]
      ring

/-- The second fourth-order candidate is the actual iterated bracket [X2,Y]. -/
theorem actual_bracket_X2_Y (z : FiveState) :
    actualLieBracket (fivePolyFieldEval polyX2) (fivePolyFieldEval polyY) z =
      fivePolyFieldEval polyZ2 z := by
  rw [actualLieBracket_poly]
  apply Prod.ext
  · apply Prod.ext <;> dsimp [polyLieBracketEval, fiveStateSub,
      fivePolyFieldDir, fivePolyFieldEval, fivePolyDir, fivePolyEval,
      polyX2, polyY, polyZ2, pc1, pc2, pu1, pu2, p2, p3] <;> ring
  · apply Prod.ext
    · apply Prod.ext <;> dsimp [polyLieBracketEval, fiveStateSub,
        fivePolyFieldDir, fivePolyDir, fivePolyFieldEval, fivePolyEval,
        polyX2, polyY, polyZ2, pc1, pc2, pu1, pu2, p2, p3] <;> ring
    · dsimp [polyLieBracketEval, fiveStateSub,
        fivePolyFieldDir, fivePolyFieldEval, fivePolyDir, fivePolyEval,
        polyX2, polyY, polyZ2, pc1, pc2, pu1, pu2, p2, p3]
      ring



/-!
# From genuine iterated Lie derivatives to the exact Cartan minor
-/ 

def actualBracketProj (w : FiveState) : ℝ × ℝ × ℝ :=
  (w.1.1, w.1.2, w.2.2)

theorem actualBracketProj_Y (z : FiveState) :
    actualBracketProj (fivePolyFieldEval polyY z) =
      cartanY z.1.1 z.1.2 z.2.1.1 z.2.1.2 := by
  apply Prod.ext
  · dsimp [actualBracketProj, fivePolyFieldEval, polyY,
      fivePolyEval, pc1, pc2, pu1, pu2, cartanY]
    ring
  · apply Prod.ext
    · dsimp [actualBracketProj, fivePolyFieldEval,
        polyY, fivePolyEval, pc1, pc2, pu1, pu2, cartanY]
      ring
    · dsimp [actualBracketProj, fivePolyFieldEval,
        polyY, fivePolyEval, pc1, pc2, pu1, pu2, cartanY]
      ring

theorem actualBracketProj_Z1 (z : FiveState) :
    actualBracketProj (fivePolyFieldEval polyZ1 z) =
      cartanZ1 z.1.1 z.1.2 z.2.1.1 z.2.1.2 := by
  apply Prod.ext
  · dsimp [actualBracketProj, fivePolyFieldEval, polyZ1,
      fivePolyEval, pc1, pc2, pu1, pu2, p2, p3, cartanZ1]
    ring
  · apply Prod.ext <;> dsimp [actualBracketProj, fivePolyFieldEval,
      polyZ1, fivePolyEval, pc1, pc2, pu1, pu2, p2, p3, cartanZ1] <;> ring

theorem actualBracketProj_Z2 (z : FiveState) :
    actualBracketProj (fivePolyFieldEval polyZ2 z) =
      cartanZ2 z.1.1 z.1.2 z.2.1.1 z.2.1.2 := by
  apply Prod.ext
  · dsimp [actualBracketProj, fivePolyFieldEval, polyZ2,
      fivePolyEval, pc1, pc2, pu1, pu2, p2, p3, cartanZ2]
    ring
  · apply Prod.ext <;> dsimp [actualBracketProj, fivePolyFieldEval,
      polyZ2, fivePolyEval, pc1, pc2, pu1, pu2, p2, p3, cartanZ2] <;> ring

/-- The known 3x3 factor is now obtained from actual iterated Lie brackets. -/
theorem genuineLieCartanMinorFactor (z : FiveState) :
    cartanMinor
      (actualBracketProj
        (actualLieBracket (fivePolyFieldEval polyX1) (fivePolyFieldEval polyX2) z))
      (actualBracketProj
        (actualLieBracket (fivePolyFieldEval polyX1) (fivePolyFieldEval polyY) z))
      (actualBracketProj
        (actualLieBracket (fivePolyFieldEval polyX2) (fivePolyFieldEval polyY) z)) =
      4 * (z.1.1 ^ 2 + z.1.2 ^ 2) *
        (z.1.1 * z.2.1.2 - z.1.2 * z.2.1.1) := by
  rw [actual_bracket_X1_X2, actual_bracket_X1_Y, actual_bracket_X2_Y,
    actualBracketProj_Y, actualBracketProj_Z1, actualBracketProj_Z2]
  exact cartan_minor_factor z.1.1 z.1.2 z.2.1.1 z.2.1.2

theorem genuineLieCartanMinorNonzero (z : FiveState)
    (hc : z.1.1 ≠ 0 ∨ z.1.2 ≠ 0)
    (hw : z.1.1 * z.2.1.2 - z.1.2 * z.2.1.1 ≠ 0) :
    cartanMinor
      (actualBracketProj
        (actualLieBracket (fivePolyFieldEval polyX1) (fivePolyFieldEval polyX2) z))
      (actualBracketProj
        (actualLieBracket (fivePolyFieldEval polyX1) (fivePolyFieldEval polyY) z))
      (actualBracketProj
        (actualLieBracket (fivePolyFieldEval polyX2) (fivePolyFieldEval polyY) z)) ≠ 0 := by
  rw [genuineLieCartanMinorFactor]
  have hpos : 0 < z.1.1 ^ 2 + z.1.2 ^ 2 := by
    rcases hc with h1 | h2
    · nlinarith [sq_pos_of_ne_zero h1, sq_nonneg z.1.2]
    · nlinarith [sq_pos_of_ne_zero h2, sq_nonneg z.1.1]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt hpos)) hw

/-!
The determinant H=c1*u2-c2*u1 and the rewrite coordinate are an inner/outer
product pair along the common horizontal directions.  These are real
identities; no imaginary-time or quantum postulate is made.
-/

def holonomyPoly : FivePoly := pc1 * pu2 - pc2 * pu1

theorem holonomy_rewrite_zero (z : FiveState) :
    fivePolyDir holonomyPoly z (rewriteTangent z) = 0 := by
  dsimp [holonomyPoly, fivePolyDir, fivePolyEval,
    pc1, pc2, pu1, pu2, rewriteTangent]
  ring

theorem holonomy_common_derivative (z : FiveState) (v : ℝ × ℝ) :
    fivePolyDir holonomyPoly z (commonDirection z v) =
      z.1.1 * v.2 - z.1.2 * v.1 := by
  dsimp [holonomyPoly, fivePolyDir, fivePolyEval,
    pc1, pc2, pu1, pu2, commonDirection]
  ring

/-- A real differentiability theorem, not just formal differentiation. -/
theorem holonomy_real_derivative (z : FiveState) (v : ℝ × ℝ) :
    deriv (fun t : ℝ =>
      fivePolyEval holonomyPoly (fiveLine z (commonDirection z v) t)) 0 =
      z.1.1 * v.2 - z.1.2 * v.1 := by
  rw [(fivePolyDir_hasDerivAt holonomyPoly z (commonDirection z v)).deriv]
  exact holonomy_common_derivative z v

/-- The real/imaginary components of the Hermitian pairing conj(c)*du. -/
theorem rewrite_holonomy_pair (z : FiveState) (v : ℝ × ℝ) :
    ((commonDirection z v).2.2,
      fivePolyDir holonomyPoly z (commonDirection z v)) =
      (z.1.1 * v.1 + z.1.2 * v.2,
        z.1.1 * v.2 - z.1.2 * v.1) := by
  apply Prod.ext
  · dsimp [commonDirection]
  · exact holonomy_common_derivative z v



/-!
# The actual five-field 5×5 matrix and its full rank certificate

Rows are ordered (u₁,u₂,c₁,c₂,r), columns are
(X₁, X₂, [X₁,X₂], [X₁,[X₁,X₂]], [X₂,[X₁,X₂]]).
The first two rows form an identity block and the last three entries of the
last three columns are the ALREADY verified actual Lie-bracket projections.
The block determinant theorem is mathlib's actual Matrix.det, not a custom
determinant of symbolic polynomials.
-/

/-- An arbitrary three-column matrix with columns a,b,c in the (c₁,c₂,r) basis. -/
def threeColumnMatrix (a b c : ℝ × ℝ × ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j =>
    let v := if j = 0 then a else if j = 1 then b else c
    if i = 0 then v.1 else if i = 1 then v.2.1 else v.2.2

theorem threeColumnMatrix_det (a b c : ℝ × ℝ × ℝ) :
    (threeColumnMatrix a b c).det = cartanMinor a b c := by
  rw [Matrix.det_fin_three]
  change
    a.1 * b.2.1 * c.2.2 - a.1 * c.2.1 * b.2.2 -
      b.1 * a.2.1 * c.2.2 + b.1 * c.2.1 * a.2.2 +
      c.1 * a.2.1 * b.2.2 - c.1 * b.2.1 * a.2.2 =
      cartanMinor a b c
  dsimp [cartanMinor]
  ring

def cartanActualTripleMatrix (z : FiveState) : Matrix (Fin 3) (Fin 3) ℝ :=
  threeColumnMatrix
    (actualBracketProj
      (actualLieBracket (fivePolyFieldEval polyX1) (fivePolyFieldEval polyX2) z))
    (actualBracketProj
      (actualLieBracket (fivePolyFieldEval polyX1) (fivePolyFieldEval polyY) z))
    (actualBracketProj
      (actualLieBracket (fivePolyFieldEval polyX2) (fivePolyFieldEval polyY) z))

/-- Actual genuine Lie bracket columns have exactly the certified triple determinant. -/
theorem cartanActualTripleMatrix_det (z : FiveState) :
    (cartanActualTripleMatrix z).det =
      4 * (z.1.1 ^ 2 + z.1.2 ^ 2) *
        (z.1.1 * z.2.1.2 - z.1.2 * z.2.1.1) := by
  unfold cartanActualTripleMatrix
  rw [threeColumnMatrix_det]
  exact genuineLieCartanMinorFactor z

/-- Lower-left block contains the confirmed/rewrite coordinates of X₁,X₂. -/
def cartanLowerLeftBlock (z : FiveState) : Matrix (Fin 3) (Fin 2) ℝ :=
  fun i j =>
    let v := if j = 0 then fivePolyFieldEval polyX1 z
      else fivePolyFieldEval polyX2 z
    if i = 0 then v.1.1 else if i = 1 then v.1.2 else v.2.2

/-- A real 5×5 matrix of actual horizontal fields and their Lie brackets,
with the five row coordinates ordered (u₁,u₂,c₁,c₂,r). -/
def cartanActualFiveMatrix (z : FiveState) :
    Matrix (Fin 2 ⊕ Fin 3) (Fin 2 ⊕ Fin 3) ℝ :=
  Matrix.fromBlocks (1 : Matrix (Fin 2) (Fin 2) ℝ)
    (0 : Matrix (Fin 2) (Fin 3) ℝ)
    (cartanLowerLeftBlock z) (cartanActualTripleMatrix z)

/-- The genuine 5×5 determinant: a 2×2 identity pivot and the 3×3 Lie minor. -/
theorem cartanActualFiveMatrix_det (z : FiveState) :
    (cartanActualFiveMatrix z).det =
      4 * (z.1.1 ^ 2 + z.1.2 ^ 2) *
        (z.1.1 * z.2.1.2 - z.1.2 * z.2.1.1) := by
  unfold cartanActualFiveMatrix
  rw [Matrix.det_fromBlocks_zero₁₂]
  simp only [Matrix.det_one, one_mul]
  exact cartanActualTripleMatrix_det z

/-- Maximum rank of the actual 5×5 Lie-bracket matrix at every generic point. -/
theorem cartanActualFiveMatrix_rank_five (z : FiveState)
    (hc : z.1.1 ≠ 0 ∨ z.1.2 ≠ 0)
    (hw : z.1.1 * z.2.1.2 - z.1.2 * z.2.1.1 ≠ 0) :
    (cartanActualFiveMatrix z).rank = 5 := by
  have hdet : (cartanActualFiveMatrix z).det ≠ 0 := by
    rw [cartanActualFiveMatrix_det]
    have hpos : 0 < z.1.1 ^ 2 + z.1.2 ^ 2 := by
      rcases hc with h1 | h2
      · nlinarith [sq_pos_of_ne_zero h1, sq_nonneg z.1.2]
      · nlinarith [sq_pos_of_ne_zero h2, sq_nonneg z.1.1]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt hpos)) hw
  have hunitdet : IsUnit (cartanActualFiveMatrix z).det :=
    isUnit_iff_ne_zero.mpr hdet
  have hunit : IsUnit (cartanActualFiveMatrix z) :=
    ((cartanActualFiveMatrix z).isUnit_iff_isUnit_det).2 hunitdet
  simpa [Fintype.card_sum] using
    Matrix.rank_of_isUnit (cartanActualFiveMatrix z) hunit

/-- The exact singular locus of this five-column Lie-bracket matrix. -/
theorem cartanActualFiveMatrix_det_zero_iff (z : FiveState) :
    (cartanActualFiveMatrix z).det = 0 ↔
      (z.1.1 = 0 ∧ z.1.2 = 0) ∨
        z.1.1 * z.2.1.2 - z.1.2 * z.2.1.1 = 0 := by
  rw [cartanActualFiveMatrix_det]
  constructor
  · intro h
    rcases (mul_eq_zero.mp h) with hleft | hright
    · rcases (mul_eq_zero.mp hleft) with hfour | hsum
      · norm_num at hfour
      · left
        constructor
        · nlinarith [sq_nonneg z.1.2]
        · nlinarith [sq_nonneg z.1.1]
    · exact Or.inr hright
  · rintro (⟨hc1, hc2⟩ | hw)
    · simp [hc1, hc2]
    · rw [hw]
      ring

/-- An explicit concrete full-rank point of the actual Lie distribution. -/
theorem cartanActualFiveMatrix_example_rank :
    (cartanActualFiveMatrix ((1, 0), ((0, 1), 0))).rank = 5 := by
  apply cartanActualFiveMatrix_rank_five
  · norm_num
  · norm_num


end LinearInputFiveDimLagrange
