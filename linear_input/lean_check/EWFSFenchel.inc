/-!
Polynomial E, its reversible two-coordinate update, WFS observation gauges,
and the Legendre--Fenchel change-of-pairing issue.

Original polynomial: E(x,y;u,k,λ,a,c) =
  λ*x^4/4 + k*x^2/2 + a*y^2/2 - c*x*y - u*x.

IMPORTANT DISTINCTIONS
* H_E(x,u)=(∂_x E(x,u),x) is a polynomial automorphism.
* Only observing its first component is NOT a faithful state update.
* WFS is defined on positive intensity, not all real E values.
* Fenchel conjugacy uses a specified dual pairing. Reparameterizing both
  the score and the domain is invariant; changing the pairing is not.
No Jacobian conjecture, global packing result or optimization of all
stationary branches is claimed.
-/

noncomputable section

namespace LinearInputEWFSDual

/-- The orientation-preserving two-coordinate update from the old E family. -/
def H (k lam c y : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (k * z.1 + lam * z.1 ^ 3 - c * y - z.2, z.1)

/-- Explicit polynomial inverse, valid for every real choice of parameters. -/
def HInv (k lam c y : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.2, k * z.2 + lam * z.2 ^ 3 - c * y - z.1)

theorem HInv_H (k lam c y : ℝ) (z : ℝ × ℝ) :
    HInv k lam c y (H k lam c y z) = z := by
  apply Prod.ext
  · rfl
  · dsimp [HInv, H]
    ring

theorem H_HInv (k lam c y : ℝ) (z : ℝ × ℝ) :
    H k lam c y (HInv k lam c y z) = z := by
  apply Prod.ext
  · dsimp [HInv, H]
    ring
  · rfl

/-- This is a sign-corrected form of the already formalized E gradient. -/
theorem H_from_existing_E (k lam a c y : ℝ) (z : ℝ × ℝ) :
    H k lam c y z =
      ((LinearInputVariablePairs.gradXu k lam a c (-1) y z).1,
       -(LinearInputVariablePairs.gradXu k lam a c (-1) y z).2) := by
  rw [LinearInputVariablePairs.gradXu_formula]
  dsimp [H]
  congr 1 <;> ring

def HEquiv (k lam c y : ℝ) : (ℝ × ℝ) ≃ (ℝ × ℝ) where
  toFun := H k lam c y
  invFun := HInv k lam c y
  left_inv := HInv_H k lam c y
  right_inv := H_HInv k lam c y

theorem H_injective (k lam c y : ℝ) :
    Function.Injective (H k lam c y) :=
  (HEquiv k lam c y).injective

theorem H_surjective (k lam c y : ℝ) :
    Function.Surjective (H k lam c y) :=
  (HEquiv k lam c y).surjective

/-- Algebraic determinant of the full Jacobian; the second output x is retained. -/
theorem H_jacobian_algebraic (k lam x : ℝ) :
    (k + 3 * lam * x ^ 2) * 0 - (-1 : ℝ) * 1 = 1 := by
  ring

/-- Observing x alone discards u. -/
def observeX (z : ℝ × ℝ) : ℝ := z.1

theorem same_observation_different_future (k lam c y : ℝ) :
    observeX ((0 : ℝ), 0) = observeX ((0 : ℝ), 1) ∧
      observeX (H k lam c y (0, 0)) ≠
        observeX (H k lam c y (0, 1)) := by
  constructor
  · rfl
  · intro h
    dsimp [observeX, H] at h
    linarith

/-- No deterministic scalar recurrence can reproduce every first coordinate
of H, even though H itself is exactly invertible. -/
theorem no_scalar_update (k lam c y : ℝ) :
    ¬ ∃ T : ℝ → ℝ, ∀ x u : ℝ,
      T x = observeX (H k lam c y (x, u)) := by
  rintro ⟨T, h⟩
  have h0 := h 0 0
  have h1 := h 0 1
  dsimp [observeX, H] at h0 h1
  linarith

/-- The cubic stationary input is an explicit specialization of original E. -/
def cubic (x : ℝ) : ℝ := 4 * x ^ 3 - 3 * x

theorem cubic_eq_E_stationary (x u : ℝ) :
    (H (-3) 4 0 0 (x, u)).1 = cubic x - u := by
  dsimp [H, cubic]
  ring

theorem cubic_has_collision :
    cubic (-1) = cubic (1 / 2) ∧ (-1 : ℝ) ≠ 1 / 2 := by
  norm_num [cubic]

theorem different_stationary_branches_same_input :
    (H (-3) 4 0 0 ((-1 : ℝ), (-1 : ℝ))).1 =
      (H (-3) 4 0 0 ((1 / 2 : ℝ), (-1 : ℝ))).1 ∧
    (H (-3) 4 0 0 ((-1 : ℝ), (-1 : ℝ))).2 ≠
      (H (-3) 4 0 0 ((1 / 2 : ℝ), (-1 : ℝ))).2 := by
  norm_num [H]

/-- The higher-energy stationary branch cannot minimize E globally. -/
theorem higher_stationary_branch_not_global_minimum :
    ¬ ∀ x : ℝ,
      LinearInputVariablePairs.energy (-3) 4 0 0 (1 / 2) 0 (-1) ≤
        LinearInputVariablePairs.energy (-3) 4 0 0 x 0 (-1) := by
  intro h
  have h0 := h (-1)
  norm_num [LinearInputVariablePairs.energy] at h0

/-- WFS power gauge for p=2, valid as a coordinate on r>0. -/
def wfs2 (r : ℝ) : ℝ := (r ^ 2 - 1) / 2

/-- Positive intensities are not collapsed by this WFS gauge. -/
theorem wfs2_inj_pos {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (h : wfs2 r = wfs2 s) : r = s := by
  have hsq : r ^ 2 = s ^ 2 := by
    dsimp [wfs2] at h
    linarith
  have hprod : (r - s) * (r + s) = 0 := by nlinarith
  rcases mul_eq_zero.mp hprod with hzero | hzero
  · linarith
  · linarith

/-- Full future-observation equivalence is unchanged by an injective gauge. -/
theorem gauge_future_iff {α : Type*} (K : α → ℝ) (U : α → α)
    (g : ℝ → ℝ) (hg : Function.Injective g) (x y : α) :
    (∀ t : ℕ, g (K (U^[t] x)) = g (K (U^[t] y))) ↔
      (∀ t : ℕ, K (U^[t] x) = K (U^[t] y)) := by
  constructor
  · intro h t
    exact hg (h t)
  · intro h t
    exact congrArg g (h t)

/-- Invariance for WFS p=2 under the necessary positive-intensity restriction. -/
theorem wfs2_future_iff {α : Type*} (K : α → ℝ) (U : α → α)
    (hK : ∀ x, 0 < K x) (x y : α) :
    (∀ t : ℕ, wfs2 (K (U^[t] x)) = wfs2 (K (U^[t] y))) ↔
      (∀ t : ℕ, K (U^[t] x) = K (U^[t] y)) := by
  constructor
  · intro h t
    exact wfs2_inj_pos (hK _) (hK _) (h t)
  · intro h t
    exact congrArg wfs2 (h t)

/-- Positive scalar intensities, not assumed to be values of E. -/
abbrev Positive := {r : ℝ // 0 < r}

/-- The Fechner (p=0) WFS coordinate is inverse to positive exponentiation. -/
def logGaugeEquiv : ℝ ≃ Positive where
  toFun z := ⟨Real.exp z, Real.exp_pos z⟩
  invFun r := Real.log r.val
  left_inv z := Real.log_exp z
  right_inv r := by
    apply Subtype.ext
    exact Real.exp_log r.property

/-- Supremum is unchanged if we reindex the entire score with an equivalence. -/
theorem supremum_reparam {α β : Type*}
    (f : α → ℝ) (g : β ≃ α) :
    sSup (Set.range (fun z : β => f (g z))) =
      sSup (Set.range f) := by
  have hset : Set.range (fun z : β => f (g z)) = Set.range f := by
    ext v
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨g z, rfl⟩
    · rintro ⟨r, rfl⟩
      exact ⟨g.symm r, by simp⟩
  exact congrArg sSup hset

/-- A concrete Legendre-Fenchel score with the *physical* pairing ur. -/
def physicalScore (u : ℝ) (r : Positive) : ℝ :=
  u * r.val - r.val ^ 2 / 2

def physicalDual (u : ℝ) : ℝ :=
  sSup (Set.range (physicalScore u))

/-- Change the coordinate using Fechner's log but NOT the physical pairing. -/
def physicalLogDual (u : ℝ) : ℝ :=
  sSup (Set.range (fun z : ℝ => physicalScore u (logGaugeEquiv z)))

theorem physicalLogDual_eq_physicalDual (u : ℝ) :
    physicalLogDual u = physicalDual u := by
  exact supremum_reparam (physicalScore u) logGaugeEquiv

/-- A new pairing ξ G_2(r), instead of ur, is mathematically different. -/
def wfs2Score (xi : ℝ) (r : Positive) : ℝ :=
  xi * wfs2 r.val - r.val ^ 2 / 2

theorem physicalScore_one_bound (r : Positive) :
    physicalScore 1 r ≤ (1 / 2 : ℝ) := by
  dsimp [physicalScore]
  nlinarith [sq_nonneg (r.val - 1)]

theorem physicalScore_one_attained :
    physicalScore 1 ⟨1, by norm_num⟩ = (1 / 2 : ℝ) := by
  norm_num [physicalScore]

theorem wfs2Score_one_constant (r : Positive) :
    wfs2Score 1 r = (-1 / 2 : ℝ) := by
  dsimp [wfs2Score, wfs2]
  ring

/-- Different maximization values, even though the WFS coordinate is invertible.
This explicitly contrasts a changed pairing with a mere reparameterization. -/
theorem changed_pairing_has_different_best_score :
    (∃ r : Positive, physicalScore 1 r = (1 / 2 : ℝ)) ∧
    (∀ r : Positive, physicalScore 1 r ≤ (1 / 2 : ℝ)) ∧
    (∀ r : Positive, wfs2Score 1 r = (-1 / 2 : ℝ)) := by
  exact ⟨⟨⟨1, by norm_num⟩, physicalScore_one_attained⟩,
    physicalScore_one_bound, wfs2Score_one_constant⟩


/-- Physical Legendre-Fenchel score is -E for the quadratic subfamily. -/
theorem physicalScore_eq_negative_original_E (u : ℝ) (r : Positive) :
    physicalScore u r =
      -LinearInputVariablePairs.energy 1 0 0 0 r.val 0 u := by
  dsimp [physicalScore, LinearInputVariablePairs.energy]
  ring

/-- The canonical x-only projection is an idempotent F0 observation. -/
def forgetU (z : ℝ × ℝ) : ℝ × ℝ := (z.1, 0)

theorem forgetU_idempotent : LinearInputF0.Idempotent forgetU := by
  intro z
  rfl

/-- The E automorphism does not descend to the x-only observation quotient.
This is exactly a failure of the F0-style relation K H K = K H. -/
theorem forgetU_H_not_descend (k lam c y : ℝ) :
    ¬ ∀ z : ℝ × ℝ,
      forgetU (H k lam c y (forgetU z)) =
        forgetU (H k lam c y z) := by
  intro h
  have hz := h (0, 1)
  have hx := congrArg Prod.fst hz
  dsimp [forgetU, H] at hx
  linarith

end LinearInputEWFSDual
