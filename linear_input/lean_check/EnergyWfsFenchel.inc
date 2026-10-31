/-!
# Polynomial E, dual work, WFS coordinates and F0 forgetting

This is an additive bridge to the existing exact polynomial
LinearInputVariablePairs.energy, gradXu, and LinearInputF0.Idempotent.

The precise distinctions are:
1. The oriented gradient H_E is polynomially reversible.
2. The Fenchel objective can be transported along H_E only while
   respecting the fixed-input curve p = V'(q) - u.
3. The positive-domain WFS p=2 coordinate is reversible, but replacing
   the physical pairing ux with the naive pairing u G_2(x) changes
   the Fenchel objective.
4. A noninjective idempotent K cannot preserve *all* pointwise affine
   probes ux-V(x). This does not prohibit preserving a particular
   optimized value or a restricted family of observations.
5. The double-well potential has a positive barrier at zero, while every
   global affine minorant is nonpositive there.

No general Jacobian conjecture, gauge-independent naive conjugacy,
complete biconjugate theorem, or geometric packing optimality is claimed.
-/

noncomputable section

namespace LinearInputEnergyGaugeFenchel

open LinearInputVariablePairs

/-- The zero-input part of the original seven-parameter polynomial E. -/
def potential (k lam a c y x : ℝ) : ℝ :=
  LinearInputVariablePairs.energy k lam a c x y 0

/-- The exact x-gradient of the zero-input energy. -/
def force (k lam c y x : ℝ) : ℝ := k * x + lam * x ^ 3 - c * y

theorem energy_as_potential (k lam a c x y u : ℝ) :
    LinearInputVariablePairs.energy k lam a c x y u =
      potential k lam a c y x - u * x := by
  unfold potential LinearInputVariablePairs.energy
  ring

/-- An orientation-corrected gradient, with Jacobian +1. -/
def orientedGradient (k lam c y : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (force k lam c y z.1 - z.2, z.1)

/-- Its explicit polynomial inverse. -/
def orientedInverse (k lam c y : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.2, force k lam c y z.2 - z.1)

/-- The oriented map is precisely the original (x,u)-gradient with
the second output coordinate sign-reversed. -/
theorem orientedGradient_eq_original (k lam a c y : ℝ) (z : ℝ × ℝ) :
    orientedGradient k lam c y z =
      ((gradXu k lam a c (-1) y z).1,
       -(gradXu k lam a c (-1) y z).2) := by
  rw [gradXu_formula]
  apply Prod.ext <;> dsimp [orientedGradient, force] <;> ring

theorem orientedInverse_left (k lam c y : ℝ) (z : ℝ × ℝ) :
    orientedInverse k lam c y (orientedGradient k lam c y z) = z := by
  apply Prod.ext <;> dsimp [orientedGradient, orientedInverse] <;> ring

theorem orientedInverse_right (k lam c y : ℝ) (z : ℝ × ℝ) :
    orientedGradient k lam c y (orientedInverse k lam c y z) = z := by
  apply Prod.ext <;> dsimp [orientedGradient, orientedInverse] <;> ring

theorem orientedGradient_bijective (k lam c y : ℝ) :
    Function.Bijective (orientedGradient k lam c y) := by
  constructor
  · intro z w h
    have hz := congrArg (orientedInverse k lam c y) h
    simpa only [orientedInverse_left] using hz
  · intro z
    exact ⟨orientedInverse k lam c y z, orientedInverse_right k lam c y z⟩

/-- The fixed-u curve becomes p = V'(q)-u. -/
theorem fixed_input_curve (k lam c y x u : ℝ) :
    (orientedGradient k lam c y (x, u)).1 =
      force k lam c y (orientedGradient k lam c y (x, u)).2 - u := by
  rfl

/-- Stationary points land on the p=0 axis. -/
theorem stationary_iff_zero_first (k lam c y x u : ℝ) :
    force k lam c y x = u ↔
      (orientedGradient k lam c y (x, u)).1 = 0 := by
  change force k lam c y x = u ↔ force k lam c y x - u = 0
  constructor <;> intro h <;> linarith

/-- A fixed external input becomes the zero-first-coordinate curve
at a stationary point, not an entire unrestricted (p,q)-plane. -/
theorem stationary_curve (k lam c y x : ℝ) :
    orientedGradient k lam c y (x, force k lam c y x) = (0, x) := by
  apply Prod.ext <;> dsimp [orientedGradient] <;> ring

/-- The physical Fenchel pairing and the exact transported pairing. -/
def fenchelWork (k lam a c y u x : ℝ) : ℝ :=
  u * x - potential k lam a c y x

def transportedWork (k lam a c y : ℝ) (z : ℝ × ℝ) : ℝ :=
  (force k lam c y z.2 - z.1) * z.2 -
    potential k lam a c y z.2

theorem fenchelWork_transport (k lam a c y x u : ℝ) :
    transportedWork k lam a c y (orientedGradient k lam c y (x, u)) =
      fenchelWork k lam a c y u x := by
  unfold transportedWork orientedGradient fenchelWork
  ring

/-- The sets of values over the correct fixed-u curve are identical. -/
theorem fenchel_value_range_transport (k lam a c y u : ℝ) :
    Set.range (fun x : ℝ => fenchelWork k lam a c y u x) =
    Set.range (fun x : ℝ =>
      transportedWork k lam a c y (orientedGradient k lam c y (x, u))) := by
  have hfun :
      (fun x : ℝ => fenchelWork k lam a c y u x) =
      (fun x : ℝ =>
        transportedWork k lam a c y (orientedGradient k lam c y (x, u))) := by
    funext x
    exact (fenchelWork_transport k lam a c y x u).symm
  exact congrArg Set.range hfun

/-- A boundedness precondition is preserved together with the dual values. -/
theorem fenchel_bddAbove_transport (k lam a c y u : ℝ) :
    BddAbove (Set.range (fun x : ℝ => fenchelWork k lam a c y u x)) ↔
    BddAbove (Set.range (fun x : ℝ =>
      transportedWork k lam a c y (orientedGradient k lam c y (x, u)))) := by
  rw [fenchel_value_range_transport]

/-- This equality is about the true supremum when the value set is bounded
above; it is not a claim of global convexity of the original potential. -/
theorem fenchel_sSup_transport (k lam a c y u : ℝ)
    (hb : BddAbove (Set.range (fun x : ℝ => fenchelWork k lam a c y u x))) :
    sSup (Set.range (fun x : ℝ => fenchelWork k lam a c y u x)) =
    sSup (Set.range (fun x : ℝ =>
      transportedWork k lam a c y (orientedGradient k lam c y (x, u)))) := by
  rw [fenchel_value_range_transport]

/-- Minimizing E(x,y;u) at fixed y and u is equivalent to maximizing
the Fenchel work ux-V_y(x). -/
theorem energy_min_iff_fenchel_max (k lam a c y u x : ℝ) :
    (∀ z : ℝ,
      LinearInputVariablePairs.energy k lam a c x y u ≤
      LinearInputVariablePairs.energy k lam a c z y u) ↔
    (∀ z : ℝ, fenchelWork k lam a c y u z ≤
      fenchelWork k lam a c y u x) := by
  constructor
  · intro h z
    have hz := h z
    rw [energy_as_potential, energy_as_potential] at hz
    dsimp [fenchelWork]
    linarith
  · intro h z
    have hz := h z
    dsimp [fenchelWork] at hz
    rw [energy_as_potential, energy_as_potential]
    linarith

/-- WFS p=0 (logarithmic/Fechner) coordinate for positive intensity. -/
def wfsLog (r : ℝ) : ℝ := Real.log r

/-- WFS p=2 (power/Stevens) coordinate for positive intensity. -/
def wfsTwo (r : ℝ) : ℝ := (r ^ 2 - 1) / 2

def wfsTwoInverse (z : ℝ) : ℝ := Real.sqrt (2 * z + 1)

theorem wfs_log_exp (x : ℝ) :
    wfsLog (Real.exp x) = x := by
  simp [wfsLog]

theorem wfs_two_inverse_positive (x : ℝ) (hx : 0 ≤ x) :
    wfsTwoInverse (wfsTwo x) = x := by
  have harg : 2 * wfsTwo x + 1 = x ^ 2 := by
    unfold wfsTwo
    ring
  unfold wfsTwoInverse
  rw [harg]
  exact Real.sqrt_sq hx

theorem wfs_two_injective_positive {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) (h : wfsTwo x = wfsTwo y) :
    x = y := by
  have hsq : x ^ 2 = y ^ 2 := by
    unfold wfsTwo at h
    linarith
  rcases lt_trichotomy x y with hlt | heq | hgt
  · have hpos : 0 < (y - x) * (y + x) :=
      mul_pos (sub_pos.mpr hlt) (add_pos hy hx)
    nlinarith
  · exact heq
  · have hpos : 0 < (x - y) * (x + y) :=
      mul_pos (sub_pos.mpr hgt) (add_pos hx hy)
    nlinarith

/-- Exact pullback of the physical pairing, when the WFS coordinate is
reversibly decoded. This statement does not linearize in the new gauge. -/
theorem wfs_two_transported_work
    (V : ℝ → ℝ) (u x : ℝ) (hx : 0 ≤ x) :
    u * wfsTwoInverse (wfsTwo x) -
        V (wfsTwoInverse (wfsTwo x)) =
      u * x - V x := by
  rw [wfs_two_inverse_positive x hx]

/-- A concrete failure of naive WFS-coordinate linear duality:
take V(x)=x²/2 and replace the physical x by G₂(x). -/
theorem naive_wfs_two_work_constant (x : ℝ) :
    wfsTwo x - x ^ 2 / 2 = -(1 / 2 : ℝ) := by
  unfold wfsTwo
  ring

theorem physical_work_at_one :
    (1 : ℝ) * 1 - (1 : ℝ) ^ 2 / 2 = 1 / 2 := by
  norm_num

theorem naive_work_differs_at_one :
    (1 : ℝ) * 1 - (1 : ℝ) ^ 2 / 2 ≠
      wfsTwo 1 - (1 : ℝ) ^ 2 / 2 := by
  norm_num [wfsTwo]

/-- Exact preservation of every pointwise Fenchel probe is a far stronger
requirement than preservation of a single optimizer or supremum. -/
def affineProbe (V : ℝ → ℝ) (u x : ℝ) : ℝ := u * x - V x

theorem all_probes_force_injectivity {β : Type*}
    (K : ℝ → β) (V : ℝ → ℝ)
    (h : ∀ u x y : ℝ, K x = K y →
      affineProbe V u x = affineProbe V u y) :
    Function.Injective K := by
  intro x y hxy
  have h0 := h 0 x y hxy
  have h1 := h 1 x y hxy
  dsimp [affineProbe] at h0 h1
  linarith

/-- An F0 idempotent preserving every real-linear Fenchel probe must
be the identity; any genuine state forgetting breaks some such probe. -/
theorem f0_all_probes_imply_identity
    (K : ℝ → ℝ) (hK : LinearInputF0.Idempotent K)
    (V : ℝ → ℝ)
    (h : ∀ u x y : ℝ, K x = K y →
      affineProbe V u x = affineProbe V u y) :
    K = id := by
  have hi := all_probes_force_injectivity K V h
  funext x
  exact hi (hK x)

/-- A polynomial double-well member of the original E family. -/
def doubleWell (x : ℝ) : ℝ := (x ^ 2 - 1) ^ 2 / 4

theorem doubleWell_from_energy (x : ℝ) :
    doubleWell x =
      LinearInputVariablePairs.energy (-1) 1 (1 / 2) 0 x 1 0 := by
  unfold doubleWell LinearInputVariablePairs.energy
  ring

theorem doubleWell_nonnegative (x : ℝ) : 0 ≤ doubleWell x := by
  unfold doubleWell
  positivity

theorem doubleWell_at_zero : doubleWell 0 = 1 / 4 := by
  norm_num [doubleWell]

theorem doubleWell_at_one : doubleWell 1 = 0 := by
  norm_num [doubleWell]

theorem doubleWell_at_neg_one : doubleWell (-1) = 0 := by
  norm_num [doubleWell]

/-- Every global affine minorant of the double-well is nonpositive
at its central, positive-height barrier. -/
theorem doubleWell_affine_minorant_zero (m b : ℝ)
    (h : ∀ x : ℝ, m * x + b ≤ doubleWell x) :
    b ≤ 0 := by
  have hp := h 1
  have hm := h (-1)
  norm_num [doubleWell] at hp hm
  linarith

end LinearInputEnergyGaugeFenchel
