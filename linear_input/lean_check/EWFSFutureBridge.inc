/-!
# E/WFS reversible coordinates and future-minimal predictive states

Additive bridge between verified E/WFS and FutureObservations modules.

1. Any equivalence of whole states transports the entire future-observation
   quotient exactly, provided the transition and observer are transported too.
2. For the existing E polynomial H(x,u)=(kx+lambda*x^3-c*y-u,x),
   current and next observed x recover BOTH original coordinates. Thus the
   future-minimal state for the x-observer is the full pair, despite observing
   only one scalar at a time.
3. A positive WFS2 gauge of exp(x) does not change this conclusion.
4. For the zero-parameter rotation H(x,u)=(-u,x), a radial-intensity observer
   is invariant, yielding a genuine nontrivial lossless predictive quotient.

The WFS cotangent lift is only defined on positive physical intensities;
H does NOT in general preserve the positive half-plane. The statements about
WFS exp(x) below are an observation gauge, not a global conjugacy of H by
the positive-intensity cotangent lift. No nonlinear Fenchel pairing is being
silently identified with the original linear pairing.
-/

noncomputable section

namespace LinearInputEWFSFuture

open LinearInputFutureObservation LinearInputEWFSDual

/-- A fully reversible change of state coordinates. -/
def conjugatedUpdate {α β : Type*} (e : α ≃ β) (U : α → α) : β → β :=
  fun b => e (U (e.symm b))

def conjugatedObservation {α β ω : Type*}
    (e : α ≃ β) (K : α → ω) : β → ω :=
  fun b => K (e.symm b)

theorem conjugated_iterate {α β : Type*}
    (e : α ≃ β) (U : α → α) (t : ℕ) (x : α) :
    (conjugatedUpdate e U)^[t] (e x) = e (U^[t] x) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      calc
        (conjugatedUpdate e U)^[t + 1] (e x) =
            conjugatedUpdate e U ((conjugatedUpdate e U)^[t] (e x)) := by
              rw [Function.iterate_succ_apply']
        _ = e (U (U^[t] x)) := by rw [ih]; simp [conjugatedUpdate]
        _ = e (U^[t + 1] x) := by rw [Function.iterate_succ_apply']

/-- Exactly the same predictive equivalence, written in new coordinates. -/
theorem conjugate_future_iff {α β ω : Type*}
    (e : α ≃ β) (K : α → ω) (U : α → α) (x y : α) :
    FutureEq (conjugatedObservation e K) (conjugatedUpdate e U) (e x) (e y)
      ↔ FutureEq K U x y := by
  constructor
  · intro h t
    have ht := h t
    change K (e.symm ((conjugatedUpdate e U)^[t] (e x))) =
      K (e.symm ((conjugatedUpdate e U)^[t] (e y))) at ht
    rw [conjugated_iterate e U t x, conjugated_iterate e U t y] at ht
    simpa using ht
  · intro h t
    change K (e.symm ((conjugatedUpdate e U)^[t] (e x))) =
      K (e.symm ((conjugatedUpdate e U)^[t] (e y)))
    rw [conjugated_iterate e U t x, conjugated_iterate e U t y]
    simpa using h t

/-- Instantiate the general coordinate invariance with the E-polynomial
automorphism whose inverse was proved in EWFSFenchel.inc. -/
theorem E_coordinate_future_iff (k lam c y : ℝ)
    (K : (ℝ × ℝ) → ℝ) (U : (ℝ × ℝ) → (ℝ × ℝ))
    (z w : ℝ × ℝ) :
    FutureEq
        (conjugatedObservation (HEquiv k lam c y) K)
        (conjugatedUpdate (HEquiv k lam c y) U)
        (H k lam c y z) (H k lam c y w)
      ↔ FutureEq K U z w := by
  exact conjugate_future_iff (HEquiv k lam c y) K U z w

/-- Observing x now and after ONE E update determines the complete (x,u).
Thus there are no distinct future-equivalent states under the x observer. -/
theorem E_x_future_iff_eq (k lam c y : ℝ) (z w : ℝ × ℝ) :
    FutureEq observeX (H k lam c y) z w ↔ z = w := by
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    have hx : z.1 = w.1 := by
      simpa only [Function.iterate_zero, id_eq, observeX] using h0
    have hnext : (H k lam c y z).1 = (H k lam c y w).1 := by
      simpa only [Function.iterate_succ_apply, Function.iterate_zero, id_eq,
        observeX] using h1
    have hu : z.2 = w.2 := by
      dsimp [H] at hnext
      rw [hx] at hnext
      linarith
    exact Prod.ext hx hu
  · intro h
    subst w
    exact future_refl observeX (H k lam c y) z

/-- Any deterministically exact representation of x-readout for E dynamics
must be injective on the entire original (x,u) state space. -/
theorem E_exact_predictive_representation_injective {β : Type*}
    (k lam c y : ℝ) (f : (ℝ × ℝ) → β) (V : β → β) (out : β → ℝ)
    (hout : ∀ z, out (f z) = observeX z)
    (hstep : ∀ z, f (H k lam c y z) = V (f z)) :
    Function.Injective f := by
  intro z w hf
  apply (E_x_future_iff_eq k lam c y z w).1
  exact predictive_kernel_sub observeX (H k lam c y) f V out
    hout hstep hf

/-- Use exp(x) as a strictly positive physical intensity; this DOES NOT
require E's actual x-coordinate to be positive. -/
def positiveIntensity (z : ℝ × ℝ) : ℝ := Real.exp (observeX z)

theorem positiveIntensity_pos (z : ℝ × ℝ) : 0 < positiveIntensity z :=
  Real.exp_pos _

def perceptualObservation (z : ℝ × ℝ) : ℝ :=
  wfs2 (positiveIntensity z)

/-- The perceptual gauge does not create new future-equivalent pairs. -/
theorem E_wfs_future_iff_eq (k lam c y : ℝ) (z w : ℝ × ℝ) :
    FutureEq perceptualObservation (H k lam c y) z w ↔ z = w := by
  constructor
  · intro h
    apply (E_x_future_iff_eq k lam c y z w).1
    intro t
    have ht := h t
    change wfs2 (Real.exp (observeX ((H k lam c y)^[t] z))) =
      wfs2 (Real.exp (observeX ((H k lam c y)^[t] w))) at ht
    exact Real.exp_injective
      (wfs2_inj_pos (Real.exp_pos _) (Real.exp_pos _) ht)
  · intro h
    subst w
    exact future_refl perceptualObservation (H k lam c y) z

/-- A second observer for the same E dynamics: strictly positive quadratic
radius intensity. It is not asserted to equal the polynomial energy E. -/
def radialIntensity (z : ℝ × ℝ) : ℝ :=
  1 + z.1 ^ 2 + z.2 ^ 2

theorem radialIntensity_pos (z : ℝ × ℝ) : 0 < radialIntensity z := by
  dsimp [radialIntensity]
  nlinarith [sq_nonneg z.1, sq_nonneg z.2]

/-- At k=lambda=c=y=0, H is the quarter-turn (-u,x). -/
theorem zeroE_rotation (z : ℝ × ℝ) :
    H 0 0 0 0 z = (-z.2, z.1) := by
  apply Prod.ext <;> simp [H]

theorem radialIntensity_invariant (z : ℝ × ℝ) :
    radialIntensity (H 0 0 0 0 z) = radialIntensity z := by
  dsimp [H, radialIntensity]
  ring

/-- Exact fixed-observation dynamics over repeated updates. -/
theorem invariant_iterate {α ω : Type*}
    (K : α → ω) (U : α → α)
    (h : ∀ x, K (U x) = K x) (t : ℕ) (x : α) :
    K (U^[t] x) = K x := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [Function.iterate_succ_apply', h, ih]

theorem invariant_future_iff {α ω : Type*}
    (K : α → ω) (U : α → α)
    (h : ∀ x, K (U x) = K x) (x y : α) :
    FutureEq K U x y ↔ K x = K y := by
  constructor
  · intro heq
    simpa only [Function.iterate_zero, id_eq] using heq 0
  · intro heq t
    calc
      K (U^[t] x) = K x := invariant_iterate K U h t x
      _ = K y := heq
      _ = K (U^[t] y) := (invariant_iterate K U h t y).symm

/-- Unlike x observation, the radial-intensity observer is a genuine
lossless coarse-graining of the special rotation H. -/
theorem radial_future_iff (z w : ℝ × ℝ) :
    FutureEq radialIntensity (H 0 0 0 0) z w
      ↔ radialIntensity z = radialIntensity w := by
  exact invariant_future_iff radialIntensity (H 0 0 0 0)
    radialIntensity_invariant z w

/-- WFS2 on a positive, invariant radius does not alter this quotient. -/
theorem wfs_radial_future_iff (z w : ℝ × ℝ) :
    FutureEq (fun a => wfs2 (radialIntensity a)) (H 0 0 0 0) z w
      ↔ radialIntensity z = radialIntensity w := by
  constructor
  · intro h
    have h0 := h 0
    have hzero : wfs2 (radialIntensity z) = wfs2 (radialIntensity w) := by
      simpa only [Function.iterate_zero, id_eq] using h0
    exact wfs2_inj_pos (radialIntensity_pos z) (radialIntensity_pos w)
      hzero
  · intro hr t
    exact congrArg wfs2 ((radial_future_iff z w).2 hr t)

/-- Witness that radial perception merges distinct states while
preserving EVERY future radial WFS observation. -/
theorem nontrivial_radial_predictive_quotient :
    ((1 : ℝ), 0) ≠ ((-1 : ℝ), 0) ∧
      FutureEq (fun a => wfs2 (radialIntensity a))
        (H 0 0 0 0) (1, 0) (-1, 0) := by
  constructor
  · intro he
    have hx := congrArg Prod.fst he
    norm_num at hx
  · apply (wfs_radial_future_iff (1, 0) (-1, 0)).2
    norm_num [radialIntensity]

end LinearInputEWFSFuture
