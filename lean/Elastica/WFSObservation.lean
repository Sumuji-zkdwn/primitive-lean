import Mathlib

/-!
# WFS projective lift and sampled cyclic observations

This file is a standalone, additive model; it does not infer a WFS
response law from the primitive elastica energy.  The lift is on
homogeneous coordinate pairs, not a constructed projective quotient.
Its invertibility ensures that it descends to the projective line.

For the sampling theorem, the state is the *fully observed* cyclic group
ZMod m and m > 0.  Additional non-injective sensors need separate hypotheses.
-/

namespace LinearInputWFSObservation

/-- Lift of z ↦ -z / (1 + 2*z) to homogeneous coordinate pairs [X:Y]. -/
def wfsLift (p : ℝ × ℝ) : ℝ × ℝ :=
  (-p.1, 2 * p.1 + p.2)

/-- Gauge C: [X:Y] ↦ [X:X+Y], corresponding to w = z/(1+z). -/
def gauge (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1, p.1 + p.2)

def gaugeInv (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1, p.2 - p.1)

/-- The normal form is a reflection, not a general nonlinear map. -/
def reflection (p : ℝ × ℝ) : ℝ × ℝ :=
  (-p.1, p.2)

theorem gaugeInv_gauge (p : ℝ × ℝ) :
    gaugeInv (gauge p) = p := by
  rcases p with ⟨x, y⟩
  apply Prod.ext
  · rfl
  · change x + y - x = y
    ring

theorem gauge_gaugeInv (p : ℝ × ℝ) :
    gauge (gaugeInv p) = p := by
  rcases p with ⟨x, y⟩
  apply Prod.ext
  · rfl
  · change x + (y - x) = y
    ring

/-- Exact conjugacy of the homogeneous linear maps: C ∘ T = R ∘ C. -/
theorem gauge_wfsLift (p : ℝ × ℝ) :
    gauge (wfsLift p) = reflection (gauge p) := by
  rcases p with ⟨x, y⟩
  apply Prod.ext
  · rfl
  · change -x + (2 * x + y) = x + y
    ring

theorem wfsLift_involutive : Function.Involutive wfsLift := by
  intro p
  rcases p with ⟨x, y⟩
  apply Prod.ext
  · change -(-x) = x
    ring
  · change 2 * (-x) + (2 * x + y) = y
    ring

theorem reflection_involutive : Function.Involutive reflection := by
  intro p
  rcases p with ⟨x, y⟩
  apply Prod.ext
  · change -(-x) = x
    ring
  · rfl

/-- Sampling a cyclic rotation d steps at a time: x ↦ d*x (mod m). -/
def sample (m d : ℕ) (x : ZMod m) : ZMod m :=
  (d : ZMod m) * x

/--
For a positive period m, d-step sampling is injective precisely when
d and m are coprime.  The positivity hypothesis matters: ZMod 0 is
the infinite cyclic group, where x ↦ 2*x is injective.
-/
theorem sample_injective_iff_coprime (m d : ℕ) (hm : 0 < m) :
    Function.Injective (sample m d) ↔ Nat.Coprime d m := by
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  constructor
  · intro hinj
    have hsurj : Function.Surjective (sample m d) :=
      Finite.surjective_of_injective hinj
    obtain ⟨x, hx⟩ := hsurj 1
    have hu : IsUnit (d : ZMod m) := by
      apply IsUnit.of_mul_eq_one x
      simpa [sample] using hx
    exact (ZMod.isUnit_iff_coprime d m).mp hu
  · intro hcop
    intro x y hxy
    have hleft : (d : ZMod m)⁻¹ * (d : ZMod m) = 1 := by
      calc
        _ = (d : ZMod m) * (d : ZMod m)⁻¹ := mul_comm _ _
        _ = 1 := ZMod.coe_mul_inv_eq_one d hcop
    have h := congrArg (fun z : ZMod m => (d : ZMod m)⁻¹ * z) hxy
    simpa only [sample, ← mul_assoc, hleft, one_mul] using h

/-- A four-state clockwise/counterclockwise ambiguity at two-step sampling. -/
theorem four_state_two_step_alias :
    sample 4 2 (1 : ZMod 4) = sample 4 2 (3 : ZMod 4) := by
  decide

theorem four_state_one_step_separates :
    sample 4 1 (1 : ZMod 4) ≠ sample 4 1 (3 : ZMod 4) := by
  decide

def samplePair (m d e : ℕ) (x : ZMod m) : ZMod m × ZMod m :=
  (sample m d x, sample m e x)

/-- Two individually lossy samplers jointly identify every six-state phase. -/
theorem six_state_two_three_joint_injective :
    Function.Injective (samplePair 6 2 3) := by
  decide

end LinearInputWFSObservation
