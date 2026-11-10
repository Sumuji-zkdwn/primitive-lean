/-!
Actual iterated interval integrals, homogeneous at every finite degree, and
the third moment of the tangent-angle reconstruction. The chronological word
convention is made explicit by reversing the internal recursion. No all-degree
Chen, tree-like uniqueness, or completed free-Lie assertion is assumed here.
-/

noncomputable section
open Real MeasureTheory

namespace LinearInputCurveWordSignature

/-- Internal recursion: the head is the latest integration coordinate. -/
def reverseIntegral {ι : Type*} (v : ι → ℝ → ℝ) (a : ℝ) : List ι → ℝ → ℝ
  | [], _ => 1
  | i :: w, b => ∫ t in a..b, reverseIntegral v a w t * v i t

/-- A coefficient in chronological order, defined by actual iterated integrals. -/
def signature {ι : Type*} (v : ι → ℝ → ℝ) (a b : ℝ) (w : List ι) : ℝ :=
  reverseIntegral v a w.reverse b

theorem reverseIntegral_scale {ι : Type*} (v : ι → ℝ → ℝ) (a σ : ℝ)
    (w : List ι) (b : ℝ) :
    reverseIntegral (fun i t => σ * v i t) a w b =
      σ ^ w.length * reverseIntegral v a w b := by
  induction w generalizing b with
  | nil => simp [reverseIntegral]
  | cons i w ih =>
    simp only [reverseIntegral, List.length_cons, ih]
    have he : (fun t => σ ^ w.length * reverseIntegral v a w t * (σ * v i t)) =
        fun t => σ ^ (w.length + 1) * (reverseIntegral v a w t * v i t) := by
      funext t
      rw [pow_succ]
      ring
    rw [he, intervalIntegral.integral_const_mul]

/-- Spatially scaling a velocity scales every degree-m coefficient by σ^m. -/
theorem signature_scale {ι : Type*} (v : ι → ℝ → ℝ) (a b σ : ℝ) (w : List ι) :
    signature (fun i t => σ * v i t) a b w = σ ^ w.length * signature v a b w := by
  simpa only [signature, List.length_reverse] using reverseIntegral_scale v a σ w.reverse b

theorem signature_empty {ι : Type*} (v : ι → ℝ → ℝ) (a b : ℝ) :
    signature v a b [] = 1 := rfl

theorem signature_singleton {ι : Type*} (v : ι → ℝ → ℝ) (a b : ℝ) (i : ι) :
    signature v a b [i] = ∫ t in a..b, v i t := by
  simp [signature, reverseIntegral]

theorem signature_pair {ι : Type*} (v : ι → ℝ → ℝ) (a b : ℝ) (i j : ι) :
    signature v a b [i, j] = ∫ t in a..b, (∫ s in a..t, v i s) * v j t := by
  simp [signature, reverseIntegral]

theorem reverseIntegral_continuous {ι : Type*} {v : ι → ℝ → ℝ}
    (hv : ∀ i, Continuous (v i)) (a : ℝ) (w : List ι) :
    Continuous (reverseIntegral v a w) := by
  induction w with
  | nil => exact continuous_const
  | cons i w ih =>
    exact (intervalIntegral.differentiable_integral_of_continuous (ih.mul (hv i))).continuous

/-- The degree-one Chen identity is the interval-integral splitting law. -/
theorem signature_singleton_split {ι : Type*} {v : ι → ℝ → ℝ}
    (hv : ∀ i, Continuous (v i)) (a b c : ℝ) (i : ι) :
    signature v a c [i] = signature v a b [i] + signature v b c [i] := by
  simp only [signature_singleton]
  exact (intervalIntegral.integral_add_adjacent_intervals
    ((hv i).intervalIntegrable a b) ((hv i).intervalIntegrable b c)).symm

/-- Every degree-two coordinate satisfies Chen's cross-term formula, derived
from the actual nested integrals. This is not an all-degree Chen assumption. -/
theorem signature_pair_split {ι : Type*} {v : ι → ℝ → ℝ}
    (hv : ∀ i, Continuous (v i)) (a b c : ℝ) (i j : ι) :
    signature v a c [i,j] = signature v a b [i,j] + signature v b c [i,j] +
      signature v a b [i] * signature v b c [j] := by
  simp only [signature_pair, signature_singleton]
  have ha : Continuous (fun t => ∫ s in a..t, v i s) :=
    (intervalIntegral.differentiable_integral_of_continuous (hv i)).continuous
  have hb : Continuous (fun t => ∫ s in b..t, v i s) :=
    (intervalIntegral.differentiable_integral_of_continuous (hv i)).continuous
  have hsplit : (∫ t in a..b, (∫ s in a..t, v i s) * v j t) +
      (∫ t in b..c, (∫ s in a..t, v i s) * v j t) =
      (∫ t in a..c, (∫ s in a..t, v i s) * v j t) :=
    intervalIntegral.integral_add_adjacent_intervals
      ((ha.mul (hv j)).intervalIntegrable a b)
      ((ha.mul (hv j)).intervalIntegrable b c)
  have he : (fun t => (∫ s in a..t, v i s) * v j t) =
      fun t => (∫ s in a..b, v i s) * v j t + (∫ s in b..t, v i s) * v j t := by
    funext t
    rw [← intervalIntegral.integral_add_adjacent_intervals
      ((hv i).intervalIntegrable a b) ((hv i).intervalIntegrable b t)]
    ring
  have hrest : (∫ t in b..c, (∫ s in a..t, v i s) * v j t) =
      (∫ s in a..b, v i s) * (∫ t in b..c, v j t) +
        (∫ t in b..c, (∫ s in b..t, v i s) * v j t) := by
    have hc : IntervalIntegrable (fun t => (∫ s in a..b, v i s) * v j t)
        volume b c := (continuous_const.mul (hv j)).intervalIntegrable b c
    have ht : IntervalIntegrable (fun t => (∫ s in b..t, v i s) * v j t)
        volume b c := (hb.mul (hv j)).intervalIntegrable b c
    rw [he, intervalIntegral.integral_add hc ht, intervalIntegral.integral_const_mul]
  linarith

/-- False is x and true is y for the actual unit-speed reconstruction. -/
def tangentVelocity (θ : ℝ → ℝ) (i : Bool) (t : ℝ) : ℝ :=
  if i then sin (θ t) else cos (θ t)

theorem signature_x (θ : ℝ → ℝ) (b : ℝ) :
    signature (tangentVelocity θ) 0 b [false] = Elastica.xCoord θ 0 b := by
  simp [signature_singleton, tangentVelocity, Elastica.xCoord]

theorem signature_y (θ : ℝ → ℝ) (b : ℝ) :
    signature (tangentVelocity θ) 0 b [true] = Elastica.yCoord θ 0 b := by
  simp [signature_singleton, tangentVelocity, Elastica.yCoord]

theorem signature_xx {θ : ℝ → ℝ} (hθ : Continuous θ) (b : ℝ) :
    signature (tangentVelocity θ) 0 b [false, false] = (Elastica.xCoord θ 0 b)^2 / 2 := by
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun s _ => Elastica.hasDerivAt_xCoord hθ 0 s)
    (fun s _ => Elastica.hasDerivAt_xCoord hθ 0 s)
    ((continuous_cos.comp hθ).intervalIntegrable 0 b)
    ((continuous_cos.comp hθ).intervalIntegrable 0 b)
  simp only [Elastica.xCoord_zero, mul_zero, sub_zero] at h
  have he : signature (tangentVelocity θ) 0 b [false, false] =
      ∫ s in 0..b, Elastica.xCoord θ 0 s * cos (θ s) := by
    simp [signature_pair, tangentVelocity, Elastica.xCoord]
  rw [he]
  have hh : (∫ s in 0..b, Elastica.xCoord θ 0 s * cos (θ s)) =
      Elastica.xCoord θ 0 b * Elastica.xCoord θ 0 b -
        (∫ s in 0..b, Elastica.xCoord θ 0 s * cos (θ s)) := by
    simpa only [mul_comm] using h
  nlinarith

/-- The cubic line integral from chain J, for the actual reconstructed curve. -/
def thirdMoment (θ : ℝ → ℝ) (b : ℝ) : ℝ :=
  ∫ s in 0..b, (Elastica.xCoord θ 0 s)^2 * sin (θ s)

theorem thirdMoment_eq_two_signature_xxy {θ : ℝ → ℝ} (hθ : Continuous θ) (b : ℝ) :
    thirdMoment θ b = 2 * signature (tangentVelocity θ) 0 b [false, false, true] := by
  have he : signature (tangentVelocity θ) 0 b [false, false, true] =
      ∫ s in 0..b, signature (tangentVelocity θ) 0 s [false, false] * sin (θ s) := by
    simp [signature, reverseIntegral, tangentVelocity]
  rw [he]
  simp only [signature_xx hθ]
  have hf : (fun s => (Elastica.xCoord θ 0 s)^2 / 2 * sin (θ s)) =
      fun s => (1 / 2 : ℝ) * ((Elastica.xCoord θ 0 s)^2 * sin (θ s)) := by
    funext s
    ring
  rw [hf, intervalIntegral.integral_const_mul]
  unfold thirdMoment
  ring

/-- Translation of a cubic line integral exposes its lower-order cross terms. -/
theorem translated_thirdMoment {θ : ℝ → ℝ} (hθ : Continuous θ) (b c : ℝ) :
    (∫ s in 0..b, (Elastica.xCoord θ 0 s + c)^2 * sin (θ s)) =
      thirdMoment θ b +
        2 * c * signature (tangentVelocity θ) 0 b [false, true] +
        c^2 * Elastica.yCoord θ 0 b := by
  have hx : Continuous (Elastica.xCoord θ 0) :=
    (show Differentiable ℝ (Elastica.xCoord θ 0) from
      fun s => (Elastica.hasDerivAt_xCoord hθ 0 s).differentiableAt).continuous
  have hs := continuous_sin.comp hθ
  have h1 : IntervalIntegrable (fun s => (Elastica.xCoord θ 0 s)^2 * sin (θ s))
      volume 0 b := (hx.pow 2 |>.mul hs).intervalIntegrable 0 b
  have h2 : IntervalIntegrable (fun s => (2*c) * (Elastica.xCoord θ 0 s * sin (θ s)))
      volume 0 b := (continuous_const.mul (hx.mul hs)).intervalIntegrable 0 b
  have h3 : IntervalIntegrable (fun s => c^2 * sin (θ s)) volume 0 b :=
    (continuous_const.mul hs).intervalIntegrable 0 b
  have he : (fun s => (Elastica.xCoord θ 0 s + c)^2 * sin (θ s)) =
      fun s => (Elastica.xCoord θ 0 s)^2 * sin (θ s) +
        (2*c) * (Elastica.xCoord θ 0 s * sin (θ s)) + c^2 * sin (θ s) := by
    funext s
    ring
  rw [he, intervalIntegral.integral_add (h1.add h2) h3,
    intervalIntegral.integral_add h1 h2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  simp [thirdMoment, signature_pair, tangentVelocity, Elastica.xCoord, Elastica.yCoord]

theorem translated_closed_thirdMoment {θ : ℝ → ℝ} (hθ : Continuous θ) (b c : ℝ)
    (hy : Elastica.yCoord θ 0 b = 0) :
    (∫ s in 0..b, (Elastica.xCoord θ 0 s + c)^2 * sin (θ s)) =
      thirdMoment θ b + 2*c * signature (tangentVelocity θ) 0 b [false, true] := by
  rw [translated_thirdMoment hθ, hy, mul_zero, add_zero]

end LinearInputCurveWordSignature
