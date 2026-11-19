/-!
The actual all-degree tensor action of a finite coordinate matrix on iterated
integrals. Each output index is transformed independently, including rotations.
-/

noncomputable section

namespace LinearInputCurveWordLinearAction

open MeasureTheory
open LinearInputCurveWordSignature LinearInputCurveWordChen

theorem reverseIntegral_congr_Icc {ι : Type*} (v u : ι → ℝ → ℝ) {a b : ℝ}
    (hab : a ≤ b) (he : ∀ i, Set.EqOn (v i) (u i) (Set.Icc a b)) (w : List ι) :
    reverseIntegral v a w b = reverseIntegral u a w b := by
  induction w generalizing b with
  | nil => rfl
  | cons i w ih =>
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    change reverseIntegral v a w t * v i t = reverseIntegral u a w t * u i t
    rw [ih ht.1 (fun j s hs => he j ⟨hs.1, hs.2.trans ht.2⟩), he i ht]

theorem signature_congr_Icc {ι : Type*} (v u : ι → ℝ → ℝ) {a b : ℝ}
    (hab : a ≤ b) (he : ∀ i, Set.EqOn (v i) (u i) (Set.Icc a b)) (w : List ι) :
    signature v a b w = signature u a b w :=
  reverseIntegral_congr_Icc v u hab he w.reverse

def reverseTensorAction {ι κ : Type*} [Fintype ι] (M : κ → ι → ℝ) :
    List κ → (List ι → ℝ) → ℝ
  | [], F => F []
  | j :: w, F => ∑ i, M j i * reverseTensorAction M w (fun u => F (i :: u))

/-- The coefficient formula for the degreewise tensor powers of a matrix,
using chronological word order. Every coefficient is a finite sum. -/
def tensorAction {ι κ : Type*} [Fintype ι] (M : κ → ι → ℝ)
    (F : List ι → ℝ) (w : List κ) : ℝ :=
  reverseTensorAction M w.reverse (fun u => F u.reverse)

def transformedVelocity {ι κ : Type*} [Fintype ι] (M : κ → ι → ℝ)
    (v : ι → ℝ → ℝ) (j : κ) (t : ℝ) : ℝ := ∑ i, M j i * v i t

theorem reverseTensorAction_mul_const {ι κ : Type*} [Fintype ι] (M : κ → ι → ℝ)
    (w : List κ) (F : List ι → ℝ) (r : ℝ) :
    reverseTensorAction M w (fun u => F u * r) = reverseTensorAction M w F * r := by
  induction w generalizing F with
  | nil => rfl
  | cons j w ih => simp only [reverseTensorAction, ih, ← mul_assoc, Finset.sum_mul]

theorem reverseTensorAction_continuous {ι κ : Type*} [Fintype ι] (M : κ → ι → ℝ)
    (w : List κ) (F : List ι → ℝ → ℝ) (hF : ∀ u, Continuous (F u)) :
    Continuous (fun t => reverseTensorAction M w (fun u => F u t)) := by
  induction w generalizing F with
  | nil => exact hF []
  | cons j w ih =>
    exact continuous_finsetSum _ (fun i _ => continuous_const.mul (ih _ (fun u => hF (i :: u))))

theorem reverseTensorAction_integral {ι κ : Type*} [Fintype ι] (M : κ → ι → ℝ)
    (w : List κ) (F : List ι → ℝ → ℝ) (hF : ∀ u, Continuous (F u)) (a b : ℝ) :
    (∫ t in a..b, reverseTensorAction M w (fun u => F u t)) =
      reverseTensorAction M w (fun u => ∫ t in a..b, F u t) := by
  induction w generalizing F with
  | nil => rfl
  | cons j w ih =>
    simp only [reverseTensorAction]
    have hint : ∀ i ∈ (Finset.univ : Finset ι), IntervalIntegrable
        (fun t => M j i * reverseTensorAction M w (fun u => F (i :: u) t)) volume a b := by
      intro i _
      exact (continuous_const.mul (reverseTensorAction_continuous M w _
        (fun u => hF (i :: u)))).intervalIntegrable a b
    rw [intervalIntegral.integral_finsetSum hint]
    apply Finset.sum_congr rfl
    intro i _
    rw [intervalIntegral.integral_const_mul, ih _ (fun u => hF (i :: u))]

theorem transformedVelocity_continuous {ι κ : Type*} [Fintype ι]
    (M : κ → ι → ℝ) (v : ι → ℝ → ℝ) (hv : ∀ i, Continuous (v i)) (j : κ) :
    Continuous (transformedVelocity M v j) :=
  continuous_finsetSum _ (fun i _ => continuous_const.mul (hv i))

theorem reverseIntegral_linear_action {ι κ : Type*} [Fintype ι]
    (M : κ → ι → ℝ) (v : ι → ℝ → ℝ) (hv : ∀ i, Continuous (v i))
    (a b : ℝ) (w : List κ) :
    reverseIntegral (transformedVelocity M v) a w b =
      reverseTensorAction M w (fun u => reverseIntegral v a u b) := by
  induction w generalizing b with
  | nil => rfl
  | cons j w ih =>
    simp only [reverseIntegral, ih, transformedVelocity, reverseTensorAction]
    have he : (fun t => reverseTensorAction M w (fun u => reverseIntegral v a u t) *
        ∑ i, M j i * v i t) =
        fun t => ∑ i, M j i * reverseTensorAction M w
          (fun u => reverseIntegral v a u t * v i t) := by
      funext t
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [reverseTensorAction_mul_const]
      ring
    have hint : ∀ i ∈ (Finset.univ : Finset ι), IntervalIntegrable
        (fun t => M j i * reverseTensorAction M w
          (fun u => reverseIntegral v a u t * v i t)) volume a b := by
      intro i _
      exact (continuous_const.mul (reverseTensorAction_continuous M w _
        (fun u => (reverseIntegral_continuous hv a u).mul (hv i)))).intervalIntegrable a b
    rw [he, intervalIntegral.integral_finsetSum hint]
    apply Finset.sum_congr rfl
    intro i _
    rw [intervalIntegral.integral_const_mul]
    exact congrArg (fun x => M j i * x) (reverseTensorAction_integral M w
      (fun u t => reverseIntegral v a u t * v i t)
      (fun u => (reverseIntegral_continuous hv a u).mul (hv i)) a b)

/-- All tensor degrees commute with an actual spatial linear transformation. -/
theorem signature_linear_action {ι κ : Type*} [Fintype ι]
    (M : κ → ι → ℝ) (v : ι → ℝ → ℝ) (hv : ∀ i, Continuous (v i))
    (a b : ℝ) (w : List κ) :
    signature (transformedVelocity M v) a b w = tensorAction M (signature v a b) w := by
  simpa only [signature, tensorAction, List.reverse_reverse] using
    reverseIntegral_linear_action M v hv a b w.reverse

def rotationMatrix (θ : ℝ) : Bool → Bool → ℝ
  | false, false => Real.cos θ
  | false, true => -Real.sin θ
  | true, false => Real.sin θ
  | true, true => Real.cos θ

theorem rotation_velocity_x (θ : ℝ) (v : Bool → ℝ → ℝ) (t : ℝ) :
    transformedVelocity (rotationMatrix θ) v false t =
      Real.cos θ * v false t - Real.sin θ * v true t := by
  simp [transformedVelocity, rotationMatrix]
  ring

theorem rotation_velocity_y (θ : ℝ) (v : Bool → ℝ → ℝ) (t : ℝ) :
    transformedVelocity (rotationMatrix θ) v true t =
      Real.sin θ * v false t + Real.cos θ * v true t := by
  simp [transformedVelocity, rotationMatrix]
  ring

theorem signature_rotation_all_degrees (θ : ℝ) (v : Bool → ℝ → ℝ)
    (hv : ∀ i, Continuous (v i)) (a b : ℝ) (w : List Bool) :
    signature (transformedVelocity (rotationMatrix θ) v) a b w =
      tensorAction (rotationMatrix θ) (signature v a b) w :=
  signature_linear_action (rotationMatrix θ) v hv a b w

/-- Chen after a spatial rotation, with the actual tensor action on both pieces. -/
theorem signature_rotation_chen (θ : ℝ) (v : Bool → ℝ → ℝ)
    (hv : ∀ i, Continuous (v i)) (a b c : ℝ) (w : List Bool) :
    signature (transformedVelocity (rotationMatrix θ) v) a c w =
      ∑ k ∈ Finset.range (w.length + 1),
        tensorAction (rotationMatrix θ) (signature v a b) (w.take k) *
          tensorAction (rotationMatrix θ) (signature v b c) (w.drop k) := by
  rw [signature_chen (transformedVelocity_continuous _ v hv) a b c w]
  simp only [signature_rotation_all_degrees θ v hv]

end LinearInputCurveWordLinearAction
