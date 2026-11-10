/-!
The all-degree rotated Chen law on the same single tangent-angle curve used
to realize Boolean words. The right-hand tensor action is the actual planar
rotation of the remaining piece, with its time origin translated explicitly.
-/

noncomputable section

namespace LinearInputCurveWordWordSignature

open Set
open LinearInputCurveWordSignature LinearInputCurveWordChen
open LinearInputCurveWordLinearAction LinearInputCurveWordReparametrization
open LinearInputCurveWordPiecewise LinearInputCurveWordArc

def angleVelocity (θ : ℝ → ℝ) : Bool → ℝ → ℝ
  | false => fun t => Real.cos (θ t)
  | true => fun t => Real.sin (θ t)

theorem angleVelocity_continuous {θ : ℝ → ℝ} (hθ : Continuous θ) (i : Bool) :
    Continuous (angleVelocity θ i) := by
  cases i
  · exact Real.continuous_cos.comp hθ
  · exact Real.continuous_sin.comp hθ

theorem angleVelocity_rotation (α : ℝ) (θ : ℝ → ℝ) :
    angleVelocity (fun t => α + θ t) = transformedVelocity (rotationMatrix α) (angleVelocity θ) := by
  funext i t
  cases i
  · rw [rotation_velocity_x]
    simp only [angleVelocity, Real.cos_add]
  · rw [rotation_velocity_y]
    simp only [angleVelocity, Real.sin_add]

theorem signature_time_translation {ι : Type*} (v : ι → ℝ → ℝ)
    (hv : ∀ i, Continuous (v i)) (a b c : ℝ) (w : List ι) :
    signature (fun i t => v i (t - c)) a b w = signature v (a - c) (b - c) w := by
  have hg (t : ℝ) : HasDerivAt (fun t => t - c) 1 t := by
    simpa using (hasDerivAt_id t).sub_const c
  simpa only [one_mul] using signature_reparametrize hv hg continuous_const a b w

theorem signature_splice_left {h : ℝ} (hh : 0 < h) (α : ℝ) (θ : ℝ → ℝ) (w : List Bool) :
    signature (angleVelocity (splice h α θ)) 0 h w =
      signature (angleVelocity (arcAngle h α)) 0 h w := by
  apply signature_congr_Icc _ _ hh.le
  intro i t ht
  cases i <;> simp only [angleVelocity, splice_left h α θ ht.2]

theorem signature_splice_right {h : ℝ} (hh : 0 < h) (α : ℝ) {θ : ℝ → ℝ}
    (hc : Continuous θ) (hz : θ 0 = 0) {L : ℝ} (hL : 0 ≤ L) (w : List Bool) :
    signature (angleVelocity (splice h α θ)) h (h + L) w =
      tensorAction (rotationMatrix α) (signature (angleVelocity θ) 0 L) w := by
  have he : signature (angleVelocity (splice h α θ)) h (h + L) w =
      signature (angleVelocity (fun t => α + θ (t - h))) h (h + L) w := by
    apply signature_congr_Icc _ _ (by linarith)
    intro i t ht
    cases i <;> simp only [angleVelocity, splice_right hh α θ hz ht.1]
  rw [he, angleVelocity_rotation]
  have hv : ∀ i, Continuous (angleVelocity (fun t => θ (t - h)) i) :=
    angleVelocity_continuous (hc.comp (continuous_id.sub continuous_const))
  rw [signature_linear_action _ _ hv]
  have hs : signature (angleVelocity (fun t => θ (t - h))) h (h + L) =
      signature (angleVelocity θ) 0 L := by
    funext u
    have ht := signature_time_translation (angleVelocity θ) (angleVelocity_continuous hc)
      h (h + L) h u
    have hfun : angleVelocity (fun t => θ (t - h)) = fun i t => angleVelocity θ i (t - h) := by
      funext i t
      cases i <;> rfl
    simpa only [hfun, sub_self, add_sub_cancel_left] using ht
  rw [hs]

/-- Rotated Chen is an identity on the constructed C1 curve, at every finite
tensor degree, with no abstract identification of a word and a curve assumed. -/
theorem actual_word_signature_cons {h : ℝ} (hh : 0 < h) (a : Bool)
    (word : List Bool) (w : List Bool) :
    signature (angleVelocity (wordAngle h (a :: word))) 0 (wordLength h (a :: word)) w =
      ∑ k ∈ Finset.range (w.length + 1),
        signature (angleVelocity (arcAngle h (letterAngle a))) 0 h (w.take k) *
          tensorAction (rotationMatrix (letterAngle a))
            (signature (angleVelocity (wordAngle h word)) 0 (wordLength h word)) (w.drop k) := by
  rw [wordLength_cons, signature_chen
    (angleVelocity_continuous (wordAngle_continuous hh (a :: word))) 0 h (h + wordLength h word) w]
  apply Finset.sum_congr rfl
  intro k _
  change signature (angleVelocity (splice h (letterAngle a) (wordAngle h word))) 0 h (w.take k) *
      signature (angleVelocity (splice h (letterAngle a) (wordAngle h word))) h
        (h + wordLength h word) (w.drop k) = _
  rw [signature_splice_left hh, signature_splice_right hh _ (wordAngle_continuous hh word)
    (wordAngle_initial hh word) (wordLength_nonneg hh word)]

end LinearInputCurveWordWordSignature
