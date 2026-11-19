/-!
All-degree signature invariance under an actual continuously differentiable
change of time. The derivative is supplied with a HasDerivAt proof, and the
transformed velocity includes its Jacobian. Monotonicity is unnecessary for
this C1 substitution identity. General singular BV reparametrizations require
the separate Stieltjes construction.
-/

noncomputable section

namespace LinearInputCurveWordReparametrization
open Real MeasureTheory
open LinearInputCurveWordSignature LinearInputCurveWordChen

theorem reverseIntegral_reparametrize {ι : Type*} {v : ι → ℝ → ℝ}
    (hv : ∀ i, Continuous (v i)) {g g' : ℝ → ℝ}
    (hg : ∀ t, HasDerivAt g (g' t) t) (hg' : Continuous g')
    (a b : ℝ) (w : List ι) :
    reverseIntegral (fun i t => g' t * v i (g t)) a w b =
      reverseIntegral v (g a) w (g b) := by
  have hgc : Continuous g := (show Differentiable ℝ g from fun t => (hg t).differentiableAt).continuous
  induction w generalizing b with
  | nil => rfl
  | cons i w ih =>
    simp only [reverseIntegral, ih]
    have hd (t : ℝ) : HasDerivAt
        (fun t => reverseIntegral v (g a) (i :: w) (g t))
        (reverseIntegral v (g a) w (g t) * (g' t * v i (g t))) t := by
      convert (reverseIntegral_hasDerivAt hv (g a) (g t) i w).comp t (hg t) using 1
      · rfl
      · ring
    have hc : Continuous (fun t => reverseIntegral v (g a) w (g t) * (g' t * v i (g t))) :=
      ((reverseIntegral_continuous hv (g a) w).comp hgc).mul (hg'.mul ((hv i).comp hgc))
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
      (hc.intervalIntegrable a b)
    simpa only [reverseIntegral, intervalIntegral.integral_same, sub_zero] using hi

theorem signature_reparametrize {ι : Type*} {v : ι → ℝ → ℝ}
    (hv : ∀ i, Continuous (v i)) {g g' : ℝ → ℝ}
    (hg : ∀ t, HasDerivAt g (g' t) t) (hg' : Continuous g')
    (a b : ℝ) (w : List ι) :
    signature (fun i t => g' t * v i (g t)) a b w = signature v (g a) (g b) w :=
  reverseIntegral_reparametrize hv hg hg' a b w.reverse

/-- Reversing a genuine velocity path gives its signature on the reversed
oriented interval, at every word degree. -/
theorem signature_reverse_time {ι : Type*} {v : ι → ℝ → ℝ}
    (hv : ∀ i, Continuous (v i)) (a b : ℝ) (w : List ι) :
    signature (fun i t => -v i (a + b - t)) a b w = signature v b a w := by
  have hg (t : ℝ) : HasDerivAt (fun t => a + b - t) (-1) t := by
    simpa using! (hasDerivAt_const t (a + b)).sub (hasDerivAt_id t)
  simpa only [neg_one_mul, add_sub_cancel_left, add_sub_cancel_right] using
    signature_reparametrize hv hg continuous_const a b w

theorem signature_reparametrize_same_endpoints {ι : Type*} {v : ι → ℝ → ℝ}
    (hv : ∀ i, Continuous (v i)) {g g' : ℝ → ℝ}
    (hg : ∀ t, HasDerivAt g (g' t) t) (hg' : Continuous g')
    (a b : ℝ) (ha : g a = a) (hb : g b = b) (w : List ι) :
    signature (fun i t => g' t * v i (g t)) a b w = signature v a b w := by
  rw [signature_reparametrize hv hg hg', ha, hb]

/-- A C1 time path returning to its starting parameter erases all nonempty
signature coefficients, even if it traverses the original curve repeatedly. -/
theorem signature_closed_reparametrize {ι : Type*} {v : ι → ℝ → ℝ}
    (hv : ∀ i, Continuous (v i)) {g g' : ℝ → ℝ}
    (hg : ∀ t, HasDerivAt g (g' t) t) (hg' : Continuous g')
    (a b : ℝ) (hend : g a = g b) (w : List ι) :
    signature (fun i t => g' t * v i (g t)) a b w = if w = [] then 1 else 0 := by
  rw [signature_reparametrize hv hg hg', ← hend]
  cases hw : w.reverse with
  | nil => have he : w = [] := List.reverse_eq_nil_iff.mp hw; simp [he, signature, reverseIntegral]
  | cons i u =>
    have he : w ≠ [] := by intro he; simp [he] at hw
    simp [signature, hw, reverseIntegral, he]

end LinearInputCurveWordReparametrization
