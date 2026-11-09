
/-! Identification of actual interval Fourier projection and actual real circle L2 projection. -/

namespace KerrKoopman.FiniteRepresentatives

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory MaterialL2
open scoped BigOperators Interval

def realLift (f : C(Circle, ℝ)) (x : ℝ) : ℝ := f (x : Circle)

theorem realLift_continuous (f : C(Circle, ℝ)) : Continuous (realLift f) :=
  f.continuous.comp (AddCircle.continuous_mk' (2*Real.pi))

theorem inner_toL2_interval (f g : C(Circle, ℝ)) :
    inner ℝ (toL2 f) (toL2 g) =
      (∫ x in 0..(2*Real.pi), realLift f x*realLift g x)/(2*Real.pi) := by
  rw [toL2, ContinuousMap.inner_toLp]
  simp only [conj_trivial]
  rw [haar_integral_eq_interval]
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  exact mul_comm _ _

theorem norm_toL2_sq_interval (f : C(Circle, ℝ)) :
    ‖toL2 f‖^2 = (∫ x in 0..(2*Real.pi), (realLift f x)^2)/(2*Real.pi) := by
  rw [← real_inner_self_eq_norm_sq, inner_toL2_interval]
  simp only [pow_two]

theorem cosine_continuousSpace_mem (N k : ℕ) (hk : k ≤ N) :
    RealGalerkin.cosine k ∈ continuousSpace N := by
  apply Submodule.subset_span
  exact ⟨(⟨k, by omega⟩, true), rfl⟩

theorem sine_continuousSpace_mem (N k : ℕ) (hk : k ≤ N) :
    RealGalerkin.sine k ∈ continuousSpace N := by
  apply Submodule.subset_span
  exact ⟨(⟨k, by omega⟩, false), rfl⟩

/-- A continuous circle polynomial with exactly the actual interval coefficients. -/
def circleProjection (N : ℕ) (f : C(Circle, ℝ)) : C(Circle, ℝ) :=
  IntervalFourier.mean (realLift f) • RealGalerkin.cosine 0 + ∑ k : Fin N,
    (IntervalFourier.cosCoeff (realLift f) (k.val+1) • RealGalerkin.cosine (k.val+1) +
     IntervalFourier.sinCoeff (realLift f) (k.val+1) • RealGalerkin.sine (k.val+1))

theorem circleProjection_mem (N : ℕ) (f : C(Circle, ℝ)) :
    circleProjection N f ∈ continuousSpace N := by
  apply (continuousSpace N).add_mem
  · exact (continuousSpace N).smul_mem _ (cosine_continuousSpace_mem N 0 (Nat.zero_le _))
  · apply (continuousSpace N).sum_mem
    intro k _
    exact (continuousSpace N).add_mem
      ((continuousSpace N).smul_mem _ (cosine_continuousSpace_mem N (k.val+1) (by omega)))
      ((continuousSpace N).smul_mem _ (sine_continuousSpace_mem N (k.val+1) (by omega)))

theorem realLift_circleProjection (N : ℕ) (f : C(Circle, ℝ)) :
    realLift (circleProjection N f) = IntervalFourier.projection N (realLift f) := by
  funext x
  simp [realLift, circleProjection, IntervalFourier.projection, FourierSupBounds.polynomial,
    cosine_coe, sine_coe]

theorem mean_projection (N : ℕ) (f : ℝ → ℝ) :
    IntervalFourier.mean (IntervalFourier.projection N f) = IntervalFourier.mean f :=
  IntervalFourier.mean_polynomial N _ _ _

theorem cosCoeff_projection (N k : ℕ) (f : ℝ → ℝ) (hk0 : 0<k) (hk : k ≤ N) :
    IntervalFourier.cosCoeff (IntervalFourier.projection N f) k = IntervalFourier.cosCoeff f k := by
  let j : Fin N := ⟨k-1, by omega⟩
  have hj : j.val+1=k := by dsimp [j]; omega
  have h := IntervalFourier.cosCoeff_polynomial N (IntervalFourier.mean f)
    (fun i => IntervalFourier.cosCoeff f (i.val+1))
    (fun i => IntervalFourier.sinCoeff f (i.val+1)) j
  simpa only [hj, IntervalFourier.projection] using h

theorem sinCoeff_projection (N k : ℕ) (f : ℝ → ℝ) (hk0 : 0<k) (hk : k ≤ N) :
    IntervalFourier.sinCoeff (IntervalFourier.projection N f) k = IntervalFourier.sinCoeff f k := by
  let j : Fin N := ⟨k-1, by omega⟩
  have hj : j.val+1=k := by dsimp [j]; omega
  have h := IntervalFourier.sinCoeff_polynomial N (IntervalFourier.mean f)
    (fun i => IntervalFourier.cosCoeff f (i.val+1))
    (fun i => IntervalFourier.sinCoeff f (i.val+1)) j
  simpa only [hj, IntervalFourier.projection] using h

theorem interval_residual_cos (N k : ℕ) (f : ℝ → ℝ) (cf : Continuous f) (hk : k ≤ N) :
    (∫ x in 0..IntervalFourier.period,
      (f x-IntervalFourier.projection N f x)*Real.cos ((k : ℝ)*x)) = 0 := by
  have cp := IntervalFourier.projection_continuous N f
  have hp : IntervalFourier.period ≠ 0 := by unfold IntervalFourier.period; positivity
  by_cases hk0 : k=0
  · subst k
    simp only [Nat.cast_zero, zero_mul, Real.cos_zero, mul_one]
    have hc := mean_projection N f
    unfold IntervalFourier.mean at hc
    have hi := congrArg (fun y : ℝ => y*IntervalFourier.period) hc
    simp only [div_mul_cancel₀ _ hp] at hi
    have hs : (∫ x in 0..IntervalFourier.period, f x-IntervalFourier.projection N f x) =
        (∫ x in 0..IntervalFourier.period, f x) -
          (∫ x in 0..IntervalFourier.period, IntervalFourier.projection N f x) :=
      intervalIntegral.integral_sub (cf.intervalIntegrable _ _) (cp.intervalIntegrable _ _)
    rw [hs, hi, sub_self]
  · have hc := cosCoeff_projection N k f (Nat.pos_of_ne_zero hk0) hk
    unfold IntervalFourier.cosCoeff at hc
    have hz : (2 : ℝ)/IntervalFourier.period ≠ 0 := div_ne_zero (by norm_num) hp
    have hi := mul_left_cancel₀ hz hc
    rw [IntervalFourier.weighted_integral_sub f _ _ cf cp (by fun_prop), hi, sub_self]

theorem interval_residual_sin (N k : ℕ) (f : ℝ → ℝ) (cf : Continuous f) (hk : k ≤ N) :
    (∫ x in 0..IntervalFourier.period,
      (f x-IntervalFourier.projection N f x)*Real.sin ((k : ℝ)*x)) = 0 := by
  have cp := IntervalFourier.projection_continuous N f
  by_cases hk0 : k=0
  · simp [hk0]
  · have hc := sinCoeff_projection N k f (Nat.pos_of_ne_zero hk0) hk
    unfold IntervalFourier.sinCoeff at hc
    have hp : IntervalFourier.period ≠ 0 := by unfold IntervalFourier.period; positivity
    have hz : (2 : ℝ)/IntervalFourier.period ≠ 0 := div_ne_zero (by norm_num) hp
    have hi := mul_left_cancel₀ hz hc
    rw [IntervalFourier.weighted_integral_sub f _ _ cf cp (by fun_prop), hi, sub_self]

/-- The interval coefficient operator equals the constructed real L2 orthogonal projection. -/
theorem toL2_circleProjection (N : ℕ) (f : C(Circle, ℝ)) :
    toL2 (circleProjection N f) = RealGalerkin.projection N (toL2 f) := by
  symm
  apply (RealGalerkin.space N).eq_starProjection_of_mem_of_inner_eq_zero
    (toL2_mem N (circleProjection_mem N f))
  intro w hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨⟨k,b⟩, rfl⟩ := hw
      have hk : k.val ≤ N := by omega
      rw [← map_sub]
      cases b
      · change inner ℝ (toL2 (f-circleProjection N f)) (toL2 (RealGalerkin.sine k.val)) = 0
        rw [inner_toL2_interval]
        have he : (fun x => realLift (f-circleProjection N f) x *
            realLift (RealGalerkin.sine k.val) x) =
            (fun x => (realLift f x-IntervalFourier.projection N (realLift f) x)*
              Real.sin ((k.val : ℝ)*x)) := by
          funext x
          simp only [realLift, ContinuousMap.sub_apply, sine_coe]
          rw [← realLift_circleProjection N f]
          rfl
        have hi := interval_residual_sin N k.val (realLift f) (realLift_continuous f) hk
        unfold IntervalFourier.period at hi
        rw [he, hi, zero_div]
      · change inner ℝ (toL2 (f-circleProjection N f)) (toL2 (RealGalerkin.cosine k.val)) = 0
        rw [inner_toL2_interval]
        have he : (fun x => realLift (f-circleProjection N f) x *
            realLift (RealGalerkin.cosine k.val) x) =
            (fun x => (realLift f x-IntervalFourier.projection N (realLift f) x)*
              Real.cos ((k.val : ℝ)*x)) := by
          funext x
          simp only [realLift, ContinuousMap.sub_apply, cosine_coe]
          rw [← realLift_circleProjection N f]
          rfl
        have hi := interval_residual_cos N k.val (realLift f) (realLift_continuous f) hk
        unfold IntervalFourier.period at hi
        rw [he, hi, zero_div]
  | zero => simp only [inner_zero_right]
  | add w z hw hz ihw ihz => rw [inner_add_right, ihw, ihz, add_zero]
  | smul c w hw ih => rw [inner_smul_right, ih, mul_zero]

theorem representative_projection_eq (N : ℕ) (f : C(Circle, ℝ)) :
    representative N ⟨RealGalerkin.projection N (toL2 f), RealGalerkin.projection_mem N _⟩ =
      circleProjection N f :=
  representative_unique N _ _ (toL2_circleProjection N f)

end
end KerrKoopman.FiniteRepresentatives
