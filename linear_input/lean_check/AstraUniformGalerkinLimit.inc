
/-! Uniform convergence on the entire physical time interval with one initial-only step count. -/
namespace KerrKoopman.GalerkinClassical
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter FiniteRepresentatives
open scoped Topology

theorem splittingNumerator_mono_time (N : ℕ) (s t r : ℝ)
    (hs : 0 ≤ s) (hst : s ≤ t) (hr : 0 ≤ r) :
    splittingNumerator N s r ≤ splittingNumerator N t r := by
  unfold splittingNumerator
  gcongr

theorem fixed_steps_error_le (T : ℝ) (hT : T ≤ 1/5)
    (base : ContinuumRelative.ClassicalKerrPair 0 IntervalFourier.period (Ioo 0 T))
    (D H : C(Circle, ℝ)) (control : ClassicalTailControl T base D H)
    (N : ℕ) (t : ℝ) (Efinal Hfinal : C(Circle, ℝ))
    (hEt : base.E t=realLift Efinal) (hHt : base.H t=realLift Hfinal) (ht : t ∈ Icc 0 T) :
    ‖approximation N (jointSteps N T ‖initialFields D H‖) t D H-initialFields Efinal Hfinal‖ ≤
      2*cutoffDecay N+1/((N : ℝ)+1) := by
  apply (approximation_error_le T hT base D H control N _ (jointSteps_pos N T _) t
    Efinal Hfinal hEt hHt ht).trans
  apply add_le_add le_rfl
  exact (div_le_div_of_nonneg_right
    (splittingNumerator_mono_time N t T _ ht.1 ht.2 (norm_nonneg _))
    (Nat.cast_nonneg _)).trans (jointSteps_budget N T _)

/-- A uniform-in-time L2 limit; the time-step count does not vary with the evaluation time. -/
theorem approximation_tendstoUniformlyOn (T : ℝ) (hT : T ≤ 1/5)
    (base : ContinuumRelative.ClassicalKerrPair 0 IntervalFourier.period (Ioo 0 T))
    (D H : C(Circle, ℝ)) (control : ClassicalTailControl T base D H)
    (Efinal Hfinal : ℝ → C(Circle, ℝ))
    (hEt : ∀ t ∈ Icc 0 T, base.E t=realLift (Efinal t))
    (hHt : ∀ t ∈ Icc 0 T, base.H t=realLift (Hfinal t)) :
    TendstoUniformlyOn
      (fun N t => approximation N (jointSteps N T ‖initialFields D H‖) t D H)
      (fun t => initialFields (Efinal t) (Hfinal t)) atTop (Icc 0 T) := by
  have hlim : Tendsto (fun N : ℕ => 2*cutoffDecay N+1/((N : ℝ)+1)) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_add] using
      (cutoffDecay_tendsto.const_mul 2).add tendsto_one_div_add_atTop_nhds_zero_nat
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with N hN
  intro t ht
  rw [dist_eq_norm, norm_sub_rev]
  exact (fixed_steps_error_le T hT base D H control N t (Efinal t) (Hfinal t)
    (hEt t ht) (hHt t ht) ht).trans_lt hN

end
end KerrKoopman.GalerkinClassical

