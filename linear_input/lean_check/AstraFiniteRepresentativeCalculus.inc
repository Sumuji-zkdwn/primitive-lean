
/-! Actual spatial and temporal calculus of the finite-space representatives. -/

namespace KerrKoopman.FiniteRepresentatives

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

open MeasureTheory MaterialL2 RealFourierDerivative

def lift (N : ℕ) (f : RealGalerkin.space N) (x : ℝ) : ℝ := representative N f (x : Circle)

theorem lift_add (N : ℕ) (f g : RealGalerkin.space N) :
    lift N (f+g) = fun x => lift N f x+lift N g x := by
  funext x
  simp [lift]

theorem lift_smul (N : ℕ) (a : ℝ) (f : RealGalerkin.space N) :
    lift N (a • f) = fun x => a*lift N f x := by
  funext x
  simp [lift]

theorem lift_zero (N : ℕ) : lift N 0 = fun _ => 0 := by
  funext x
  simp [lift]

def cosineVector (N k : ℕ) (hk : k ≤ N) : RealGalerkin.space N :=
  ⟨RealGalerkin.cosineL2 k, cosine_mem N k hk⟩

def sineVector (N k : ℕ) (hk : k ≤ N) : RealGalerkin.space N :=
  ⟨RealGalerkin.sineL2 k, sine_mem N k hk⟩

theorem representative_cosineVector (N k : ℕ) (hk : k ≤ N) :
    representative N (cosineVector N k hk) = RealGalerkin.cosine k :=
  representative_unique N _ _ rfl

theorem representative_sineVector (N k : ℕ) (hk : k ≤ N) :
    representative N (sineVector N k hk) = RealGalerkin.sine k :=
  representative_unique N _ _ rfl

theorem lift_cosineVector (N k : ℕ) (hk : k ≤ N) :
    lift N (cosineVector N k hk) = fun x => Real.cos ((k : ℝ)*x) := by
  funext x
  rw [lift, representative_cosineVector, cosine_coe]

theorem lift_sineVector (N k : ℕ) (hk : k ≤ N) :
    lift N (sineVector N k hk) = fun x => Real.sin ((k : ℝ)*x) := by
  funext x
  rw [lift, representative_sineVector, sine_coe]

theorem finiteDerivative_cosineVector (N k : ℕ) (hk : k ≤ N) :
    finiteDerivative N (cosineVector N k hk) = -(k : ℝ) • sineVector N k hk := by
  apply Subtype.ext
  exact derivative_cosine N k hk

theorem finiteDerivative_sineVector (N k : ℕ) (hk : k ≤ N) :
    finiteDerivative N (sineVector N k hk) = (k : ℝ) • cosineVector N k hk := by
  apply Subtype.ext
  exact derivative_sine N k hk

attribute [local irreducible] representative finiteEquiv RealFourierDerivative.finiteDerivative

/-- The previously constructed Q is the actual spatial derivative of the smooth representative. -/
theorem lift_hasDerivAt (N : ℕ) (f : RealGalerkin.space N) (x : ℝ) :
    HasDerivAt (lift N f) (lift N (finiteDerivative N f) x) x := by
  obtain ⟨f, hf⟩ := f
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨⟨k, b⟩, rfl⟩ := hf
      have hk : k.val ≤ N := by omega
      cases b
      · change HasDerivAt (lift N (sineVector N k.val hk))
          (lift N (finiteDerivative N (sineVector N k.val hk)) x) x
        rw [lift_sineVector, finiteDerivative_sineVector, lift_smul, lift_cosineVector]
        convert ((hasDerivAt_id x).const_mul (k.val : ℝ)).sin using 1
        simp only [id_eq]
        ring
      · change HasDerivAt (lift N (cosineVector N k.val hk))
          (lift N (finiteDerivative N (cosineVector N k.val hk)) x) x
        rw [lift_cosineVector, finiteDerivative_cosineVector, lift_smul, lift_sineVector]
        convert ((hasDerivAt_id x).const_mul (k.val : ℝ)).cos using 1
        simp only [id_eq]
        ring
  | zero =>
      change HasDerivAt (lift N 0) (lift N (finiteDerivative N 0) x) x
      rw [map_zero, lift_zero]
      exact hasDerivAt_const x 0
  | add f g hf hg ihf ihg =>
      change HasDerivAt (lift N (⟨f,hf⟩+⟨g,hg⟩))
        (lift N (finiteDerivative N (⟨f,hf⟩+⟨g,hg⟩)) x) x
      rw [lift_add, map_add, lift_add]
      exact ihf.add ihg
  | smul a f hf ih =>
      change HasDerivAt (lift N (a • (⟨f,hf⟩ : RealGalerkin.space N)))
        (lift N (finiteDerivative N (a • (⟨f,hf⟩ : RealGalerkin.space N))) x) x
      rw [lift_smul, map_smul, lift_smul]
      exact ih.const_mul a

theorem lift_deriv (N : ℕ) (f : RealGalerkin.space N) :
    deriv (lift N f) = lift N (finiteDerivative N f) := by
  funext x
  exact (lift_hasDerivAt N f x).deriv

theorem lift_continuous (N : ℕ) (f : RealGalerkin.space N) : Continuous (lift N f) :=
  continuous_iff_continuousAt.mpr (fun x => (lift_hasDerivAt N f x).continuousAt)

theorem lift_contDiff (N : ℕ) (f : RealGalerkin.space N) : ContDiff ℝ ⊤ (lift N f) := by
  obtain ⟨f,hf⟩ := f
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨⟨k,b⟩, rfl⟩ := hf
      have hk : k.val ≤ N := by omega
      cases b
      · change ContDiff ℝ ⊤ (lift N (sineVector N k.val hk))
        rw [lift_sineVector]
        fun_prop
      · change ContDiff ℝ ⊤ (lift N (cosineVector N k.val hk))
        rw [lift_cosineVector]
        fun_prop
  | zero => change ContDiff ℝ ⊤ (lift N 0); rw [lift_zero]; exact contDiff_const
  | add f g hf hg ihf ihg =>
      change ContDiff ℝ ⊤ (lift N (⟨f,hf⟩+⟨g,hg⟩))
      rw [lift_add]
      exact ihf.add ihg
  | smul a f hf ih =>
      change ContDiff ℝ ⊤ (lift N (a • (⟨f,hf⟩ : RealGalerkin.space N)))
      rw [lift_smul]
      exact contDiff_const.mul ih

theorem lift_periodic (N : ℕ) (f : RealGalerkin.space N) :
    Function.Periodic (lift N f) (2*Real.pi) := by
  intro x
  simp only [lift, AddCircle.coe_add_period]

theorem lift_endpoint (N : ℕ) (f : RealGalerkin.space N) :
    lift N f (2*Real.pi) = lift N f 0 := by
  simpa only [zero_add] using lift_periodic N f 0

theorem lift_time_hasDerivAt (N : ℕ) (z : ℝ → RealGalerkin.space N)
    (dz : RealGalerkin.space N) (t x : ℝ) (hz : HasDerivAt z dz t) :
    HasDerivAt (fun s => lift N (z s) x) (lift N dz x) t :=
  evaluate_hasDerivAt N z dz t x hz

end
end KerrKoopman.FiniteRepresentatives
