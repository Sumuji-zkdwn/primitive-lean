
/-! Analytic construction: actual characteristic transport of the weighted initial
coefficients and actual extraction of displacement from the two branches. -/

namespace KerrKoopman.AnalyticLift

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped Topology

abbrev Time (T : ℝ) := Set.Icc (0 : ℝ) T
abbrev Scalar (T : ℝ) := AnalyticLpMap.L1 ℤ C(Time T, ℂ)
abbrev Branches (T : ℝ) := AnalyticLpMap.L1 ℤ C(Time T, ℂ × ℂ)
abbrev Initial := AnalyticLpMap.L1 ℤ (ℂ × ℂ)

def waveFactor (T β c : ℝ) (k : ℤ) (σ : ℝ) : C(Time T, ℂ) :=
  ⟨fun t => (Real.exp (-β * (t : ℝ) * |(k : ℝ)|) : ℂ) *
    Complex.exp (((-σ * c * (k : ℝ) * (t : ℝ) : ℝ) : ℂ) * Complex.I), by fun_prop⟩

theorem waveFactor_norm_le (T β c : ℝ) (hβ : 0 ≤ β) (k : ℤ) (σ : ℝ) (t : Time T) :
    ‖waveFactor T β c k σ t‖ ≤ 1 := by
  change ‖(Real.exp (-β * (t : ℝ) * |(k : ℝ)|) : ℂ) *
    Complex.exp (((-σ * c * (k : ℝ) * (t : ℝ) : ℝ) : ℂ) * Complex.I)‖ ≤ 1
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hβ) t.property.1) (abs_nonneg _)

def freeTrace (T β c : ℝ) (k : ℤ) (a : ℂ × ℂ) : C(Time T, ℂ × ℂ) :=
  ⟨fun t => (waveFactor T β c k 1 t * a.1, waveFactor T β c k (-1) t * a.2), by fun_prop⟩

theorem freeTrace_norm_le (T β c : ℝ) (hβ : 0 ≤ β) (k : ℤ) (a : ℂ × ℂ) :
    ‖freeTrace T β c k a‖ ≤ ‖a‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro t
  change max ‖waveFactor T β c k 1 t * a.1‖ ‖waveFactor T β c k (-1) t * a.2‖ ≤
    max ‖a.1‖ ‖a.2‖
  apply max_le_max
  · rw [norm_mul]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (waveFactor_norm_le T β c hβ k 1 t) (norm_nonneg a.1)
  · rw [norm_mul]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (waveFactor_norm_le T β c hβ k (-1) t) (norm_nonneg a.2)

def freeTraceLinear (T β c : ℝ) (k : ℤ) : (ℂ × ℂ) →ₗ[ℝ] C(Time T, ℂ × ℂ) where
  toFun := freeTrace T β c k
  map_add' a b := by
    ext t <;> simp [freeTrace, mul_add]
  map_smul' r a := by
    ext t <;> simp [freeTrace] <;> ring

def freeTraceCLM (T β c : ℝ) (hβ : 0 ≤ β) (k : ℤ) :
    (ℂ × ℂ) →L[ℝ] C(Time T, ℂ × ℂ) :=
  (freeTraceLinear T β c k).mkContinuous 1 (fun a => by simpa using freeTrace_norm_le T β c hβ k a)

theorem freeTraceCLM_opNorm_le (T β c : ℝ) (hβ : 0 ≤ β) (k : ℤ) :
    ‖freeTraceCLM T β c hβ k‖ ≤ 1 := by
  apply (freeTraceCLM T β c hβ k).opNorm_le_bound (by norm_num)
  intro a
  simpa only [one_mul] using freeTrace_norm_le T β c hβ k a

/-- The supplied initial coefficients already include exp(rho0 |k|).
This map evolves them with physical characteristic phases and shrinking width. -/
def freeLift (T β c : ℝ) (hβ : 0 ≤ β) : Initial →L[ℝ] Branches T :=
  AnalyticLpMap.diagonal (freeTraceCLM T β c hβ) 1 (freeTraceCLM_opNorm_le T β c hβ)

theorem freeLift_apply (T β c : ℝ) (hβ : 0 ≤ β) (a : Initial) (k : ℤ) (t : Time T) :
    freeLift T β c hβ a k t =
      (waveFactor T β c k 1 t * (a k).1, waveFactor T β c k (-1) t * (a k).2) := rfl

theorem freeLift_norm_le (T β c : ℝ) (hβ : 0 ≤ β) (a : Initial) :
    ‖freeLift T β c hβ a‖ ≤ ‖a‖ := by
  simpa only [one_mul] using AnalyticLpMap.diagonal_norm_le
    (freeTraceCLM T β c hβ) 1 (freeTraceCLM_opNorm_le T β c hβ) a

theorem freeLift_initial (T β c : ℝ) (hT : 0 ≤ T) (hβ : 0 ≤ β) (a : Initial) (k : ℤ) :
    freeLift T β c hβ a k ⟨0, ⟨le_rfl, hT⟩⟩ = a k := by
  rw [freeLift_apply]
  simp [waveFactor]

theorem inverse_sqrt_two_le : (1 : ℝ) / Real.sqrt 2 ≤ 5 / 7 := by
  have hp : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs : (7 / 5 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  apply (div_le_iff₀ hp).mpr
  linarith

def displacementTrace (T : ℝ) (z : C(Time T, ℂ × ℂ)) : C(Time T, ℂ) :=
  ⟨fun t => (1 / Real.sqrt 2 : ℝ) • ((z t).1 - (z t).2), by fun_prop⟩

theorem displacementTrace_norm_le (T : ℝ) (z : C(Time T, ℂ × ℂ)) :
    ‖displacementTrace T z‖ ≤ (10 / 7 : ℝ) * ‖z‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  have hzt := z.norm_coe_le_norm t
  have hf : ‖(z t).1‖ ≤ ‖z‖ := (le_max_left _ _).trans hzt
  have hs : ‖(z t).2‖ ≤ ‖z‖ := (le_max_right _ _).trans hzt
  change ‖(1 / Real.sqrt 2 : ℝ) • ((z t).1 - (z t).2)‖ ≤ _
  rw [Complex.real_smul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ (5 / 7 : ℝ) * (‖(z t).1‖ + ‖(z t).2‖) :=
      mul_le_mul inverse_sqrt_two_le (norm_sub_le _ _) (norm_nonneg _) (by norm_num)
    _ ≤ (5 / 7 : ℝ) * (‖z‖ + ‖z‖) := by gcongr
    _ = _ := by ring

def displacementTraceLinear (T : ℝ) : C(Time T, ℂ × ℂ) →ₗ[ℝ] C(Time T, ℂ) where
  toFun := displacementTrace T
  map_add' z w := by
    ext t
    simp only [displacementTrace, ContinuousMap.coe_mk, ContinuousMap.add_apply,
      Prod.fst_add, Prod.snd_add]
    module
  map_smul' r z := by
    ext t
    change (1 / Real.sqrt 2 : ℝ) • (r • (z t).1 - r • (z t).2) =
      r • ((1 / Real.sqrt 2 : ℝ) • ((z t).1 - (z t).2))
    rw [← smul_sub, smul_comm]

def displacementTraceCLM (T : ℝ) : C(Time T, ℂ × ℂ) →L[ℝ] C(Time T, ℂ) :=
  (displacementTraceLinear T).mkContinuous (10 / 7) (displacementTrace_norm_le T)

theorem displacementTraceCLM_opNorm_le (T : ℝ) : ‖displacementTraceCLM T‖ ≤ 10 / 7 :=
  (displacementTraceCLM T).opNorm_le_bound (by norm_num) (displacementTrace_norm_le T)

def displacement (T : ℝ) : Branches T →L[ℝ] Scalar T :=
  AnalyticLpMap.diagonal (fun _ : ℤ => displacementTraceCLM T) (10 / 7)
    (fun _ => displacementTraceCLM_opNorm_le T)

theorem displacement_apply (T : ℝ) (z : Branches T) (k : ℤ) (t : Time T) :
    displacement T z k t = (1 / Real.sqrt 2 : ℝ) • ((z k t).1 - (z k t).2) := rfl

theorem displacement_opNorm_le (T : ℝ) : ‖displacement T‖ ≤ 10 / 7 :=
  AnalyticLpMap.diagonal_opNorm_le _ _ (by norm_num) (fun _ => displacementTraceCLM_opNorm_le T)

end

end KerrKoopman.AnalyticLift
