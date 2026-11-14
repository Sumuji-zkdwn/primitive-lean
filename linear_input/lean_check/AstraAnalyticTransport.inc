
/-! Time differentiation of the actual restored infinite Fourier series from
an actual mild coefficient identity. The PDE is a conclusion, not a hypothesis. -/

namespace KerrKoopman.AnalyticTransport

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Filter AnalyticDuhamel AnalyticPhysicalMode AnalyticFourierDuhamel
open Phase3WeightedConvolution Phase3WeightedDerivative Phase3WeightedRealDecode
open scoped Topology ENNReal

def analyticWidth (T : ℝ) : C(Time T, ℝ) := ⟨fun t => 1 / 2 - (t : ℝ), by fun_prop⟩

theorem analyticWidth_lower (T : ℝ) (hT : T ≤ 1 / 5) (t : Time T) :
    (3 / 10 : ℝ) ≤ analyticWidth T t := by
  change 3 / 10 ≤ 1 / 2 - (t : ℝ)
  linarith [t.property.2]

def extendedMode (T : ℝ) (hT : 0 ≤ T) (u : AnalyticLift.Scalar T)
    (k : ℤ) (t x : ℝ) : ℂ :=
  modeValue (1 / 2 - t) k (extend T hT (u k) t) x

def decodedExtension (T : ℝ) (hT : 0 ≤ T) (u : AnalyticLift.Scalar T) (t x : ℝ) : ℂ :=
  ∑' k, extendedMode T hT u k t x

theorem extend_at (T : ℝ) (hT : 0 ≤ T) (f : C(Time T, ℂ)) (t : Time T) :
    extend T hT f t = f t := by simp [extend, Set.projIcc_val]

theorem decodedExtension_eq (T : ℝ) (hT : 0 ≤ T) (u : AnalyticLift.Scalar T) (t : Time T) (x : ℝ) :
    decodedExtension T hT u t x = rawDecode (analyticWidth T) u t x := by
  unfold decodedExtension rawDecode
  apply tsum_congr
  intro k
  simp [extendedMode, extend_at, analyticWidth]

def spatialPhase (k : ℤ) (x : ℝ) : ℂ := Complex.exp ((((k : ℝ) * x : ℝ) : ℂ) * Complex.I)

theorem modeValue_factor (r : ℝ) (k : ℤ) (a : ℂ) (x : ℝ) :
    modeValue r k a x = (Real.exp (-r * |(k : ℝ)|) : ℂ) * a * spatialPhase k x := by
  rw [modeValue, Complex.exp_add, ← Complex.ofReal_exp]
  unfold spatialPhase
  ring

def MildCoefficients (T : ℝ) (hT : 0 ≤ T) (c : ℝ)
    (a : ℤ → ℂ) (u f : AnalyticLift.Scalar T) : Prop :=
  ∀ k (t : Time T), u k t =
    AnalyticLift.waveFactor T 1 c k 1 t * a k + mode T hT 1 c (by norm_num) k (f k) t

theorem physicalTrace_eq (T : ℝ) (hT : 0 ≤ T) (c : ℝ) (a : ℤ → ℂ)
    (u f : AnalyticLift.Scalar T) (hm : MildCoefficients T hT c a u f)
    (k : ℤ) (t : Time T) :
    physicalTrace (1/2) T hT 1 (c * k) k (a k) (f k) t =
      damping (1/2) 1 |(k : ℝ)| t * u k t := by
  unfold physicalTrace
  congr 1
  have hw := weightedTrace_eq T hT 1 c 1 (by norm_num) k (a k) (f k) t
  simp only [one_mul] at hw
  exact hw.trans (hm k t).symm

theorem extendedMode_eq_physical (T : ℝ) (hT : 0 ≤ T) (c : ℝ) (a : ℤ → ℂ)
    (u f : AnalyticLift.Scalar T) (hm : MildCoefficients T hT c a u f)
    (k : ℤ) (t : Time T) (x : ℝ) :
    extendedMode T hT u k t x =
      physicalTrace (1/2) T hT 1 (c * k) k (a k) (f k) t * spatialPhase k x := by
  rw [physicalTrace_eq T hT c a u f hm]
  simp only [extendedMode, extend_at, modeValue_factor, damping, one_mul]

def timeModeDerivative (T : ℝ) (hT : 0 ≤ T) (c : ℝ)
    (u f : AnalyticLift.Scalar T) (k : ℤ) (t x : ℝ) : ℂ :=
  -(c : ℂ) * modeDerivative (1/2-t) k (extend T hT (u k) t) x -
    modeDerivative (1/2-t) k (extend T hT (f k) t) x

theorem extendedMode_hasDerivAt (T : ℝ) (hT : 0 ≤ T) (c : ℝ) (a : ℤ → ℂ)
    (u f : AnalyticLift.Scalar T) (hm : MildCoefficients T hT c a u f)
    (k : ℤ) (t x : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun s => extendedMode T hT u k s x) (timeModeDerivative T hT c u f k t x) t := by
  let tt : Time T := ⟨t, ht.1.le, ht.2.le⟩
  have hd := (physicalTrace_hasDerivAt (1/2) T hT 1 (c * k) k (a k) (f k) tt).mul_const
    (spatialPhase k x)
  have he : (fun s => extendedMode T hT u k s x) =ᶠ[𝓝 t]
      (fun s => physicalTrace (1/2) T hT 1 (c * k) k (a k) (f k) s * spatialPhase k x) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact extendedMode_eq_physical T hT c a u f hm k ⟨s, hs.1.le, hs.2.le⟩ x
  have hd' := hd.congr_of_eventuallyEq he
  convert hd' using 1
  rw [physicalTrace_eq T hT c a u f hm k tt]
  change timeModeDerivative T hT c u f k (tt : ℝ) x = _
  simp only [timeModeDerivative, extend_at, modeDerivative, modeValue_factor, damping, one_mul]
  push_cast
  ring

theorem extended_spatial_norm_le (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1/5)
    (u : AnalyticLift.Scalar T) (k : ℤ) (t x : ℝ) (ht : t ∈ Ioo 0 T) :
    ‖modeDerivative (1/2-t) k (extend T hT (u k) t) x‖ ≤
      (Real.exp (-1) / (3/10)) * ‖u k‖ := by
  let tt : Time T := ⟨t, ht.1.le, ht.2.le⟩
  change ‖modeDerivative (1/2-(tt : ℝ)) k (extend T hT (u k) tt) x‖ ≤ _
  rw [extend_at]
  exact modeDerivative_norm_le (analyticWidth T) (3/10) (by norm_num)
    (analyticWidth_lower T hT1) u tt k x

theorem timeModeDerivative_norm_le (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1/5)
    (c : ℝ) (u f : AnalyticLift.Scalar T) (k : ℤ) (t x : ℝ) (ht : t ∈ Ioo 0 T) :
    ‖timeModeDerivative T hT c u f k t x‖ ≤
      (Real.exp (-1) / (3/10)) * (|c| * ‖u k‖ + ‖f k‖) := by
  have hu := extended_spatial_norm_le T hT hT1 u k t x ht
  have hf := extended_spatial_norm_le T hT hT1 f k t x ht
  calc
    _ ≤ |c| * ‖modeDerivative (1/2-t) k (extend T hT (u k) t) x‖ +
        ‖modeDerivative (1/2-t) k (extend T hT (f k) t) x‖ := by
      simpa only [timeModeDerivative, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
        using norm_sub_le (-(c : ℂ) * modeDerivative (1/2-t) k (extend T hT (u k) t) x)
          (modeDerivative (1/2-t) k (extend T hT (f k) t) x)
    _ ≤ |c| * ((Real.exp (-1) / (3/10)) * ‖u k‖) +
        (Real.exp (-1) / (3/10)) * ‖f k‖ :=
      add_le_add (mul_le_mul_of_nonneg_left hu (abs_nonneg c)) hf
    _ = _ := by ring

theorem extended_spatial_summable (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1/5)
    (u : AnalyticLift.Scalar T) (t x : ℝ) (ht : t ∈ Ioo 0 T) :
    Summable (fun k => modeDerivative (1/2-t) k (extend T hT (u k) t) x) := by
  exact Summable.of_norm_bounded ((l1_summable_norm u).mul_left (Real.exp (-1) / (3/10)))
    (fun k => extended_spatial_norm_le T hT hT1 u k t x ht)

theorem extendedMode_summable (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1/5)
    (u : AnalyticLift.Scalar T) (t : Time T) (x : ℝ) :
    Summable (fun k => extendedMode T hT u k t x) := by
  have hs := (summable_norm_modeValue (analyticWidth T)
    (fun s => (by norm_num : (0 : ℝ) ≤ 3/10).trans (analyticWidth_lower T hT1 s)) u t x).of_norm
  simpa only [extendedMode, extend_at, analyticWidth, ContinuousMap.coe_mk] using hs

theorem extendedDerivative_eq (T : ℝ) (hT : 0 ≤ T) (u : AnalyticLift.Scalar T)
    (t : Time T) (x : ℝ) :
    (∑' k, modeDerivative (1/2-(t : ℝ)) k (extend T hT (u k) t) x) =
      rawDerivative (analyticWidth T) u t x := by
  simp only [rawDerivative, extend_at, analyticWidth, ContinuousMap.coe_mk]

/-- Actual time differentiation of the full Fourier restoration. The input
identity is the modewise mild equation; the physical transport PDE follows. -/
theorem decodedExtension_hasDerivAt (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1/5)
    (c : ℝ) (a : ℤ → ℂ) (u f : AnalyticLift.Scalar T)
    (hm : MildCoefficients T hT c a u f) (t x : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun s => decodedExtension T hT u s x)
      (-(c : ℂ) * rawDerivative (analyticWidth T) u ⟨t, ht.1.le, ht.2.le⟩ x -
        rawDerivative (analyticWidth T) f ⟨t, ht.1.le, ht.2.le⟩ x) t := by
  have hmajor := (((l1_summable_norm u).mul_left |c|).add (l1_summable_norm f)).mul_left
    (Real.exp (-1) / (3/10))
  have hd := hasDerivAt_tsum_of_isPreconnected
    (g := fun k s => extendedMode T hT u k s x)
    (g' := fun k s => timeModeDerivative T hT c u f k s x)
    (y₀ := t) hmajor isOpen_Ioo (convex_Ioo (0 : ℝ) T).isPreconnected
    (fun k s hs => extendedMode_hasDerivAt T hT c a u f hm k s x hs)
    (fun k s hs => timeModeDerivative_norm_le T hT hT1 c u f k s x hs)
    ht (extendedMode_summable T hT hT1 u ⟨t, ht.1.le, ht.2.le⟩ x) ht
  convert hd using 1
  · rfl
  · simp only [timeModeDerivative]
    rw [Summable.tsum_sub ((extended_spatial_summable T hT hT1 u t x ht).mul_left (-(c : ℂ)))
      (extended_spatial_summable T hT hT1 f t x ht), tsum_mul_left]
    rw [extendedDerivative_eq T hT u ⟨t, ht.1.le, ht.2.le⟩,
      extendedDerivative_eq T hT f ⟨t, ht.1.le, ht.2.le⟩]

def realExtension (T : ℝ) (hT : 0 ≤ T) (u : AnalyticLift.Scalar T) (t x : ℝ) : ℝ :=
  (decodedExtension T hT u t x).re

theorem realExtension_eq (T : ℝ) (hT : 0 ≤ T) (u : AnalyticLift.Scalar T) (t : Time T) (x : ℝ) :
    realExtension T hT u t x = realDecode (analyticWidth T) u t x := by
  unfold realExtension realDecode
  rw [decodedExtension_eq]

theorem realExtension_hasDerivAt (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1/5)
    (c : ℝ) (a : ℤ → ℂ) (u f : AnalyticLift.Scalar T)
    (hm : MildCoefficients T hT c a u f) (t x : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun s => realExtension T hT u s x)
      (-c * realDerivative (analyticWidth T) u ⟨t, ht.1.le, ht.2.le⟩ x -
        realDerivative (analyticWidth T) f ⟨t, ht.1.le, ht.2.le⟩ x) t := by
  have hd := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
    (decodedExtension_hasDerivAt T hT hT1 c a u f hm t x ht)
  convert hd using 1
  · rfl
  · simp [realDerivative]

end
end KerrKoopman.AnalyticTransport
