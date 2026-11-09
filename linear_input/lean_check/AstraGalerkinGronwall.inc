
/-! Actual initial projection energy and actual Galerkin rate combined through interior-time Gronwall. -/

namespace KerrKoopman.GalerkinClassical

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter FiniteRepresentatives
open scoped Topology Interval

abbrev normalizedRelative {s : Set ℝ}
    (base : ContinuumRelative.ClassicalKerrPair 0 IntervalFourier.period s)
    (N : ℕ) (z : GalerkinFlow.State N) : ℝ → ℝ :=
  ContinuumGalerkin.ClassicalKerrPair.normalizedEnergy (withGalerkin base N z)

theorem actual_energy_envelope (T : ℝ)
    (base : ContinuumRelative.ClassicalKerrPair 0 IntervalFourier.period (Ioo 0 T))
    (N : ℕ) (D H : C(Circle, ℝ)) (A B t : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hD : ∀ x, Riccati.constitutive (base.E 0 x) = realLift D x) (hH : base.H 0=realLift H)
    (hc : ContinuousOn (normalizedRelative base N (projectedInitial N D H)) (Icc 0 T))
    (bound : ℝ → ℝ) (hb : IntervalIntegrable bound volume 0 IntervalFourier.period)
    (hbound : ∀ x ∈ uIcc 0 IntervalFourier.period, ∀ q ∈ Ioo 0 T,
      |(withGalerkin base N (projectedInitial N D H)).rate q x| ≤ bound x)
    (hHx : ∀ q ∈ Ioo 0 T, ∀ x ∈ Icc 0 IntervalFourier.period, |base.Hx q x| ≤ 1)
    (hAtail : ∀ q ∈ Ioo 0 T, (∫ x in 0..IntervalFourier.period,
      (base.Hx q x-IntervalFourier.projection N (base.Hx q) x)^2)/IntervalFourier.period ≤ A^2)
    (hBtail : ∀ q ∈ Ioo 0 T, (∫ x in 0..IntervalFourier.period,
      (base.E q x-IntervalFourier.projection N (base.E q) x)^2)/IntervalFourier.period ≤ B^2)
    (ht : t ∈ Icc 0 T) :
    normalizedRelative base N (projectedInitial N D H) t ≤ Real.exp (4*t)*
      (‖RealGalerkin.projection N (toL2 D)-toL2 D‖^2/2 +
       ‖RealGalerkin.projection N (toL2 H)-toL2 H‖^2/2 + t*(A^2/2+A*B)) := by
  let R := normalizedRelative base N (projectedInitial N D H)
  have hd : ∀ q ∈ Ioo 0 T, HasDerivAt R (deriv R q) q := by
    intro q hq
    have hs : Ioo 0 T ∈ 𝓝 q := isOpen_Ioo.mem_nhds hq
    have he := (withGalerkin base N (projectedInitial N D H)).energy_hasDerivAt
      q hs bound hb hbound
    exact (he.div_const (IntervalFourier.period-0)).differentiableAt.hasDerivAt
  have hineq : ∀ q ∈ Ioo 0 T, deriv R q ≤ 4*R q+(A^2/2+A*B) := by
    intro q hq
    have hs : Ioo 0 T ∈ 𝓝 q := isOpen_Ioo.mem_nhds hq
    have he := actual_galerkin_relative_rate base N (projectedInitial N D H) q 1 A B
      hs (by norm_num) hA hB bound hb hbound (hHx q hq) (hAtail q hq) (hBtail q hq)
    dsimp only [R, normalizedRelative]
    nlinarith
  exact InteriorGronwall.energy_envelope R (deriv R) _ _ T t (by positivity) hc hd
    (normalized_initial_energy_le base N D H hD hH) hineq ht

def cutoffDecay (N : ℕ) : ℝ := Real.exp (-(3/20 : ℝ)*((N : ℝ)+1))

theorem cutoffDecay_pos (N : ℕ) : 0 < cutoffDecay N := Real.exp_pos _

theorem cutoffDecay_le_one (N : ℕ) : cutoffDecay N ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  have hn := Nat.cast_nonneg (α := ℝ) N
  nlinarith

theorem initial_norm_tail_budget (N : ℕ) (d h : ℝ) (hd : 0 ≤ d) (hh : 0 ≤ h)
    (hdTail : d ≤ (10/7 : ℝ)*(57/250)*Real.exp (-((N : ℝ)+1)/2))
    (hhTail : h ≤ (57/250 : ℝ)*Real.exp (-((N : ℝ)+1)/2)) :
    d^2/2+h^2/2 ≤ (2/25 : ℝ)*(cutoffDecay N)^2 := by
  have hb : d^2/2+h^2/2 ≤
      ((10/7 : ℝ)*(57/250)*Real.exp (-((N : ℝ)+1)/2))^2/2 +
      ((57/250 : ℝ)*Real.exp (-((N : ℝ)+1)/2))^2/2 := by gcongr
  have he : (Real.exp (-((N : ℝ)+1)/2))^2 = Real.exp (-((N : ℝ)+1)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hid : ((10/7 : ℝ)*(57/250)*Real.exp (-((N : ℝ)+1)/2))^2/2 +
      ((57/250 : ℝ)*Real.exp (-((N : ℝ)+1)/2))^2/2 =
      (149/98 : ℝ)*(57/250)^2*Real.exp (-((N : ℝ)+1)) := by
    calc
      _ = (149/98 : ℝ)*(57/250)^2*(Real.exp (-((N : ℝ)+1)/2))^2 := by ring
      _ = _ := by rw [he]
  rw [hid] at hb
  exact hb.trans (InteriorGronwall.initial_tail_budget N)

/-- The complete spatial error estimate uses the actual initial encoding, PDE, projection, and decoder. -/
theorem actual_spatial_error_le (T : ℝ) (hT : T ≤ 1/5)
    (base : ContinuumRelative.ClassicalKerrPair 0 IntervalFourier.period (Ioo 0 T))
    (N : ℕ) (D H Efinal Hfinal : C(Circle, ℝ)) (t : ℝ)
    (hD : ∀ x, Riccati.constitutive (base.E 0 x)=realLift D x) (hH : base.H 0=realLift H)
    (hEt : base.E t=realLift Efinal) (hHt : base.H t=realLift Hfinal)
    (hc : ContinuousOn (normalizedRelative base N (projectedInitial N D H)) (Icc 0 T))
    (bound : ℝ → ℝ) (hb : IntervalIntegrable bound volume 0 IntervalFourier.period)
    (hbound : ∀ x ∈ uIcc 0 IntervalFourier.period, ∀ q ∈ Ioo 0 T,
      |(withGalerkin base N (projectedInitial N D H)).rate q x| ≤ bound x)
    (hHx : ∀ q ∈ Ioo 0 T, ∀ x ∈ Icc 0 IntervalFourier.period, |base.Hx q x| ≤ 1)
    (hAtail : ∀ q ∈ Ioo 0 T, (∫ x in 0..IntervalFourier.period,
      (base.Hx q x-IntervalFourier.projection N (base.Hx q) x)^2)/IntervalFourier.period ≤
        (2*cutoffDecay N)^2)
    (hBtail : ∀ q ∈ Ioo 0 T, (∫ x in 0..IntervalFourier.period,
      (base.E q x-IntervalFourier.projection N (base.E q) x)^2)/IntervalFourier.period ≤
        ((cutoffDecay N)^2/5)^2)
    (hdTail : ‖RealGalerkin.projection N (toL2 D)-toL2 D‖ ≤
      (10/7 : ℝ)*(57/250)*Real.exp (-((N : ℝ)+1)/2))
    (hhTail : ‖RealGalerkin.projection N (toL2 H)-toL2 H‖ ≤
      (57/250 : ℝ)*Real.exp (-((N : ℝ)+1)/2))
    (ht : t ∈ Icc 0 T) :
    ‖GalerkinFlow.decode N (GalerkinFlow.flow N t (projectedInitial N D H)) -
      WithLp.toLp 2 (toL2 Efinal,toL2 Hfinal)‖ ≤ 2*cutoffDecay N := by
  have hq := (cutoffDecay_pos N).le
  have he := actual_energy_envelope T base N D H (2*cutoffDecay N)
    ((cutoffDecay N)^2/5) t (by positivity) (by positivity) hD hH hc bound hb hbound
    hHx hAtail hBtail ht
  have hz := initial_norm_tail_budget N _ _ (norm_nonneg _) (norm_nonneg _) hdTail hhTail
  have hs := StoppingCertificate.tail_source_budget (cutoffDecay N) (2*cutoffDecay N)
    ((cutoffDecay N)^2/5) hq (cutoffDecay_le_one N) (by positivity) (by positivity) le_rfl le_rfl
  have henvelope : normalizedRelative base N (projectedInitial N D H) t ≤
      Real.exp (4*t)*((2/25 : ℝ)+t*(12/5))*(cutoffDecay N)^2 := by
    apply he.trans
    have htime := mul_le_mul_of_nonneg_left hs ht.1
    have hsum := add_le_add hz htime
    have hmul := mul_le_mul_of_nonneg_left hsum (Real.exp_nonneg (4*t))
    convert hmul using 1
    ring
  exact InteriorGronwall.short_time_restored_budget _ _ (cutoffDecay N) t hq ht.1 (ht.2.trans hT)
    (decoded_error_sq_le_relative base N (projectedInitial N D H) t Efinal Hfinal hEt hHt) henvelope

end
end KerrKoopman.GalerkinClassical
