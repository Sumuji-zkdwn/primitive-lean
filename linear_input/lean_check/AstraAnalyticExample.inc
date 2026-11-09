
/-! The tested mixed sinusoidal input is an actual instance of the common PDE construction. -/

namespace KerrKoopman.AnalyticExample

noncomputable section
set_option backward.isDefEq.respectTransparency false
open AnalyticFields AnalyticInitial AnalyticLift AnalyticPDE
open ExplicitAnalyticInput Phase3WeightedDerivative

def data (T : ℝ) (hT0 : 0 ≤ T) (hT1 : T ≤ 1 / 5) : Data where
  T := T
  time_nonneg := hT0
  time_le := hT1
  initial := ExplicitAnalyticInput.initial
  initial_bound := initial_norm_le
  initial_real := initial_hermitian

theorem branch_two_modes (T : ℝ) (hT0 : 0 ≤ T) (hT1 : T ≤ 1 / 5) (b : Bool) (x : ℝ) :
    initialBranch (data T hT0 hT1) b x =
      (modeValue (1 / 2) 1 (component b weightedPositive) x +
        modeValue (1 / 2) (-1) (component b (star weightedPositive)) x).re := by
  unfold initialBranch
  congr 1
  have hs : (∑' k : ℤ, modeValue (1 / 2) k (component b ((data T hT0 hT1).initial k)) x) =
      ∑ k ∈ ({1, -1} : Finset ℤ),
        modeValue (1 / 2) k (component b ((data T hT0 hT1).initial k)) x := by
    apply tsum_eq_sum
    intro k hk
    have hp : k ≠ 1 := by simpa using (show k ≠ 1 from fun h => hk (by simp [h]))
    have hn : k ≠ -1 := by simpa using (show k ≠ -1 from fun h => hk (by simp [h]))
    simp [data, ExplicitAnalyticInput.initial, Pi.add_apply, lp.single_apply, hp, hn, modeValue]
  rw [hs]
  simp [data, ExplicitAnalyticInput.initial, Pi.add_apply, lp.single_apply]

theorem conjugate_pair_value (a : ℂ) (x : ℝ) :
    (modeValue (1 / 2) 1 ((Real.exp (1 / 2) : ℝ) • a) x +
      modeValue (1 / 2) (-1) (star ((Real.exp (1 / 2) : ℝ) • a)) x).re =
      2 * (a.re * Real.cos x - a.im * Real.sin x) := by
  have he : Real.exp (-(1 / 2 : ℝ)) * Real.exp (1 / 2) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hm : modeValue (1 / 2) 1 ((Real.exp (1 / 2) : ℝ) • a) x =
      Complex.exp ((x : ℂ) * Complex.I) * a := by
    unfold modeValue
    norm_num only [Int.cast_one, abs_one, mul_one, one_mul, Complex.real_smul]
    rw [Complex.exp_add, ← Complex.ofReal_exp]
    have hec : (Real.exp (-(1 / 2 : ℝ)) : ℂ) * (Real.exp (1 / 2) : ℂ) = 1 := by
      exact_mod_cast he
    calc
      _ = ((Real.exp (-(1 / 2 : ℝ)) : ℂ) * (Real.exp (1 / 2) : ℂ)) *
        (Complex.exp ((x : ℂ) * Complex.I) * a) := by ring
      _ = _ := by rw [hec, one_mul]
  rw [show modeValue (1 / 2) (-1) (star ((Real.exp (1 / 2) : ℝ) • a)) x =
      star (modeValue (1 / 2) 1 ((Real.exp (1 / 2) : ℝ) • a) x) from
    Phase3WeightedRealDecode.modeValue_neg_star (1 / 2) 1 _ x, hm]
  have hr : (Complex.exp ((x : ℂ) * Complex.I)).re = Real.cos x := by
    simp [Complex.exp_re]
  have hi : (Complex.exp ((x : ℂ) * Complex.I)).im = Real.sin x := by
    simp [Complex.exp_im]
  simp only [Complex.add_re, Complex.star_def, Complex.conj_re, Complex.mul_re, hr, hi]
  ring

theorem initialBranch_true (T : ℝ) (hT0 : 0 ≤ T) (hT1 : T ≤ 1 / 5) (x : ℝ) :
    initialBranch (data T hT0 hT1) true x = (3 / 100) * Real.sin x + c / 25 * Real.cos x := by
  rw [branch_two_modes]
  change (modeValue (1 / 2) 1 ((Real.exp (1 / 2) : ℝ) • positive.1) x +
    modeValue (1 / 2) (-1) (star ((Real.exp (1 / 2) : ℝ) • positive.1)) x).re = _
  rw [conjugate_pair_value]
  norm_num [positive, Complex.div_re, Complex.div_im]
  ring

theorem initialBranch_false (T : ℝ) (hT0 : 0 ≤ T) (hT1 : T ≤ 1 / 5) (x : ℝ) :
    initialBranch (data T hT0 hT1) false x = (3 / 100) * Real.sin x - c / 25 * Real.cos x := by
  rw [branch_two_modes]
  change (modeValue (1 / 2) 1 ((Real.exp (1 / 2) : ℝ) • positive.2) x +
    modeValue (1 / 2) (-1) (star ((Real.exp (1 / 2) : ℝ) • positive.2)) x).re = _
  rw [conjugate_pair_value]
  norm_num [positive, Complex.div_re, Complex.div_im]
  ring

theorem displacement_initial_wave (T : ℝ) (hT0 : 0 ≤ T) (hT1 : T ≤ 1 / 5) (x : ℝ) :
    displacementField (data T hT0 hT1) (zeroTime _) x = 4 / 3 + (1 / 25) * Real.cos x := by
  rw [displacement_initial]
  unfold initialDisplacement
  rw [initialBranch_true, initialBranch_false]
  have hc : c ^ 2 = 1 / 2 := speed_sq
  change 4 / 3 + c * ((3 / 100) * Real.sin x + c / 25 * Real.cos x -
    ((3 / 100) * Real.sin x - c / 25 * Real.cos x)) = _
  linear_combination (2 / 25 * Real.cos x) * hc

theorem magnetic_initial_wave (T : ℝ) (hT0 : 0 ≤ T) (hT1 : T ≤ 1 / 5) (x : ℝ) :
    magnetic (data T hT0 hT1) (zeroTime _) x = 3 / 10 + (3 / 100) * Real.sin x := by
  rw [magnetic_initial]
  unfold initialMagnetic
  rw [initialBranch_true, initialBranch_false]
  ring

end
end KerrKoopman.AnalyticExample
