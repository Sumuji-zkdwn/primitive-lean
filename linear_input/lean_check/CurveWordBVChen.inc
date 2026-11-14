/-!
Chen multiplication for every degree of the actual continuous-BV Stieltjes
signature. The proof uses interval splitting and integral linearity.
-/

noncomputable section

namespace LinearInputCurveWordBVChen

open Real Set MeasureTheory
open LinearInputCurveWordStieltjes LinearInputCurveWordBVSignature

theorem stieltjesIntegral_add_adjacent (p m : StieltjesFunction ℝ)
    {F : ℝ → ℝ} (hF : Continuous F) (a b c : ℝ) :
    stieltjesIntegral p m a b F + stieltjesIntegral p m b c F =
      stieltjesIntegral p m a c F := by
  have hp := intervalIntegral.integral_add_adjacent_intervals (μ := p.measure)
    (hF.intervalIntegrable a b) (hF.intervalIntegrable b c)
  have hm := intervalIntegral.integral_add_adjacent_intervals (μ := m.measure)
    (hF.intervalIntegrable a b) (hF.intervalIntegrable b c)
  unfold stieltjesIntegral
  linarith

theorem stieltjesIntegral_mul_const (p m : StieltjesFunction ℝ)
    (F : ℝ → ℝ) (r a b : ℝ) :
    stieltjesIntegral p m a b (fun t => F t * r) = stieltjesIntegral p m a b F * r := by
  unfold stieltjesIntegral
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]
  ring

theorem stieltjesIntegral_finset_sum {κ : Type*} (p m : StieltjesFunction ℝ)
    (s : Finset κ) (F : κ → ℝ → ℝ) (hF : ∀ k ∈ s, Continuous (F k)) (a b : ℝ) :
    stieltjesIntegral p m a b (fun t => ∑ k ∈ s, F k t) =
      ∑ k ∈ s, stieltjesIntegral p m a b (F k) := by
  unfold stieltjesIntegral
  rw [intervalIntegral.integral_finsetSum (fun k hk => (hF k hk).intervalIntegrable a b),
    intervalIntegral.integral_finsetSum (fun k hk => (hF k hk).intervalIntegrable a b),
    Finset.sum_sub_distrib]

theorem reverseStieltjes_split {ι : Type*} (p m : ι → StieltjesFunction ℝ)
    (hp : ∀ i, Continuous (p i : ℝ → ℝ)) (hm : ∀ i, Continuous (m i : ℝ → ℝ))
    (a b c : ℝ) (w : List ι) :
    reverseStieltjes p m a w c =
      ∑ k ∈ Finset.range (w.length + 1),
        reverseStieltjes p m b (w.take k) c * reverseStieltjes p m a (w.drop k) b := by
  induction w generalizing c with
  | nil => simp [reverseStieltjes]
  | cons i w ih =>
    have hs := stieltjesIntegral_add_adjacent (p i) (m i)
      (reverseStieltjes_continuous p m hp hm a w) a b c
    have he : reverseStieltjes p m a w = fun t =>
        ∑ k ∈ Finset.range (w.length + 1),
          reverseStieltjes p m b (w.take k) t * reverseStieltjes p m a (w.drop k) b :=
      funext ih
    have hrest : stieltjesIntegral (p i) (m i) b c (reverseStieltjes p m a w) =
        ∑ k ∈ Finset.range (w.length + 1),
          reverseStieltjes p m b (i :: w.take k) c *
            reverseStieltjes p m a (w.drop k) b := by
      rw [he, stieltjesIntegral_finset_sum]
      · apply Finset.sum_congr rfl
        intro k _
        rw [stieltjesIntegral_mul_const]
        rfl
      · intro k _
        exact (reverseStieltjes_continuous p m hp hm b (w.take k)).mul continuous_const
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.take_succ_cons, List.drop_succ_cons, List.take_zero,
      List.drop_zero, reverseStieltjes, one_mul]
    simp only [reverseStieltjes] at hrest
    rw [← hs, hrest]
    ring

/-- All-degree Chen identity in chronological word order for continuous
Stieltjes pairs, including canonical pairs of continuous BV coordinates. -/
theorem stieltjesSignature_chen {ι : Type*} (p m : ι → StieltjesFunction ℝ)
    (hp : ∀ i, Continuous (p i : ℝ → ℝ)) (hm : ∀ i, Continuous (m i : ℝ → ℝ))
    (a b c : ℝ) (w : List ι) :
    stieltjesSignature p m a c w =
      ∑ k ∈ Finset.range (w.length + 1),
        stieltjesSignature p m a b (w.take k) * stieltjesSignature p m b c (w.drop k) := by
  rw [stieltjesSignature, reverseStieltjes_split p m hp hm a b c w.reverse]
  simp only [List.length_reverse]
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ w.length := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  simp only [Nat.add_sub_cancel, List.take_reverse, List.drop_reverse,
    Nat.sub_sub_self hk', stieltjesSignature]
  ring

end LinearInputCurveWordBVChen
