/-!
Fubini integration-by-parts for continuous Stieltjes signatures.
The diagonal has zero mass, so the two ordered integration triangles partition
the product integral without a jump correction.
-/

noncomputable section

namespace LinearInputCurveWordBVShuffle

open Real Set MeasureTheory Filter
open scoped Topology
open LinearInputCurveWordStieltjes LinearInputCurveWordBVSignature

theorem integral_triangle_product (μ ν : Measure ℝ) [SFinite μ] [SFinite ν] [NullSingletonClass μ]
    {F G : ℝ → ℝ} (hF : Integrable F μ) (hG : Integrable G ν) :
    (∫ x, F x ∂μ) * (∫ y, G y ∂ν) =
      (∫ x, F x * (∫ y in Iic x, G y ∂ν) ∂μ) +
        ∫ y, (∫ x in Iic y, F x ∂μ) * G y ∂ν := by
  let L : ℝ × ℝ → ℝ := {z | z.2 ≤ z.1}.indicator (fun z => F z.1 * G z.2)
  let U : ℝ × ℝ → ℝ := {z | z.1 < z.2}.indicator (fun z => F z.1 * G z.2)
  have hL : Integrable L (μ.prod ν) :=
    (hF.mul_prod hG).indicator (measurableSet_le measurable_snd measurable_fst)
  have hU : Integrable U (μ.prod ν) :=
    (hF.mul_prod hG).indicator (measurableSet_lt measurable_fst measurable_snd)
  have hpart (x y : ℝ) : L (x, y) + U (x, y) = F x * G y := by
    by_cases hxy : y ≤ x
    · simp [L, U, hxy, not_lt.mpr hxy]
    · simp [L, U, hxy, lt_of_not_ge hxy]
  have hLi (x : ℝ) : (∫ y, L (x, y) ∂ν) = F x * (∫ y in Iic x, G y ∂ν) := by
    change (∫ y, (Iic x).indicator (fun y => F x * G y) y ∂ν) = _
    rw [integral_indicator measurableSet_Iic, integral_const_mul]
  have hUi (y : ℝ) : (∫ x, U (x, y) ∂μ) = (∫ x in Iic y, F x ∂μ) * G y := by
    change (∫ x, (Iio y).indicator (fun x => F x * G y) x ∂μ) = _
    rw [integral_indicator measurableSet_Iio, ← integral_Iic_eq_integral_Iio, integral_mul_const]
  have hswap : (∫ x, ∫ y, U (x, y) ∂ν ∂μ) = ∫ y, ∫ x, U (x, y) ∂μ ∂ν :=
    integral_integral_swap hU
  have hsum := integral_integral_add hL hU
  simp_rw [hpart, hLi] at hsum
  rw [hswap] at hsum
  simp_rw [hUi, integral_const_mul] at hsum
  rw [integral_mul_const] at hsum
  exact hsum

theorem integral_restrict_Iic (μ : Measure ℝ) (F : ℝ → ℝ) {a b t : ℝ}
    (ht : t ∈ Icc a b) :
    (∫ s in Iic t, F s ∂μ.restrict (Ioc a b)) = ∫ s in a..t, F s ∂μ := by
  have he : Iic t ∩ Ioc a b = Ioc a t := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioc]
    constructor
    · intro hs
      exact ⟨hs.2.1, hs.1⟩
    · intro hs
      exact ⟨hs.2, hs.1, hs.2.trans ht.2⟩
  rw [Measure.restrict_restrict measurableSet_Iic, he, intervalIntegral.integral_of_le ht.1]

theorem intervalIntegral_triangle_product (μ ν : Measure ℝ)
    [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] [NullSingletonClass μ]
    {F G : ℝ → ℝ} (hF : Continuous F) (hG : Continuous G) {a b : ℝ} (hab : a ≤ b) :
    (∫ x in a..b, F x ∂μ) * (∫ y in a..b, G y ∂ν) =
      (∫ x in a..b, F x * (∫ y in a..x, G y ∂ν) ∂μ) +
        ∫ y in a..b, (∫ x in a..y, F x ∂μ) * G y ∂ν := by
  have h := integral_triangle_product (μ.restrict (Ioc a b)) (ν.restrict (Ioc a b))
    (hF.intervalIntegrable a b).1 (hG.intervalIntegrable a b).1
  simp only [intervalIntegral.integral_of_le hab]
  rw [h]
  congr 1
  · apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [integral_restrict_Iic ν G ⟨ht.1.le, ht.2⟩]
  · apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [integral_restrict_Iic μ F ⟨ht.1.le, ht.2⟩]

theorem stieltjes_integration_by_parts (p m q n : StieltjesFunction ℝ)
    (hp : Continuous (p : ℝ → ℝ)) (hm : Continuous (m : ℝ → ℝ))
    (hq : Continuous (q : ℝ → ℝ)) (hn : Continuous (n : ℝ → ℝ))
    {F G : ℝ → ℝ} (hF : Continuous F) (hG : Continuous G) {a b : ℝ} (hab : a ≤ b) :
    stieltjesIntegral p m a b F * stieltjesIntegral q n a b G =
      stieltjesIntegral p m a b (fun t => F t * stieltjesIntegral q n a t G) +
        stieltjesIntegral q n a b (fun t => stieltjesIntegral p m a t F * G t) := by
  let : NullSingletonClass p.measure := continuous_stieltjes_noAtoms p hp
  let : NullSingletonClass m.measure := continuous_stieltjes_noAtoms m hm
  have hPQ := intervalIntegral_triangle_product p.measure q.measure hF hG hab
  have hPN := intervalIntegral_triangle_product p.measure n.measure hF hG hab
  have hMQ := intervalIntegral_triangle_product m.measure q.measure hF hG hab
  have hMN := intervalIntegral_triangle_product m.measure n.measure hF hG hab
  have hIp := primitive_stieltjes_continuous p hp hF a
  have hIm := primitive_stieltjes_continuous m hm hF a
  have hIq := primitive_stieltjes_continuous q hq hG a
  have hIn := primitive_stieltjes_continuous n hn hG a
  have hFp : Continuous (fun t => F t * (∫ s in a..t, G s ∂q.measure)) := hF.mul hIq
  have hFm : Continuous (fun t => F t * (∫ s in a..t, G s ∂n.measure)) := hF.mul hIn
  have hpG : Continuous (fun t => (∫ s in a..t, F s ∂p.measure) * G t) := hIp.mul hG
  have hmG : Continuous (fun t => (∫ s in a..t, F s ∂m.measure) * G t) := hIm.mul hG
  unfold stieltjesIntegral
  simp only [mul_sub, sub_mul]
  rw [intervalIntegral.integral_sub (hFp.intervalIntegrable a b) (hFm.intervalIntegrable a b),
    intervalIntegral.integral_sub (hFp.intervalIntegrable a b) (hFm.intervalIntegrable a b),
    intervalIntegral.integral_sub (hpG.intervalIntegrable a b) (hmG.intervalIntegrable a b),
    intervalIntegral.integral_sub (hpG.intervalIntegrable a b) (hmG.intervalIntegrable a b)]
  linarith

open LinearInputCurveWordChen

theorem stieltjesIntegral_congr (p m : StieltjesFunction ℝ) {a b : ℝ} {F G : ℝ → ℝ}
    (h : EqOn F G (uIcc a b)) : stieltjesIntegral p m a b F = stieltjesIntegral p m a b G := by
  unfold stieltjesIntegral
  rw [intervalIntegral.integral_congr h, intervalIntegral.integral_congr h]

theorem stieltjesIntegral_add (p m : StieltjesFunction ℝ) {F G : ℝ → ℝ}
    (hF : Continuous F) (hG : Continuous G) (a b : ℝ) :
    stieltjesIntegral p m a b (fun t => F t + G t) =
      stieltjesIntegral p m a b F + stieltjesIntegral p m a b G := by
  unfold stieltjesIntegral
  rw [intervalIntegral.integral_add (hF.intervalIntegrable a b) (hG.intervalIntegrable a b),
    intervalIntegral.integral_add (hF.intervalIntegrable a b) (hG.intervalIntegrable a b)]
  ring

theorem stieltjesIntegral_list_sum {κ : Type*} (p m : StieltjesFunction ℝ)
    (l : List κ) (F : κ → ℝ → ℝ) (hF : ∀ k, Continuous (F k)) (a b : ℝ) :
    stieltjesIntegral p m a b (fun t => (l.map (fun k => F k t)).sum) =
      (l.map (fun k => stieltjesIntegral p m a b (F k))).sum := by
  induction l with
  | nil => simp [stieltjesIntegral]
  | cons k l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [stieltjesIntegral_add p m (hF k) (continuous_list_sum l F hF), ih]

theorem sum_reverseStieltjes_cons {ι : Type*} (p m : ι → StieltjesFunction ℝ)
    (hp : ∀ i, Continuous (p i : ℝ → ℝ)) (hm : ∀ i, Continuous (m i : ℝ → ℝ))
    (a b : ℝ) (i : ι) (ws : List (List ι)) :
    (ws.map (fun w => reverseStieltjes p m a (i :: w) b)).sum =
      stieltjesIntegral (p i) (m i) a b (fun t => (ws.map (fun w => reverseStieltjes p m a w t)).sum) := by
  rw [stieltjesIntegral_list_sum (p i) (m i) ws (fun w => reverseStieltjes p m a w)
    (reverseStieltjes_continuous p m hp hm a)]
  rfl

theorem reverseStieltjes_shuffle {ι : Type*} (p m : ι → StieltjesFunction ℝ)
    (hp : ∀ i, Continuous (p i : ℝ → ℝ)) (hm : ∀ i, Continuous (m i : ℝ → ℝ))
    (a b : ℝ) (hab : a ≤ b) (u w : List ι) :
    reverseStieltjes p m a u b * reverseStieltjes p m a w b =
      ((shuffles u w).map (fun z => reverseStieltjes p m a z b)).sum := by
  cases u with
  | nil => simp [shuffles, reverseStieltjes]
  | cons i u =>
    cases w with
    | nil => simp [shuffles_nil_right, reverseStieltjes]
    | cons j w =>
      have hparts := stieltjes_integration_by_parts (p i) (m i) (p j) (m j)
        (hp i) (hm i) (hp j) (hm j)
        (reverseStieltjes_continuous p m hp hm a u) (reverseStieltjes_continuous p m hp hm a w) hab
      change reverseStieltjes p m a (i :: u) b * reverseStieltjes p m a (j :: w) b =
        stieltjesIntegral (p i) (m i) a b
          (fun t => reverseStieltjes p m a u t * reverseStieltjes p m a (j :: w) t) +
        stieltjesIntegral (p j) (m j) a b
          (fun t => reverseStieltjes p m a (i :: u) t * reverseStieltjes p m a w t) at hparts
      rw [shuffles, List.map_append, List.sum_append]
      simp only [List.map_map, Function.comp_def]
      rw [sum_reverseStieltjes_cons p m hp hm, sum_reverseStieltjes_cons p m hp hm]
      rw [hparts]
      congr 1
      · apply stieltjesIntegral_congr
        intro t ht
        rw [uIcc_of_le hab] at ht
        exact reverseStieltjes_shuffle p m hp hm a t ht.1 u (j :: w)
      · apply stieltjesIntegral_congr
        intro t ht
        rw [uIcc_of_le hab] at ht
        exact reverseStieltjes_shuffle p m hp hm a t ht.1 (i :: u) w
termination_by u.length + w.length

/-- The all-degree shuffle identity for genuine continuous-BV Stieltjes
signatures, in chronological order and with interleaving multiplicity. -/
theorem stieltjesSignature_shuffle {ι : Type*} (p m : ι → StieltjesFunction ℝ)
    (hp : ∀ i, Continuous (p i : ℝ → ℝ)) (hm : ∀ i, Continuous (m i : ℝ → ℝ))
    (a b : ℝ) (hab : a ≤ b) (u w : List ι) :
    stieltjesSignature p m a b u * stieltjesSignature p m a b w =
      ((chronologicalShuffles u w).map (stieltjesSignature p m a b)).sum := by
  simpa only [stieltjesSignature, chronologicalShuffles, List.map_map, Function.comp_def,
    List.reverse_reverse] using reverseStieltjes_shuffle p m hp hm a b hab u.reverse w.reverse

end LinearInputCurveWordBVShuffle
