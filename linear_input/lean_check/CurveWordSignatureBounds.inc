/-!
Quantitative bounds for actual BV Stieltjes signatures. A common continuous
positive Stieltjes control dominates coordinate variation measures; its
iterated integrals give the factorial degree bound.
-/

noncomputable section

namespace LinearInputCurveWordSignatureBounds

open Real Set MeasureTheory Filter
open scoped Topology
open LinearInputCurveWordStieltjes LinearInputCurveWordBVSignature
open LinearInputCurveWordBVShuffle LinearInputCurveWordChen

def positiveIterate (v : StieltjesFunction ℝ) (a : ℝ) (n : ℕ) (b : ℝ) : ℝ :=
  reverseStieltjes (fun _ : Unit => v) (fun _ => 0) a (List.replicate n ()) b

theorem positiveIterate_zero (v : StieltjesFunction ℝ) (a b : ℝ) : positiveIterate v a 0 b = 1 := rfl

theorem positiveIterate_succ (v : StieltjesFunction ℝ) (a b : ℝ) (n : ℕ) :
    positiveIterate v a (n + 1) b = ∫ t in a..b, positiveIterate v a n t ∂v.measure := by
  simp [positiveIterate, List.replicate_succ, reverseStieltjes, stieltjesIntegral, intervalIntegral]

theorem positiveIterate_continuous (v : StieltjesFunction ℝ) (hv : Continuous (v : ℝ → ℝ))
    (a : ℝ) (n : ℕ) : Continuous (positiveIterate v a n) :=
  reverseStieltjes_continuous _ _ (fun _ => hv) (fun _ => continuous_const) a _

theorem positiveIterate_one (v : StieltjesFunction ℝ) {a b : ℝ} (hab : a ≤ b) :
    positiveIterate v a 1 b = v b - v a := by
  rw [positiveIterate_succ]
  simp only [positiveIterate_zero, intervalIntegral.integral_of_le hab, integral_const,
    smul_eq_mul, mul_one, measureReal_def, Measure.restrict_apply_univ,
    StieltjesFunction.measure_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr (v.mono hab))]

theorem shuffles_replicate_singleton {ι : Type*} (i : ι) (n : ℕ) :
    shuffles [i] (List.replicate n i) = List.replicate (n + 1) (List.replicate (n + 1) i) := by
  induction n with
  | zero => simp [shuffles_nil_right]
  | succ n ih =>
    rw [List.replicate_succ, shuffles, shuffles, ih]
    simp only [List.map_singleton, List.map_replicate, List.singleton_append]
    rfl

theorem positiveIterate_recurrence (v : StieltjesFunction ℝ) (hv : Continuous (v : ℝ → ℝ))
    {a b : ℝ} (hab : a ≤ b) (n : ℕ) :
    (v b - v a) * positiveIterate v a n b = (n + 1 : ℕ) * positiveIterate v a (n + 1) b := by
  have hs := reverseStieltjes_shuffle (fun _ : Unit => v) (fun _ => 0)
    (fun _ => hv) (fun _ => continuous_const) a b hab [()] (List.replicate n ())
  rw [shuffles_replicate_singleton] at hs
  simp only [List.map_replicate, List.sum_replicate, nsmul_eq_mul] at hs
  change positiveIterate v a 1 b * positiveIterate v a n b =
    (n + 1 : ℕ) * positiveIterate v a (n + 1) b at hs
  rw [positiveIterate_one v hab] at hs
  exact hs

theorem positiveIterate_divided_power (v : StieltjesFunction ℝ) (hv : Continuous (v : ℝ → ℝ))
    {a b : ℝ} (hab : a ≤ b) (n : ℕ) :
    positiveIterate v a n b = (v b - v a) ^ n / (n.factorial : ℝ) := by
  induction n with
  | zero => simp [positiveIterate_zero]
  | succ n ih =>
    have hs := positiveIterate_recurrence v hv hab n
    rw [ih] at hs
    have hn : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    have hnp : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
    field_simp at hs ⊢
    nlinarith

theorem positiveIterate_nonneg (v : StieltjesFunction ℝ) (hv : Continuous (v : ℝ → ℝ))
    {a b : ℝ} (hab : a ≤ b) (n : ℕ) : 0 ≤ positiveIterate v a n b := by
  rw [positiveIterate_divided_power v hv hab]
  exact div_nonneg (pow_nonneg (sub_nonneg.mpr (v.mono hab)) _) (Nat.cast_nonneg _)

theorem abs_stieltjesIntegral_le_control (p m v : StieltjesFunction ℝ)
    (hcontrol : p.measure + m.measure ≤ v.measure)
    {F B : ℝ → ℝ} (hF : Continuous F) (hB : Continuous B) {a b : ℝ} (hab : a ≤ b)
    (hbound : ∀ t ∈ Icc a b, |F t| ≤ B t) :
    |stieltjesIntegral p m a b F| ≤ ∫ t in a..b, B t ∂v.measure := by
  have hP : |∫ t in a..b, F t ∂p.measure| ≤ ∫ t in a..b, |F t| ∂p.measure := by
    simpa only [Real.norm_eq_abs] using
      (intervalIntegral.norm_integral_le_integral_norm (f := F) (μ := p.measure) hab)
  have hM : |∫ t in a..b, F t ∂m.measure| ≤ ∫ t in a..b, |F t| ∂m.measure := by
    simpa only [Real.norm_eq_abs] using
      (intervalIntegral.norm_integral_le_integral_norm (f := F) (μ := m.measure) hab)
  have hPB := intervalIntegral.integral_mono_on (μ := p.measure) hab
    (hF.abs.intervalIntegrable a b) (hB.intervalIntegrable a b) hbound
  have hMB := intervalIntegral.integral_mono_on (μ := m.measure) hab
    (hF.abs.intervalIntegrable a b) (hB.intervalIntegrable a b) hbound
  calc
    _ ≤ |∫ t in a..b, F t ∂p.measure| + |∫ t in a..b, F t ∂m.measure| := abs_sub _ _
    _ ≤ (∫ t in a..b, B t ∂p.measure) + ∫ t in a..b, B t ∂m.measure :=
      add_le_add (hP.trans hPB) (hM.trans hMB)
    _ = ∫ t in a..b, B t ∂(p.measure + m.measure) :=
      (intervalIntegral_add_measure p.measure m.measure a b
        (hB.intervalIntegrable a b) (hB.intervalIntegrable a b)).symm
    _ ≤ _ := by
      rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
      apply integral_mono_measure (Measure.restrict_mono_measure hcontrol (Ioc a b))
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact (abs_nonneg _).trans (hbound t ⟨ht.1.le, ht.2⟩)
      · exact (hB.intervalIntegrable a b).1

theorem reverseStieltjes_le_positiveIterate {ι : Type*} (p m : ι → StieltjesFunction ℝ)
    (hp : ∀ i, Continuous (p i : ℝ → ℝ)) (hm : ∀ i, Continuous (m i : ℝ → ℝ))
    (v : StieltjesFunction ℝ) (hv : Continuous (v : ℝ → ℝ))
    (hcontrol : ∀ i, (p i).measure + (m i).measure ≤ v.measure)
    (a b : ℝ) (hab : a ≤ b) (w : List ι) :
    |reverseStieltjes p m a w b| ≤ positiveIterate v a w.length b := by
  induction w generalizing b with
  | nil => simp [reverseStieltjes, positiveIterate_zero]
  | cons i w ih =>
    rw [List.length_cons, positiveIterate_succ]
    exact abs_stieltjesIntegral_le_control (p i) (m i) v (hcontrol i)
      (reverseStieltjes_continuous p m hp hm a w) (positiveIterate_continuous v hv a w.length)
      hab (fun t ht => ih t ht.1)

/-- The factorial estimate is obtained from the actual integral recursion,
domination of variation measures, and the scalar shuffle divided-power law. -/
theorem signature_factorial_bound {ι : Type*} (p m : ι → StieltjesFunction ℝ)
    (hp : ∀ i, Continuous (p i : ℝ → ℝ)) (hm : ∀ i, Continuous (m i : ℝ → ℝ))
    (v : StieltjesFunction ℝ) (hv : Continuous (v : ℝ → ℝ))
    (hcontrol : ∀ i, (p i).measure + (m i).measure ≤ v.measure)
    (a b : ℝ) (hab : a ≤ b) (w : List ι) :
    |stieltjesSignature p m a b w| ≤ (v b - v a) ^ w.length / (w.length.factorial : ℝ) := by
  have h := reverseStieltjes_le_positiveIterate p m hp hm v hv hcontrol a b hab w.reverse
  rw [positiveIterate_divided_power v hv hab, List.length_reverse] at h
  exact h

theorem stieltjesIntegral_sub (p m : StieltjesFunction ℝ) {F G : ℝ → ℝ}
    (hF : Continuous F) (hG : Continuous G) (a b : ℝ) :
    stieltjesIntegral p m a b (fun t => F t - G t) =
      stieltjesIntegral p m a b F - stieltjesIntegral p m a b G := by
  unfold stieltjesIntegral
  rw [intervalIntegral.integral_sub (hF.intervalIntegrable a b) (hG.intervalIntegrable a b),
    intervalIntegral.integral_sub (hF.intervalIntegrable a b) (hG.intervalIntegrable a b)]
  ring

theorem differenceIntegral_eq (p m q n r s : StieltjesFunction ℝ)
    (hdiff : SameIncrements (p + n) (m + q) r s) {F : ℝ → ℝ} (hF : Continuous F) (a b : ℝ) :
    stieltjesIntegral p m a b F - stieltjesIntegral q n a b F = stieltjesIntegral r s a b F := by
  have he := stieltjesIntegral_independent hdiff hF a b
  unfold stieltjesIntegral at he ⊢
  rw [StieltjesFunction.measure_add, StieltjesFunction.measure_add,
    intervalIntegral_add_measure p.measure n.measure a b (hF.intervalIntegrable a b) (hF.intervalIntegrable a b),
    intervalIntegral_add_measure m.measure q.measure a b (hF.intervalIntegrable a b) (hF.intervalIntegrable a b)] at he
  linarith

theorem differenceIntegral_split (p m q n r s : StieltjesFunction ℝ)
    (hdiff : SameIncrements (p + n) (m + q) r s) {F G : ℝ → ℝ}
    (hF : Continuous F) (hG : Continuous G) (a b : ℝ) :
    stieltjesIntegral p m a b F - stieltjesIntegral q n a b G =
      stieltjesIntegral p m a b (fun t => F t - G t) + stieltjesIntegral r s a b G := by
  rw [stieltjesIntegral_sub p m hF hG,
    ← differenceIntegral_eq p m q n r s hdiff hG a b]
  ring

theorem abs_stieltjesIntegral_le_constant (p m v : StieltjesFunction ℝ)
    (hcontrol : p.measure + m.measure ≤ v.measure) {F : ℝ → ℝ} (hF : Continuous F)
    {a b C : ℝ} (hab : a ≤ b) (hbound : ∀ t ∈ Icc a b, |F t| ≤ C) :
    |stieltjesIntegral p m a b F| ≤ C * (v b - v a) := by
  have h := abs_stieltjesIntegral_le_control p m v hcontrol hF continuous_const hab hbound
  rw [intervalIntegral.integral_of_le hab, integral_const, measureReal_def,
    Measure.restrict_apply_univ, StieltjesFunction.measure_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (v.mono hab)), smul_eq_mul] at h
  simpa only [mul_comm] using h

theorem reverseStieltjes_power_bound {ι : Type*} (p m : ι → StieltjesFunction ℝ)
    (hp : ∀ i, Continuous (p i : ℝ → ℝ)) (hm : ∀ i, Continuous (m i : ℝ → ℝ))
    (v : StieltjesFunction ℝ) (hv : Continuous (v : ℝ → ℝ))
    (hcontrol : ∀ i, (p i).measure + (m i).measure ≤ v.measure)
    (a b M : ℝ) (hab : a ≤ b) (hM : v b - v a ≤ M) (w : List ι) :
    |reverseStieltjes p m a w b| ≤ M ^ w.length := by
  have h := reverseStieltjes_le_positiveIterate p m hp hm v hv hcontrol a b hab w
  rw [positiveIterate_divided_power v hv hab] at h
  have hV : 0 ≤ v b - v a := sub_nonneg.mpr (v.mono hab)
  have hfac : (1 : ℝ) ≤ (w.length.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos w.length
  exact h.trans ((div_le_self (pow_nonneg hV _) hfac).trans (pow_le_pow_left₀ hV hM _))

/-- A quantitative BV stability estimate. The pair `r,s` represents the
coordinate difference, and `d` dominates its variation. The constant is
deliberately nonoptimal; its linear dependence on the actual variation
increment `d b-d a` gives continuity in BV distance. -/
theorem reverseStieltjes_difference_bound {ι : Type*}
    (p m q n r s : ι → StieltjesFunction ℝ)
    (hp : ∀ i, Continuous (p i : ℝ → ℝ)) (hm : ∀ i, Continuous (m i : ℝ → ℝ))
    (hq : ∀ i, Continuous (q i : ℝ → ℝ)) (hn : ∀ i, Continuous (n i : ℝ → ℝ))
    (v : StieltjesFunction ℝ) (hv : Continuous (v : ℝ → ℝ)) (d : StieltjesFunction ℝ)
    (hcontrol : ∀ i, (p i).measure + (m i).measure ≤ v.measure)
    (hbase : ∀ i, (q i).measure + (n i).measure ≤ v.measure)
    (hdiff : ∀ i, SameIncrements (p i + n i) (m i + q i) (r i) (s i))
    (hdelta : ∀ i, (r i).measure + (s i).measure ≤ d.measure)
    (a b M : ℝ) (hab : a ≤ b) (hMone : 1 ≤ M) (hM : v b - v a ≤ M) (w : List ι) :
    ∀ t ∈ Icc a b, |reverseStieltjes p m a w t - reverseStieltjes q n a w t| ≤
      (w.length : ℝ) * (d b - d a) * M ^ w.length := by
  have hM0 : 0 ≤ M := zero_le_one.trans hMone
  have hD0 : 0 ≤ d b - d a := sub_nonneg.mpr (d.mono hab)
  induction w with
  | nil => intro t _; simp [reverseStieltjes]
  | cons i w ih =>
    intro t ht
    have hF := reverseStieltjes_continuous p m hp hm a w
    have hG := reverseStieltjes_continuous q n hq hn a w
    have hs := differenceIntegral_split (p i) (m i) (q i) (n i) (r i) (s i)
      (hdiff i) hF hG a t
    have h1 := abs_stieltjesIntegral_le_constant (p i) (m i) v (hcontrol i)
      (show Continuous (fun u => reverseStieltjes p m a w u - reverseStieltjes q n a w u) from hF.sub hG)
      ht.1 (fun u hu => ih u ⟨hu.1, hu.2.trans ht.2⟩)
    have hGbound : ∀ u ∈ Icc a t, |reverseStieltjes q n a w u| ≤ M ^ w.length := by
      intro u hu
      exact reverseStieltjes_power_bound q n hq hn v hv hbase a u M hu.1
        ((sub_le_sub_right (v.mono (hu.2.trans ht.2)) (v a)).trans hM) w
    have h2 := abs_stieltjesIntegral_le_constant (r i) (s i) d (hdelta i) hG ht.1 hGbound
    have hVt : v t - v a ≤ M := (sub_le_sub_right (v.mono ht.2) (v a)).trans hM
    have hDt : d t - d a ≤ d b - d a := sub_le_sub_right (d.mono ht.2) (d a)
    have hpow : M ^ w.length ≤ M ^ (w.length + 1) := by
      rw [pow_succ]
      exact le_mul_of_one_le_right (pow_nonneg hM0 _) hMone
    change |stieltjesIntegral (p i) (m i) a t _ - stieltjesIntegral (q i) (n i) a t _| ≤ _
    rw [hs]
    calc
      _ ≤ |stieltjesIntegral (p i) (m i) a t
          (fun u => reverseStieltjes p m a w u - reverseStieltjes q n a w u)| +
          |stieltjesIntegral (r i) (s i) a t (reverseStieltjes q n a w)| := abs_add_le _ _
      _ ≤ ((w.length : ℝ) * (d b - d a) * M ^ w.length) * (v t - v a) +
          M ^ w.length * (d t - d a) := add_le_add h1 h2
      _ ≤ ((w.length : ℝ) * (d b - d a) * M ^ w.length) * M +
          M ^ w.length * (d b - d a) :=
        add_le_add (mul_le_mul_of_nonneg_left hVt (by positivity))
          (mul_le_mul_of_nonneg_left hDt (pow_nonneg hM0 _))
      _ ≤ (w.length : ℝ) * (d b - d a) * M ^ (w.length + 1) +
          (d b - d a) * M ^ (w.length + 1) := by
        calc
          _ = (w.length : ℝ) * (d b - d a) * M ^ (w.length + 1) +
              (d b - d a) * M ^ w.length := by rw [pow_succ]; ring
          _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hpow hD0)
      _ = ((i :: w).length : ℝ) * (d b - d a) * M ^ (i :: w).length := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        ring

theorem signature_difference_bound {ι : Type*}
    (p m q n r s : ι → StieltjesFunction ℝ)
    (hp : ∀ i, Continuous (p i : ℝ → ℝ)) (hm : ∀ i, Continuous (m i : ℝ → ℝ))
    (hq : ∀ i, Continuous (q i : ℝ → ℝ)) (hn : ∀ i, Continuous (n i : ℝ → ℝ))
    (v : StieltjesFunction ℝ) (hv : Continuous (v : ℝ → ℝ)) (d : StieltjesFunction ℝ)
    (hcontrol : ∀ i, (p i).measure + (m i).measure ≤ v.measure)
    (hbase : ∀ i, (q i).measure + (n i).measure ≤ v.measure)
    (hdiff : ∀ i, SameIncrements (p i + n i) (m i + q i) (r i) (s i))
    (hdelta : ∀ i, (r i).measure + (s i).measure ≤ d.measure)
    (a b M : ℝ) (hab : a ≤ b) (hMone : 1 ≤ M) (hM : v b - v a ≤ M) (w : List ι) :
    |stieltjesSignature p m a b w - stieltjesSignature q n a b w| ≤
      (w.length : ℝ) * (d b - d a) * M ^ w.length := by
  simpa only [stieltjesSignature, List.length_reverse] using
    reverseStieltjes_difference_bound p m q n r s hp hm hq hn v hv d
      hcontrol hbase hdiff hdelta a b M hab hMone hM w.reverse b ⟨hab, le_rfl⟩

/-- BV convergence, with a uniform variation bound, implies coefficientwise
convergence of the entire Stieltjes signature. The dominating positive control
may vary with the index; uniform convergence of paths alone is not assumed to
imply this conclusion. -/
theorem signature_tendsto_of_variation_tendsto_zero {ι κ : Type*} {l : Filter κ}
    (p m r s : κ → ι → StieltjesFunction ℝ) (q n : ι → StieltjesFunction ℝ)
    (hp : ∀ k i, Continuous (p k i : ℝ → ℝ)) (hm : ∀ k i, Continuous (m k i : ℝ → ℝ))
    (hq : ∀ i, Continuous (q i : ℝ → ℝ)) (hn : ∀ i, Continuous (n i : ℝ → ℝ))
    (v d : κ → StieltjesFunction ℝ) (hv : ∀ k, Continuous (v k : ℝ → ℝ))
    (hcontrol : ∀ k i, (p k i).measure + (m k i).measure ≤ (v k).measure)
    (hbase : ∀ k i, (q i).measure + (n i).measure ≤ (v k).measure)
    (hdiff : ∀ k i, SameIncrements (p k i + n i) (m k i + q i) (r k i) (s k i))
    (hdelta : ∀ k i, (r k i).measure + (s k i).measure ≤ (d k).measure)
    (a b M : ℝ) (hab : a ≤ b) (hMone : 1 ≤ M) (hM : ∀ k, v k b - v k a ≤ M)
    (hvanish : Tendsto (fun k => d k b - d k a) l (𝓝 0)) :
    Tendsto (fun k => stieltjesSignature (p k) (m k) a b) l (𝓝 (stieltjesSignature q n a b)) := by
  apply tendsto_pi_nhds.mpr
  intro w
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp only [Real.dist_eq]
  have hlim : Tendsto (fun k => (w.length : ℝ) * (d k b - d k a) * M ^ w.length) l (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using (tendsto_const_nhds.mul hvanish).mul tendsto_const_nhds
  apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) _ hlim
  exact Eventually.of_forall (fun k => signature_difference_bound (p k) (m k) q n (r k) (s k)
    (hp k) (hm k) hq hn (v k) (hv k) (d k) (hcontrol k) (hbase k) (hdiff k) (hdelta k)
    a b M hab hMone (hM k) w)

/-- In finite dimension a common control is constructed by summing the
positive and negative coordinate measures. -/
def finiteControl {ι : Type*} [Fintype ι] (p m : ι → StieltjesFunction ℝ) : StieltjesFunction ℝ :=
  ∑ i, (p i + m i)

theorem finiteSum_apply {ι : Type*} (s : Finset ι) (f : ι → StieltjesFunction ℝ) (t : ℝ) :
    (∑ i ∈ s, f i) t = ∑ i ∈ s, f i t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [Finset.sum_insert, hi, ih]

theorem finiteSum_measure {ι : Type*} (s : Finset ι) (f : ι → StieltjesFunction ℝ) :
    (∑ i ∈ s, f i).measure = ∑ i ∈ s, (f i).measure := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [Finset.sum_insert, hi, StieltjesFunction.measure_add, ih]

theorem finiteControl_continuous {ι : Type*} [Fintype ι] (p m : ι → StieltjesFunction ℝ)
    (hp : ∀ i, Continuous (p i : ℝ → ℝ)) (hm : ∀ i, Continuous (m i : ℝ → ℝ)) :
    Continuous (finiteControl p m : ℝ → ℝ) := by
  change Continuous (fun t => (∑ i, (p i + m i)) t)
  simp_rw [finiteSum_apply, StieltjesFunction.add_apply]
  exact continuous_finset_sum _ (fun i _ => (hp i).add (hm i))

theorem finiteControl_dominates {ι : Type*} [Fintype ι] (p m : ι → StieltjesFunction ℝ) (i : ι) :
    (p i).measure + (m i).measure ≤ (finiteControl p m).measure := by
  classical
  rw [finiteControl, finiteSum_measure]
  simpa only [StieltjesFunction.measure_add] using
    (Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => bot_le : ∀ j ∈ Finset.univ, 0 ≤ (p j + m j).measure)
      (Finset.mem_univ i))

theorem finiteControl_increment {ι : Type*} [Fintype ι] (p m : ι → StieltjesFunction ℝ) (a b : ℝ) :
    finiteControl p m b - finiteControl p m a =
      ∑ i, ((p i b - p i a) + (m i b - m i a)) := by
  simp only [finiteControl, finiteSum_apply, StieltjesFunction.add_apply, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The finite-dimensional factorial estimate needs no supplied control:
the total coordinate variation measure itself constructs one. -/
theorem signature_factorial_bound_finite {ι : Type*} [Fintype ι] (p m : ι → StieltjesFunction ℝ)
    (hp : ∀ i, Continuous (p i : ℝ → ℝ)) (hm : ∀ i, Continuous (m i : ℝ → ℝ))
    (a b : ℝ) (hab : a ≤ b) (w : List ι) :
    |stieltjesSignature p m a b w| ≤
      (∑ i, ((p i b - p i a) + (m i b - m i a))) ^ w.length / (w.length.factorial : ℝ) := by
  simpa only [finiteControl_increment] using
    signature_factorial_bound p m hp hm (finiteControl p m) (finiteControl_continuous p m hp hm)
      (finiteControl_dominates p m) a b hab w

/-- For the canonical Jordan pair, the control increment is the actual
sum of coordinate variations, not an independently assumed bound. -/
theorem bv_signature_factorial_bound {ι : Type*} [Fintype ι] (f : ι → ℝ → ℝ)
    (hf : ∀ i, BoundedVariationOn (f i) univ) (hc : ∀ i, Continuous (f i))
    (a b : ℝ) (hab : a ≤ b) (w : List ι) :
    |stieltjesSignature (fun i => bvPositive (hf i) (hc i) a)
      (fun i => bvNegative (hf i) (hc i) a) a b w| ≤
      (∑ i, variationOnFromTo (f i) univ a b) ^ w.length / (w.length.factorial : ℝ) := by
  have h := signature_factorial_bound_finite
    (fun i => bvPositive (hf i) (hc i) a) (fun i => bvNegative (hf i) (hc i) a)
    (fun i => (jordan_continuous (hf i) (hc i) a).1)
    (fun i => (jordan_continuous (hf i) (hc i) a).2) a b hab w
  have he (i : ι) :
      (bvPositive (hf i) (hc i) a b - bvPositive (hf i) (hc i) a a) +
      (bvNegative (hf i) (hc i) a b - bvNegative (hf i) (hc i) a a) =
        variationOnFromTo (f i) univ a b := by
    change (jordanPositive (f i) a b - jordanPositive (f i) a a) +
      (jordanNegative (f i) a b - jordanNegative (f i) a a) = _
    have hb := jordan_sum (f i) a b
    have ha := jordan_sum (f i) a a
    rw [variationOnFromTo.self] at ha
    linarith
  simp_rw [he] at h
  exact h

end LinearInputCurveWordSignatureBounds
