/-!
Uniform convergence with uniformly bounded variation implies convergence of
actual Stieltjes signatures. Integration by parts moves a difference of
coordinate measures onto its uniformly small coordinate primitive.
-/

noncomputable section

namespace LinearInputCurveWordSignatureUniform

open Real Set MeasureTheory Filter
open scoped Topology
open LinearInputCurveWordStieltjes LinearInputCurveWordBVSignature
open LinearInputCurveWordBVShuffle LinearInputCurveWordSignatureBounds

def coordinateIncrement (p m : StieltjesFunction ℝ) (a t : ℝ) : ℝ :=
  (p t - p a) - (m t - m a)

theorem stieltjesIntegral_one_of_le (p m : StieltjesFunction ℝ) {a b : ℝ} (hab : a ≤ b) :
    stieltjesIntegral p m a b (fun _ => 1) = coordinateIncrement p m a b := by
  simp only [stieltjesIntegral, intervalIntegral.integral_of_le hab, integral_const,
    smul_eq_mul, mul_one, measureReal_def, Measure.restrict_apply_univ,
    StieltjesFunction.measure_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr (p.mono hab)),
    ENNReal.toReal_ofReal (sub_nonneg.mpr (m.mono hab)), coordinateIncrement]

theorem difference_coordinate_increment (p m q n : StieltjesFunction ℝ) (a t : ℝ) :
    coordinateIncrement (p + n) (m + q) a t =
      coordinateIncrement p m a t - coordinateIncrement q n a t := by
  simp only [coordinateIncrement, StieltjesFunction.add_apply]
  ring

/-- A uniformly small primitive controls integration against every fixed
signature coefficient, despite a potentially large variation of its derivative. -/
theorem integral_reverse_bound_of_small_primitive {ι : Type*}
    (r s : StieltjesFunction ℝ) (hr : Continuous (r : ℝ → ℝ)) (hs : Continuous (s : ℝ → ℝ))
    (q n : ι → StieltjesFunction ℝ)
    (hq : ∀ i, Continuous (q i : ℝ → ℝ)) (hn : ∀ i, Continuous (n i : ℝ → ℝ))
    (v : StieltjesFunction ℝ) (hv : Continuous (v : ℝ → ℝ))
    (hcontrol : ∀ i, (q i).measure + (n i).measure ≤ v.measure)
    (a b M ε : ℝ) (hab : a ≤ b) (hMone : 1 ≤ M) (hM : v b - v a ≤ M) (hε : 0 ≤ ε)
    (hsmall : ∀ t ∈ Icc a b, |stieltjesIntegral r s a t (fun _ => 1)| ≤ ε) (w : List ι) :
    |stieltjesIntegral r s a b (reverseStieltjes q n a w)| ≤ 2 * ε * M ^ w.length := by
  have hM0 : 0 ≤ M := zero_le_one.trans hMone
  cases w with
  | nil =>
    change |stieltjesIntegral r s a b (fun _ => 1)| ≤ 2 * ε * M ^ 0
    simpa only [pow_zero, mul_one] using (hsmall b ⟨hab, le_rfl⟩).trans (by linarith : ε ≤ 2 * ε)
  | cons j w =>
    let P := fun t => stieltjesIntegral r s a t (fun _ => 1)
    have hP : Continuous P := stieltjesIntegral_continuous r s hr hs continuous_const a
    have hR := reverseStieltjes_continuous q n hq hn a w
    have hparts := stieltjes_integration_by_parts r s (q j) (n j) hr hs (hq j) (hn j)
      (show Continuous (fun _ : ℝ => (1 : ℝ)) from continuous_const) hR hab
    simp only [one_mul] at hparts
    change P b * reverseStieltjes q n a (j :: w) b =
      stieltjesIntegral r s a b (reverseStieltjes q n a (j :: w)) +
        stieltjesIntegral (q j) (n j) a b (fun t => P t * reverseStieltjes q n a w t) at hparts
    have hmul : ∀ t ∈ Icc a b, |P t * reverseStieltjes q n a w t| ≤ ε * M ^ w.length := by
      intro t ht
      rw [abs_mul]
      exact mul_le_mul (hsmall t ht)
        (reverseStieltjes_power_bound q n hq hn v hv hcontrol a t M ht.1
          ((sub_le_sub_right (v.mono ht.2) (v a)).trans hM) w) (abs_nonneg _) hε
    have hi := abs_stieltjesIntegral_le_constant (q j) (n j) v (hcontrol j) (hP.mul hR) hab hmul
    have he : stieltjesIntegral r s a b (reverseStieltjes q n a (j :: w)) =
        P b * reverseStieltjes q n a (j :: w) b -
          stieltjesIntegral (q j) (n j) a b (fun t => P t * reverseStieltjes q n a w t) := by linarith
    rw [he]
    calc
      _ ≤ |P b * reverseStieltjes q n a (j :: w) b| +
          |stieltjesIntegral (q j) (n j) a b (fun t => P t * reverseStieltjes q n a w t)| := abs_sub _ _
      _ ≤ ε * M ^ (j :: w).length + (ε * M ^ w.length) * (v b - v a) := by
        apply add_le_add _ hi
        rw [abs_mul]
        exact mul_le_mul (hsmall b ⟨hab, le_rfl⟩)
          (reverseStieltjes_power_bound q n hq hn v hv hcontrol a b M hab hM (j :: w))
          (abs_nonneg _) hε
      _ ≤ ε * M ^ (j :: w).length + (ε * M ^ w.length) * M :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hM (by positivity))
      _ = 2 * ε * M ^ (j :: w).length := by rw [List.length_cons, pow_succ]; ring

/-- An explicit stability estimate using uniform coordinate increments and a
uniform variation bound. No small-variation assumption on the difference occurs. -/
theorem reverseStieltjes_uniform_difference_bound {ι : Type*}
    (p m q n : ι → StieltjesFunction ℝ)
    (hp : ∀ i, Continuous (p i : ℝ → ℝ)) (hm : ∀ i, Continuous (m i : ℝ → ℝ))
    (hq : ∀ i, Continuous (q i : ℝ → ℝ)) (hn : ∀ i, Continuous (n i : ℝ → ℝ))
    (v : StieltjesFunction ℝ) (hv : Continuous (v : ℝ → ℝ))
    (hcontrol : ∀ i, (p i).measure + (m i).measure ≤ v.measure)
    (hbase : ∀ i, (q i).measure + (n i).measure ≤ v.measure)
    (a b M ε : ℝ) (hMone : 1 ≤ M) (hM : v b - v a ≤ M) (hε : 0 ≤ ε)
    (hsmall : ∀ i t, t ∈ Icc a b →
      |coordinateIncrement (p i) (m i) a t - coordinateIncrement (q i) (n i) a t| ≤ ε)
    (w : List ι) :
    ∀ t ∈ Icc a b, |reverseStieltjes p m a w t - reverseStieltjes q n a w t| ≤
      2 * (w.length : ℝ) * ε * M ^ w.length := by
  have hM0 : 0 ≤ M := zero_le_one.trans hMone
  induction w with
  | nil => intro t _; simp [reverseStieltjes]
  | cons i w ih =>
    intro t ht
    have hF := reverseStieltjes_continuous p m hp hm a w
    have hG := reverseStieltjes_continuous q n hq hn a w
    have hs := differenceIntegral_split (p i) (m i) (q i) (n i) (p i + n i) (m i + q i)
      (fun _ _ => rfl) hF hG a t
    have h1 := abs_stieltjesIntegral_le_constant (p i) (m i) v (hcontrol i)
      (show Continuous (fun u => reverseStieltjes p m a w u - reverseStieltjes q n a w u) from hF.sub hG)
      ht.1 (fun u hu => ih u ⟨hu.1, hu.2.trans ht.2⟩)
    have hVt : v t - v a ≤ M := (sub_le_sub_right (v.mono ht.2) (v a)).trans hM
    have h2 := integral_reverse_bound_of_small_primitive (p i + n i) (m i + q i)
      ((hp i).add (hn i)) ((hm i).add (hq i)) q n hq hn v hv hbase
      a t M ε ht.1 hMone hVt hε (fun u hu => by
        rw [stieltjesIntegral_one_of_le _ _ hu.1, difference_coordinate_increment]
        exact hsmall i u ⟨hu.1, hu.2.trans ht.2⟩) w
    have hpow : M ^ w.length ≤ M ^ (w.length + 1) := by
      rw [pow_succ]
      exact le_mul_of_one_le_right (pow_nonneg hM0 _) hMone
    change |stieltjesIntegral (p i) (m i) a t _ - stieltjesIntegral (q i) (n i) a t _| ≤ _
    rw [hs]
    calc
      _ ≤ |stieltjesIntegral (p i) (m i) a t
          (fun u => reverseStieltjes p m a w u - reverseStieltjes q n a w u)| +
          |stieltjesIntegral (p i + n i) (m i + q i) a t (reverseStieltjes q n a w)| := abs_add_le _ _
      _ ≤ (2 * (w.length : ℝ) * ε * M ^ w.length) * (v t - v a) + 2 * ε * M ^ w.length :=
        add_le_add h1 h2
      _ ≤ (2 * (w.length : ℝ) * ε * M ^ w.length) * M + 2 * ε * M ^ (w.length + 1) :=
        add_le_add (mul_le_mul_of_nonneg_left hVt (by positivity))
          (mul_le_mul_of_nonneg_left hpow (by positivity))
      _ = 2 * ((i :: w).length : ℝ) * ε * M ^ (i :: w).length := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one, pow_succ]
        ring

theorem signature_uniform_difference_bound {ι : Type*}
    (p m q n : ι → StieltjesFunction ℝ)
    (hp : ∀ i, Continuous (p i : ℝ → ℝ)) (hm : ∀ i, Continuous (m i : ℝ → ℝ))
    (hq : ∀ i, Continuous (q i : ℝ → ℝ)) (hn : ∀ i, Continuous (n i : ℝ → ℝ))
    (v : StieltjesFunction ℝ) (hv : Continuous (v : ℝ → ℝ))
    (hcontrol : ∀ i, (p i).measure + (m i).measure ≤ v.measure)
    (hbase : ∀ i, (q i).measure + (n i).measure ≤ v.measure)
    (a b M ε : ℝ) (hab : a ≤ b) (hMone : 1 ≤ M) (hM : v b - v a ≤ M) (hε : 0 ≤ ε)
    (hsmall : ∀ i t, t ∈ Icc a b →
      |coordinateIncrement (p i) (m i) a t - coordinateIncrement (q i) (n i) a t| ≤ ε)
    (w : List ι) :
    |stieltjesSignature p m a b w - stieltjesSignature q n a b w| ≤
      2 * (w.length : ℝ) * ε * M ^ w.length := by
  simpa only [stieltjesSignature, List.length_reverse] using
    reverseStieltjes_uniform_difference_bound p m q n hp hm hq hn v hv hcontrol hbase
      a b M ε hMone hM hε hsmall w.reverse b ⟨hab, le_rfl⟩

theorem signature_tendsto_of_uniform_increment_bound {ι κ : Type*} {l : Filter κ}
    (p m : κ → ι → StieltjesFunction ℝ) (q n : ι → StieltjesFunction ℝ)
    (hp : ∀ k i, Continuous (p k i : ℝ → ℝ)) (hm : ∀ k i, Continuous (m k i : ℝ → ℝ))
    (hq : ∀ i, Continuous (q i : ℝ → ℝ)) (hn : ∀ i, Continuous (n i : ℝ → ℝ))
    (v : κ → StieltjesFunction ℝ) (hv : ∀ k, Continuous (v k : ℝ → ℝ))
    (hcontrol : ∀ k i, (p k i).measure + (m k i).measure ≤ (v k).measure)
    (hbase : ∀ k i, (q i).measure + (n i).measure ≤ (v k).measure)
    (a b M : ℝ) (hab : a ≤ b) (hMone : 1 ≤ M) (hM : ∀ k, v k b - v k a ≤ M)
    (ε : κ → ℝ) (hε : ∀ k, 0 ≤ ε k) (hvanish : Tendsto ε l (𝓝 0))
    (hsmall : ∀ k i t, t ∈ Icc a b →
      |coordinateIncrement (p k i) (m k i) a t - coordinateIncrement (q i) (n i) a t| ≤ ε k) :
    Tendsto (fun k => stieltjesSignature (p k) (m k) a b) l (𝓝 (stieltjesSignature q n a b)) := by
  apply tendsto_pi_nhds.mpr
  intro w
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp only [Real.dist_eq]
  have hlim : Tendsto (fun k => 2 * (w.length : ℝ) * ε k * M ^ w.length) l (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using (tendsto_const_nhds.mul hvanish).mul tendsto_const_nhds
  apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) _ hlim
  exact Eventually.of_forall (fun k => signature_uniform_difference_bound (p k) (m k) q n
    (hp k) (hm k) hq hn (v k) (hv k) (hcontrol k) (hbase k)
    a b M (ε k) hab hMone (hM k) (hε k) (hsmall k) w)

/-- Coordinatewise uniform convergence on a compact time interval and a
uniform BV control imply convergence of every signature coefficient. -/
theorem signature_tendsto_of_uniform_convergence {ι κ : Type*} [Finite ι] {l : Filter κ}
    (p m : κ → ι → StieltjesFunction ℝ) (q n : ι → StieltjesFunction ℝ)
    (hp : ∀ k i, Continuous (p k i : ℝ → ℝ)) (hm : ∀ k i, Continuous (m k i : ℝ → ℝ))
    (hq : ∀ i, Continuous (q i : ℝ → ℝ)) (hn : ∀ i, Continuous (n i : ℝ → ℝ))
    (v : κ → StieltjesFunction ℝ) (hv : ∀ k, Continuous (v k : ℝ → ℝ))
    (hcontrol : ∀ k i, (p k i).measure + (m k i).measure ≤ (v k).measure)
    (hbase : ∀ k i, (q i).measure + (n i).measure ≤ (v k).measure)
    (a b M : ℝ) (hab : a ≤ b) (hMone : 1 ≤ M) (hM : ∀ k, v k b - v k a ≤ M)
    (hconv : ∀ i, TendstoUniformlyOn (fun k => coordinateIncrement (p k i) (m k i) a)
      (coordinateIncrement (q i) (n i) a) l (Icc a b)) :
    Tendsto (fun k => stieltjesSignature (p k) (m k) a b) l (𝓝 (stieltjesSignature q n a b)) := by
  apply tendsto_pi_nhds.mpr
  intro w
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  let C : ℝ := 2 * (w.length : ℝ) * M ^ w.length
  have hC : 0 ≤ C := by dsimp [C]; have : 0 ≤ M := zero_le_one.trans hMone; positivity
  let η := δ / (C + 1)
  have hη : 0 < η := div_pos hδ (by positivity)
  have hlim : ∀ᶠ k in l, ∀ i t, t ∈ Icc a b →
      |coordinateIncrement (p k i) (m k i) a t - coordinateIncrement (q i) (n i) a t| ≤ η := by
    apply eventually_all.mpr
    intro i
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp (hconv i)) η hη] with k hk
    intro t ht
    simpa only [Real.dist_eq, abs_sub_comm] using (hk t ht).le
  filter_upwards [hlim] with k hk
  rw [Real.dist_eq]
  have hs := signature_uniform_difference_bound (p k) (m k) q n
    (hp k) (hm k) hq hn (v k) (hv k) (hcontrol k) (hbase k)
    a b M η hab hMone (hM k) hη.le hk w
  have he : 2 * (w.length : ℝ) * η * M ^ w.length = C * η := by dsimp [C]; ring
  rw [he] at hs
  apply hs.trans_lt
  have hid : (C + 1) * η = δ := by
    dsimp [η]
    field_simp
  nlinarith

def bvSignature {ι : Type*} (f : ι → ℝ → ℝ)
    (hf : ∀ i, BoundedVariationOn (f i) univ) (hc : ∀ i, Continuous (f i)) (a b : ℝ) : List ι → ℝ :=
  stieltjesSignature (fun i => bvPositive (hf i) (hc i) a) (fun i => bvNegative (hf i) (hc i) a) a b

def bvControl {ι : Type*} [Fintype ι] (f : ι → ℝ → ℝ)
    (hf : ∀ i, BoundedVariationOn (f i) univ) (hc : ∀ i, Continuous (f i)) (a : ℝ) : StieltjesFunction ℝ :=
  finiteControl (fun i => bvPositive (hf i) (hc i) a) (fun i => bvNegative (hf i) (hc i) a)

theorem coordinateIncrement_bv {f : ℝ → ℝ} (hf : BoundedVariationOn f univ) (hc : Continuous f)
    (a t : ℝ) : coordinateIncrement (bvPositive hf hc a) (bvNegative hf hc a) a t = f t - f a := by
  change (jordanPositive f a t - jordanPositive f a a) -
    (jordanNegative f a t - jordanNegative f a a) = _
  have ht := jordan_difference f a t
  have ha := jordan_difference f a a
  linarith

theorem bvControl_increment {ι : Type*} [Fintype ι] (f : ι → ℝ → ℝ)
    (hf : ∀ i, BoundedVariationOn (f i) univ) (hc : ∀ i, Continuous (f i))
    (a b : ℝ) (hab : a ≤ b) :
    bvControl f hf hc a b - bvControl f hf hc a a = ∑ i, (eVariationOn (f i) (Icc a b)).toReal := by
  rw [bvControl, finiteControl_increment]
  apply Finset.sum_congr rfl
  intro i _
  change (jordanPositive (f i) a b - jordanPositive (f i) a a) +
    (jordanNegative (f i) a b - jordanNegative (f i) a a) = _
  have hb := jordan_sum (f i) a b
  have ha := jordan_sum (f i) a a
  rw [variationOnFromTo.self] at ha
  rw [variationOnFromTo.eq_of_le _ _ hab, univ_inter] at hb
  linarith

/-- A formulation directly for finite-dimensional continuous BV curves.
Both the control and its size are derived from the actual Jordan decomposition
and actual coordinate variations. Global BV is supplied, for example, by the
previously proved constant endpoint extension of compact-interval BV curves. -/
theorem bvSignature_tendsto_of_uniform_convergence {ι κ : Type*} [Fintype ι] {l : Filter κ}
    (f : κ → ι → ℝ → ℝ) (g : ι → ℝ → ℝ)
    (hf : ∀ k i, BoundedVariationOn (f k i) univ) (hfc : ∀ k i, Continuous (f k i))
    (hg : ∀ i, BoundedVariationOn (g i) univ) (hgc : ∀ i, Continuous (g i))
    (a b M : ℝ) (hab : a ≤ b) (hMone : 1 ≤ M)
    (hM : ∀ k, (∑ i, (eVariationOn (f k i) (Icc a b)).toReal) +
      (∑ i, (eVariationOn (g i) (Icc a b)).toReal) ≤ M)
    (hconv : ∀ i, TendstoUniformlyOn (fun k => f k i) (g i) l (Icc a b)) :
    Tendsto (fun k => bvSignature (f k) (hf k) (hfc k) a b) l (𝓝 (bvSignature g hg hgc a b)) := by
  let p := fun k i => bvPositive (hf k i) (hfc k i) a
  let m := fun k i => bvNegative (hf k i) (hfc k i) a
  let q := fun i => bvPositive (hg i) (hgc i) a
  let n := fun i => bvNegative (hg i) (hgc i) a
  have hp : ∀ k i, Continuous (p k i : ℝ → ℝ) := fun k i => (jordan_continuous (hf k i) (hfc k i) a).1
  have hm : ∀ k i, Continuous (m k i : ℝ → ℝ) := fun k i => (jordan_continuous (hf k i) (hfc k i) a).2
  have hq : ∀ i, Continuous (q i : ℝ → ℝ) := fun i => (jordan_continuous (hg i) (hgc i) a).1
  have hn : ∀ i, Continuous (n i : ℝ → ℝ) := fun i => (jordan_continuous (hg i) (hgc i) a).2
  let v := fun k => finiteControl (p k) (m k) + finiteControl q n
  have hv : ∀ k, Continuous (v k : ℝ → ℝ) := fun k =>
    (finiteControl_continuous _ _ (hp k) (hm k)).add (finiteControl_continuous _ _ hq hn)
  have hvM : ∀ k, v k b - v k a ≤ M := by
    intro k
    change (bvControl (f k) (hf k) (hfc k) a b + bvControl g hg hgc a b) -
      (bvControl (f k) (hf k) (hfc k) a a + bvControl g hg hgc a a) ≤ M
    have he : (bvControl (f k) (hf k) (hfc k) a b + bvControl g hg hgc a b) -
        (bvControl (f k) (hf k) (hfc k) a a + bvControl g hg hgc a a) =
        (bvControl (f k) (hf k) (hfc k) a b - bvControl (f k) (hf k) (hfc k) a a) +
        (bvControl g hg hgc a b - bvControl g hg hgc a a) := by ring
    rw [he, bvControl_increment _ _ _ a b hab, bvControl_increment _ _ _ a b hab]
    exact hM k
  apply signature_tendsto_of_uniform_convergence p m q n hp hm hq hn v hv
    (fun k i => by
      rw [show v k = finiteControl (p k) (m k) + finiteControl q n from rfl,
        StieltjesFunction.measure_add]
      exact Measure.le_add_right (finiteControl_dominates (p k) (m k) i))
    (fun k i => by
      rw [show v k = finiteControl (p k) (m k) + finiteControl q n from rfl,
        StieltjesFunction.measure_add]
      exact Measure.le_add_left (finiteControl_dominates q n i)) a b M hab hMone hvM
  intro i
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp (hconv i)) (ε / 2) (by positivity)] with k hk
  intro t ht
  change dist (coordinateIncrement (bvPositive (hg i) (hgc i) a) (bvNegative (hg i) (hgc i) a) a t)
    (coordinateIncrement (bvPositive (hf k i) (hfc k i) a) (bvNegative (hf k i) (hfc k i) a) a t) < ε
  rw [coordinateIncrement_bv, coordinateIncrement_bv, Real.dist_eq]
  have hbound : |(g i t - g i a) - (f k i t - f k i a)| ≤
      |g i t - f k i t| + |g i a - f k i a| := by
    convert abs_sub (g i t - f k i t) (g i a - f k i a) using 1
    congr 1
    ring
  have ht' := hk t ht
  have ha' := hk a ⟨le_rfl, hab⟩
  rw [Real.dist_eq] at ht' ha'
  linarith

end LinearInputCurveWordSignatureUniform
