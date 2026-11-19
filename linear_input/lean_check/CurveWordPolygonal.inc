/-!
Polygonal interpolation of time-ordered samples, with constant endpoint
extensions. All variations and signatures refer to the actual interpolated
function, not to an independently supplied polygonal model.
-/

noncomputable section

namespace LinearInputCurveWordPolygonal

open Real Set MeasureTheory Filter
open scoped Topology
open LinearInputCurveWordBoundedVariation

def ramp (a b t : ℝ) : ℝ := (clamp a b t - a) / (b - a)

theorem ramp_continuous (a b : ℝ) : Continuous (ramp a b) :=
  ((clamp_continuous a b).sub continuous_const).div_const (b - a)

theorem ramp_monotone {a b : ℝ} (hab : a < b) : Monotone (ramp a b) := by
  intro s t hst
  exact div_le_div_of_nonneg_right (sub_le_sub_right (clamp_monotone a b hst) a) (sub_pos.mpr hab).le

theorem ramp_mem {a b : ℝ} (hab : a < b) (t : ℝ) : ramp a b t ∈ Icc (0 : ℝ) 1 := by
  have hc := clamp_mem hab.le t
  constructor
  · exact div_nonneg (sub_nonneg.mpr hc.1) (sub_pos.mpr hab).le
  · exact (div_le_one (sub_pos.mpr hab)).mpr (sub_le_sub_right hc.2 a)

theorem ramp_before {a b t : ℝ} (ht : t ≤ a) : ramp a b t = 0 := by
  have hmin : min b t ≤ a := (min_le_right b t).trans ht
  simp [ramp, clamp, max_eq_left hmin]

theorem ramp_after {a b t : ℝ} (hab : a < b) (ht : b ≤ t) : ramp a b t = 1 := by
  simp [ramp, clamp, min_eq_left ht, max_eq_right hab.le, ne_of_gt (sub_pos.mpr hab)]

theorem ramp_on {a b t : ℝ} (ht : t ∈ Icc a b) : ramp a b t = (t - a) / (b - a) := by
  rw [ramp, clamp_eq ht]

def polygonal (T X : ℕ → ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  X 0 + ∑ j ∈ Finset.range N, ramp (T j) (T (j + 1)) t * (X (j + 1) - X j)

theorem polygonal_zero (T X : ℕ → ℝ) (t : ℝ) : polygonal T X 0 t = X 0 := by simp [polygonal]

theorem polygonal_succ (T X : ℕ → ℝ) (N : ℕ) (t : ℝ) :
    polygonal T X (N + 1) t = polygonal T X N t + ramp (T N) (T (N + 1)) t * (X (N + 1) - X N) := by
  simp only [polygonal, Finset.sum_range_succ]
  ring

theorem polygonal_continuous (T X : ℕ → ℝ) (N : ℕ) : Continuous (polygonal T X N) := by
  apply continuous_const.add
  change Continuous (fun t => ∑ j ∈ Finset.range N, ramp (T j) (T (j + 1)) t * (X (j + 1) - X j))
  exact continuous_finsetSum _ (fun j _ => (ramp_continuous (T j) (T (j + 1))).mul continuous_const)

theorem polygonal_before (T X : ℕ → ℝ) (N : ℕ) (hT : Monotone T)
    {t : ℝ} (ht : t ≤ T 0) : polygonal T X N t = X 0 := by
  unfold polygonal
  have hz : ∀ j ∈ Finset.range N, ramp (T j) (T (j + 1)) t * (X (j + 1) - X j) = 0 := by
    intro j _
    rw [ramp_before (ht.trans (hT (Nat.zero_le j))), zero_mul]
  rw [Finset.sum_eq_zero hz, add_zero]

theorem polygonal_after (T X : ℕ → ℝ) (N : ℕ) (hT : Monotone T)
    (hs : ∀ j < N, T j < T (j + 1)) {t : ℝ} (ht : T N ≤ t) : polygonal T X N t = X N := by
  unfold polygonal
  have he : ∀ j ∈ Finset.range N,
      ramp (T j) (T (j + 1)) t * (X (j + 1) - X j) = X (j + 1) - X j := by
    intro j hj
    have hjN := Finset.mem_range.mp hj
    rw [ramp_after (hs j hjN) ((hT (Nat.succ_le_of_lt hjN)).trans ht), one_mul]
  rw [Finset.sum_congr rfl he, Finset.sum_range_sub]
  ring

/-- On each sample interval, the global curve is the affine segment between
the corresponding sampled values, including both endpoints. -/
theorem polygonal_on_edge (T X : ℕ → ℝ) (hT : Monotone T) (N : ℕ)
    (hs : ∀ j < N, T j < T (j + 1)) (i : ℕ) (hi : i < N) {t : ℝ}
    (ht : t ∈ Icc (T i) (T (i + 1))) :
    polygonal T X N t = X i + (t - T i) / (T (i + 1) - T i) * (X (i + 1) - X i) := by
  induction N with
  | zero => omega
  | succ N ih =>
    rw [polygonal_succ]
    by_cases hin : i < N
    · rw [ih (fun j hj => hs j (by omega)) hin,
        ramp_before (ht.2.trans (hT (by omega : i + 1 ≤ N))), zero_mul, add_zero]
    · have hei : i = N := by omega
      subst i
      rw [polygonal_after T X N hT (fun j hj => hs j (by omega)) ht.1, ramp_on ht]

theorem polygonal_sub_eq_sum (T X : ℕ → ℝ) (N : ℕ) (s t : ℝ) :
    polygonal T X N t - polygonal T X N s =
      ∑ j ∈ Finset.range N, (ramp (T j) (T (j + 1)) t - ramp (T j) (T (j + 1)) s) * (X (j + 1) - X j) := by
  simp only [polygonal]
  rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

def lengthControl (T X : ℕ → ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range N, ramp (T j) (T (j + 1)) t * |X (j + 1) - X j|

def sampleLength (X : ℕ → ℝ) (N : ℕ) : ℝ := ∑ j ∈ Finset.range N, |X (j + 1) - X j|

theorem lengthControl_mem (T X : ℕ → ℝ) (N : ℕ)
    (hs : ∀ j < N, T j < T (j + 1)) (t : ℝ) :
    lengthControl T X N t ∈ Icc (0 : ℝ) (sampleLength X N) := by
  constructor
  · exact Finset.sum_nonneg (fun j hj => mul_nonneg (ramp_mem (hs j (Finset.mem_range.mp hj)) t).1 (abs_nonneg _))
  · apply Finset.sum_le_sum
    intro j hj
    exact mul_le_of_le_one_left (abs_nonneg _) (ramp_mem (hs j (Finset.mem_range.mp hj)) t).2

theorem polygonal_increment_le_control (T X : ℕ → ℝ) (N : ℕ)
    (hs : ∀ j < N, T j < T (j + 1)) {s t : ℝ} (hst : s ≤ t) :
    |polygonal T X N t - polygonal T X N s| ≤ lengthControl T X N t - lengthControl T X N s := by
  rw [polygonal_sub_eq_sum]
  calc
    _ ≤ ∑ j ∈ Finset.range N,
        |(ramp (T j) (T (j + 1)) t - ramp (T j) (T (j + 1)) s) * (X (j + 1) - X j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      simp only [lengthControl, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (ramp_monotone (hs j (Finset.mem_range.mp hj)) hst))]
      ring

theorem variation_le_bounded_control (f v : ℝ → ℝ) (V : ℝ)
    (hinc : ∀ s t, s ≤ t → |f t - f s| ≤ v t - v s)
    (hspan : ∀ s t, v t - v s ≤ V) : eVariationOn f univ ≤ ENNReal.ofReal V := by
  apply iSup_le
  rintro ⟨k, u, hu, _⟩
  calc
    _ ≤ ∑ j ∈ Finset.range k, ENNReal.ofReal (v (u (j + 1)) - v (u j)) := by
      apply Finset.sum_le_sum
      intro j _
      rw [edist_dist, Real.dist_eq]
      exact ENNReal.ofReal_le_ofReal (hinc _ _ (hu (Nat.le_succ j)))
    _ = ENNReal.ofReal (∑ j ∈ Finset.range k, (v (u (j + 1)) - v (u j))) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro j _
      exact (abs_nonneg _).trans (hinc _ _ (hu (Nat.le_succ j)))
    _ = ENNReal.ofReal (v (u k) - v (u 0)) := by rw [Finset.sum_range_sub (fun j => v (u j))]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (hspan _ _)

theorem polygonal_variation_le_sampleLength (T X : ℕ → ℝ) (N : ℕ)
    (hs : ∀ j < N, T j < T (j + 1)) :
    eVariationOn (polygonal T X N) univ ≤ ENNReal.ofReal (sampleLength X N) := by
  apply variation_le_bounded_control _ (lengthControl T X N) _
    (fun _ _ hst => polygonal_increment_le_control T X N hs hst)
  intro s t
  have hs' := lengthControl_mem T X N hs s
  have ht' := lengthControl_mem T X N hs t
  linarith [hs'.1, ht'.2]

theorem polygonal_boundedVariation (T X : ℕ → ℝ) (N : ℕ)
    (hs : ∀ j < N, T j < T (j + 1)) : BoundedVariationOn (polygonal T X N) univ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (polygonal_variation_le_sampleLength T X N hs)

theorem sampleLength_le_variation (T : ℕ → ℝ) (f : ℝ → ℝ) (N : ℕ) (hT : Monotone T) :
    ENNReal.ofReal (sampleLength (f ∘ T) N) ≤ eVariationOn f (Icc (T 0) (T N)) := by
  have h := eVariationOn.sum_le_of_monotoneOn_Iic (f := f) (s := Icc (T 0) (T N)) (n := N) (u := T)
    (hT.monotoneOn _) (fun i hi => ⟨hT (Nat.zero_le i), hT hi⟩)
  simpa only [sampleLength, Function.comp_apply, edist_dist, Real.dist_eq,
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => abs_nonneg _)] using h

/-- Sampling in time order cannot increase total variation, even when the
polygonal curve is extended constantly to the entire real line. -/
theorem polygonal_variation_le (T : ℕ → ℝ) (f : ℝ → ℝ) (N : ℕ) (hT : Monotone T)
    (hs : ∀ j < N, T j < T (j + 1)) :
    eVariationOn (polygonal T (f ∘ T) N) univ ≤ eVariationOn f (Icc (T 0) (T N)) :=
  (polygonal_variation_le_sampleLength T (f ∘ T) N hs).trans (sampleLength_le_variation T f N hT)

theorem exists_sample_edge (T : ℕ → ℝ) (N : ℕ) (hN : 0 < N) {t : ℝ}
    (ht : t ∈ Icc (T 0) (T N)) : ∃ i < N, t ∈ Icc (T i) (T (i + 1)) := by
  induction N with
  | zero => omega
  | succ N ih =>
    by_cases hn : N = 0
    · subst N
      exact ⟨0, by omega, ht⟩
    · by_cases htn : t ≤ T N
      · obtain ⟨i, hi, hit⟩ := ih (by omega) ⟨ht.1, htn⟩
        exact ⟨i, by omega, hit⟩
      · exact ⟨N, by omega, (not_le.mp htn).le, ht.2⟩

theorem polygonal_approx_on_edge (T : ℕ → ℝ) (f : ℝ → ℝ) (hT : Monotone T) (N : ℕ)
    (hs : ∀ j < N, T j < T (j + 1)) (i : ℕ) (hi : i < N) {t ε : ℝ}
    (ht : t ∈ Icc (T i) (T (i + 1)))
    (hleft : |f (T i) - f t| ≤ ε) (hright : |f (T (i + 1)) - f t| ≤ ε) :
    |polygonal T (f ∘ T) N t - f t| ≤ ε := by
  rw [polygonal_on_edge T (f ∘ T) hT N hs i hi ht]
  simp only [Function.comp_apply]
  let θ := (t - T i) / (T (i + 1) - T i)
  have hθ : θ ∈ Icc (0 : ℝ) 1 := by
    dsimp only [θ]
    rw [← ramp_on ht]
    exact ramp_mem (hs i hi) t
  have he : f (T i) + θ * (f (T (i + 1)) - f (T i)) - f t =
      (1 - θ) * (f (T i) - f t) + θ * (f (T (i + 1)) - f t) := by ring
  change |f (T i) + θ * (f (T (i + 1)) - f (T i)) - f t| ≤ ε
  rw [he]
  calc
    _ ≤ |(1 - θ) * (f (T i) - f t)| + |θ * (f (T (i + 1)) - f t)| := abs_add_le _ _
    _ = (1 - θ) * |f (T i) - f t| + θ * |f (T (i + 1)) - f t| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hθ.2), abs_of_nonneg hθ.1]
    _ ≤ (1 - θ) * ε + θ * ε :=
      add_le_add (mul_le_mul_of_nonneg_left hleft (sub_nonneg.mpr hθ.2))
        (mul_le_mul_of_nonneg_left hright hθ.1)
    _ = ε := by ring

/-- Uniform approximation follows from oscillation control on the actual
sample intervals; a small mesh is one way, but not the only way, to supply it. -/
theorem polygonal_uniform_approx (T : ℕ → ℝ) (f : ℝ → ℝ) (hT : Monotone T) (N : ℕ)
    (hs : ∀ j < N, T j < T (j + 1)) {ε : ℝ} (hε : 0 ≤ ε)
    (hosc : ∀ i < N, ∀ t ∈ Icc (T i) (T (i + 1)),
      |f (T i) - f t| ≤ ε ∧ |f (T (i + 1)) - f t| ≤ ε) :
    ∀ t ∈ Icc (T 0) (T N), |polygonal T (f ∘ T) N t - f t| ≤ ε := by
  intro t ht
  by_cases hN : N = 0
  · subst N
    have he : t = T 0 := le_antisymm ht.2 ht.1
    simp only [polygonal_zero, Function.comp_apply, he, sub_self, abs_zero]
    exact hε
  · obtain ⟨i, hi, hit⟩ := exists_sample_edge T N (Nat.pos_of_ne_zero hN) ht
    exact polygonal_approx_on_edge T f hT N hs i hi hit (hosc i hi t hit).1 (hosc i hi t hit).2

def extendSamples {N : ℕ} (T : Fin (N + 1) → ℝ) (j : ℕ) : ℝ :=
  T ⟨min j N, Nat.lt_succ_of_le (min_le_right j N)⟩

theorem extendSamples_of_le {N : ℕ} (T : Fin (N + 1) → ℝ) {j : ℕ} (hj : j ≤ N) :
    extendSamples T j = T ⟨j, Nat.lt_succ_of_le hj⟩ := by
  unfold extendSamples
  congr 1
  exact Fin.ext (min_eq_left hj)

theorem extendSamples_monotone {N : ℕ} (T : Fin (N + 1) → ℝ) (hT : StrictMono T) :
    Monotone (extendSamples T) := by
  intro i j hij
  apply hT.monotone
  exact min_le_min_right N hij

theorem extendSamples_strict {N : ℕ} (T : Fin (N + 1) → ℝ) (hT : StrictMono T) :
    ∀ j < N, extendSamples T j < extendSamples T (j + 1) := by
  intro j hj
  rw [extendSamples_of_le T hj.le, extendSamples_of_le T (Nat.succ_le_of_lt hj)]
  apply hT
  exact Nat.lt_succ_self j

def interpolate {N : ℕ} (T X : Fin (N + 1) → ℝ) : ℝ → ℝ :=
  polygonal (extendSamples T) (extendSamples X) N

theorem interpolate_continuous {N : ℕ} (T X : Fin (N + 1) → ℝ) : Continuous (interpolate T X) :=
  polygonal_continuous _ _ _

theorem interpolate_boundedVariation {N : ℕ} (T X : Fin (N + 1) → ℝ) (hT : StrictMono T) :
    BoundedVariationOn (interpolate T X) univ :=
  polygonal_boundedVariation _ _ _ (extendSamples_strict T hT)

theorem interpolate_on_edge {N : ℕ} (T X : Fin (N + 1) → ℝ) (hT : StrictMono T)
    (i : Fin N) {t : ℝ} (ht : t ∈ Icc (T i.castSucc) (T i.succ)) :
    interpolate T X t = X i.castSucc + (t - T i.castSucc) / (T i.succ - T i.castSucc) *
      (X i.succ - X i.castSucc) := by
  have he := polygonal_on_edge (extendSamples T) (extendSamples X) (extendSamples_monotone T hT)
    N (extendSamples_strict T hT) i.val i.isLt (t := t)
  have ht' : t ∈ Icc (extendSamples T i.val) (extendSamples T (i.val + 1)) := by
    simpa only [extendSamples_of_le T i.isLt.le, extendSamples_of_le T (Nat.succ_le_of_lt i.isLt)] using! ht
  simpa only [interpolate, extendSamples_of_le T i.isLt.le,
    extendSamples_of_le T (Nat.succ_le_of_lt i.isLt), extendSamples_of_le X i.isLt.le,
    extendSamples_of_le X (Nat.succ_le_of_lt i.isLt)] using! he ht'

theorem interpolate_variation_le {N : ℕ} (T : Fin (N + 1) → ℝ) (hT : StrictMono T) (f : ℝ → ℝ) :
    eVariationOn (interpolate T (f ∘ T)) univ ≤ eVariationOn f (Icc (T 0) (T (Fin.last N))) := by
  have h := polygonal_variation_le (extendSamples T) f N (extendSamples_monotone T hT)
    (extendSamples_strict T hT)
  change eVariationOn (interpolate T (f ∘ T)) univ ≤ _ at h
  simpa only [extendSamples_of_le T (Nat.zero_le N), extendSamples_of_le T (le_refl N)] using! h

theorem interpolate_uniform_approx {N : ℕ} (T : Fin (N + 1) → ℝ) (hT : StrictMono T)
    (f : ℝ → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hosc : ∀ i : Fin N, ∀ t ∈ Icc (T i.castSucc) (T i.succ),
      |f (T i.castSucc) - f t| ≤ ε ∧ |f (T i.succ) - f t| ≤ ε) :
    ∀ t ∈ Icc (T 0) (T (Fin.last N)), |interpolate T (f ∘ T) t - f t| ≤ ε := by
  have ho : ∀ j < N, ∀ t ∈ Icc (extendSamples T j) (extendSamples T (j + 1)),
      |f (extendSamples T j) - f t| ≤ ε ∧ |f (extendSamples T (j + 1)) - f t| ≤ ε := by
    intro j hj t ht
    simpa only [extendSamples_of_le T hj.le, extendSamples_of_le T (Nat.succ_le_of_lt hj)] using!
      hosc ⟨j, hj⟩ t (by simpa only [extendSamples_of_le T hj.le,
        extendSamples_of_le T (Nat.succ_le_of_lt hj)] using! ht)
  have h := polygonal_uniform_approx (extendSamples T) f (extendSamples_monotone T hT)
    N (extendSamples_strict T hT) hε ho
  simpa only [extendSamples_of_le T (Nat.zero_le N), extendSamples_of_le T (le_refl N)] using! h

theorem interpolate_tendstoUniformlyOn_of_oscillation {κ : Type*} {l : Filter κ}
    (N : κ → ℕ) (T : ∀ k, Fin (N k + 1) → ℝ) (hT : ∀ k, StrictMono (T k))
    (f : ℝ → ℝ) (a b : ℝ) (ha : ∀ k, T k 0 = a) (hb : ∀ k, T k (Fin.last (N k)) = b)
    (hosc : ∀ ε > 0, ∀ᶠ k in l, ∀ i : Fin (N k), ∀ t ∈ Icc (T k i.castSucc) (T k i.succ),
      |f (T k i.castSucc) - f t| ≤ ε ∧ |f (T k i.succ) - f t| ≤ ε) :
    TendstoUniformlyOn (fun k => interpolate (T k) (f ∘ T k)) f l (Icc a b) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hosc (ε / 2) (by positivity)] with k hk
  intro t ht
  have ht' : t ∈ Icc (T k 0) (T k (Fin.last (N k))) := by simpa only [ha, hb] using ht
  have h := interpolate_uniform_approx (T k) (hT k) f (by positivity : 0 ≤ ε / 2) hk t ht'
  rw [Real.dist_eq, abs_sub_comm]
  exact h.trans_lt (by linarith)

open LinearInputCurveWordStieltjes LinearInputCurveWordBVSignature LinearInputCurveWordBVCanonical
open LinearInputCurveWordSignature LinearInputCurveWordReparametrization LinearInputCurveWordFormalSeries

def affineEdge (a b x y t : ℝ) : ℝ := x + (t - a) / (b - a) * (y - x)

theorem affineEdge_hasDerivAt (a b x y t : ℝ) :
    HasDerivAt (affineEdge a b x y) ((y - x) / (b - a)) t := by
  change HasDerivAt (fun s => x + (s - a) / (b - a) * (y - x)) _ t
  convert (hasDerivAt_const t x).add (((hasDerivAt_id t).sub_const a).div_const (b - a) |>.mul_const (y - x)) using 1
  · rfl
  · ring

/-- Any local Stieltjes representation of the affine edge has the actual
unit-time straight-segment signature. -/
theorem stieltjesSignature_affineEdge {ι : Type*} (p m : ι → StieltjesFunction ℝ)
    (x y : ι → ℝ) (a b : ℝ) (hab : a < b)
    (hrep : ∀ i, RepresentsOn (p i) (m i) (affineEdge a b (x i) (y i)) a b) (w : List ι) :
    stieltjesSignature p m a b w = signature (fun i _ => y i - x i) 0 1 w := by
  let v := fun i (_ : ℝ) => (y i - x i) / (b - a)
  have hv : ∀ i, Continuous (v i) := fun _ => continuous_const
  have hd : ∀ i t, HasDerivAt (affineEdge a b (x i) (y i)) (v i t) t :=
    fun i t => affineEdge_hasDerivAt a b (x i) (y i) t
  rw [stieltjesSignature_independent_on
    (fun i => primitive_continuous (positiveVelocity_continuous (hv i)))
    (fun i => primitive_continuous (negativeVelocity_continuous (hv i))) hab.le
    (fun i => (hrep i).sameIncrementsOn (c1_representsOn (hv i) (hd i) a b)) w,
    c1_stieltjesSignature_eq_signature hv]
  have hg (t : ℝ) : HasDerivAt (fun t => (t - a) / (b - a)) (1 / (b - a)) t :=
    ((hasDerivAt_id t).sub_const a).div_const (b - a)
  have hr := signature_reparametrize (fun _ : ι => continuous_const) hg continuous_const a b w
    (v := fun i _ => y i - x i)
  have he : (fun i (_ : ℝ) => 1 / (b - a) * (y i - x i)) = v := by
    funext i t
    dsimp [v]
    ring
  simp only [sub_self, zero_div, div_self (ne_of_gt (sub_pos.mpr hab))] at hr
  rw [he] at hr
  exact hr

/-- Ordered product of actual unit-time straight-segment signatures. -/
def segmentProduct {ι : Type*} (X : ℕ → ι → ℝ) : ℕ → Series ι
  | 0 => unitSeries
  | N + 1 => product (segmentProduct X N) (signature (fun i _ => X (N + 1) i - X N i) 0 1)

theorem stieltjesSignature_same {ι : Type*} (p m : ι → StieltjesFunction ℝ) (a : ℝ) :
    stieltjesSignature p m a a = unitSeries := by
  funext w
  cases w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w i =>
    simp [stieltjesSignature, List.reverse_append, reverseStieltjes, stieltjesIntegral, unitSeries]
    cases w <;> rfl

/-- Local representation on the sampled interval suffices for the whole
polygonal signature to equal the chronological product of its edge signatures. -/
theorem stieltjesSignature_polygonal_product {ι : Type*}
    (p m : ι → StieltjesFunction ℝ)
    (hp : ∀ i, Continuous (p i : ℝ → ℝ)) (hm : ∀ i, Continuous (m i : ℝ → ℝ))
    (T : ℕ → ℝ) (X : ℕ → ι → ℝ) (N : ℕ) (hT : Monotone T)
    (hs : ∀ j < N, T j < T (j + 1))
    (hrep : ∀ i, RepresentsOn (p i) (m i) (polygonal T (fun j => X j i) N) (T 0) (T N)) :
    stieltjesSignature p m (T 0) (T N) = segmentProduct X N := by
  have hprefix : ∀ k ≤ N, stieltjesSignature p m (T 0) (T k) = segmentProduct X k := by
    intro k
    induction k with
    | zero => intro _; exact stieltjesSignature_same p m (T 0)
    | succ k ih =>
      intro hkN
      have hk : k < N := by omega
      have hedge : stieltjesSignature p m (T k) (T (k + 1)) =
          signature (fun i _ => X (k + 1) i - X k i) 0 1 := by
        funext w
        apply stieltjesSignature_affineEdge p m (X k) (X (k + 1)) (T k) (T (k + 1)) (hs k hk) _ w
        intro i x hx y hy
        have hfull : Icc (T k) (T (k + 1)) ⊆ Icc (T 0) (T N) :=
          Icc_subset_Icc (hT (Nat.zero_le k)) (hT hkN)
        have he := hrep i x (hfull hx) y (hfull hy)
        rw [polygonal_on_edge T (fun j => X j i) hT N hs k hk hx,
          polygonal_on_edge T (fun j => X j i) hT N hs k hk hy] at he
        exact he
      change stieltjesSignature p m (T 0) (T (k + 1)) =
        product (segmentProduct X k) (signature (fun i _ => X (k + 1) i - X k i) 0 1)
      rw [← ih (by omega), ← hedge]
      funext w
      exact LinearInputCurveWordBVChen.stieltjesSignature_chen p m hp hm (T 0) (T k) (T (k + 1)) w
  exact hprefix N le_rfl

theorem curveSignature_polygonal_product {ι : Type*}
    (T : ℕ → ℝ) (X : ℕ → ι → ℝ) (N : ℕ) (hT : Monotone T)
    (hs : ∀ j < N, T j < T (j + 1)) :
    curveSignature (fun i => polygonal T (fun j => X j i) N) (hT (Nat.zero_le N))
      (fun i => (polygonal_boundedVariation T (fun j => X j i) N hs).mono (subset_univ _))
      (fun i => (polygonal_continuous T (fun j => X j i) N).continuousOn) = segmentProduct X N := by
  apply stieltjesSignature_polygonal_product
    _ _ (fun i => canonicalPositive_continuous _ _ _) (fun i => canonicalNegative_continuous _ _ _)
    T X N hT hs
  intro i
  exact canonical_represents _ _ _

open LinearInputCurveWordSignatureUniform

theorem bvSignature_polygonal_product {ι : Type*}
    (T : ℕ → ℝ) (X : ℕ → ι → ℝ) (N : ℕ) (hT : Monotone T)
    (hs : ∀ j < N, T j < T (j + 1)) :
    bvSignature (fun i => polygonal T (fun j => X j i) N)
      (fun i => polygonal_boundedVariation T (fun j => X j i) N hs)
      (fun i => polygonal_continuous T (fun j => X j i) N) (T 0) (T N) = segmentProduct X N := by
  apply stieltjesSignature_polygonal_product _ _
    (fun i => (jordan_continuous (polygonal_boundedVariation T (fun j => X j i) N hs)
      (polygonal_continuous T (fun j => X j i) N) (T 0)).1)
    (fun i => (jordan_continuous (polygonal_boundedVariation T (fun j => X j i) N hs)
      (polygonal_continuous T (fun j => X j i) N) (T 0)).2) T X N hT hs
  intro i x _ y _
  change (jordanPositive _ (T 0) y - jordanPositive _ (T 0) x) -
    (jordanNegative _ (T 0) y - jordanNegative _ (T 0) x) = _
  have hx := jordan_difference (polygonal T (fun j => X j i) N) (T 0) x
  have hy := jordan_difference (polygonal T (fun j => X j i) N) (T 0) y
  linarith

def interpolateProduct {ι : Type*} {N : ℕ} (X : Fin (N + 1) → ι → ℝ) : Series ι :=
  segmentProduct (fun j i => extendSamples (fun k => X k i) j) N

theorem bvSignature_interpolate_product {ι : Type*} {N : ℕ}
    (T : Fin (N + 1) → ℝ) (X : Fin (N + 1) → ι → ℝ) (hT : StrictMono T) :
    bvSignature (fun i => interpolate T (fun k => X k i))
      (fun i => interpolate_boundedVariation T (fun k => X k i) hT)
      (fun i => interpolate_continuous T (fun k => X k i)) (T 0) (T (Fin.last N)) = interpolateProduct X := by
  have h := bvSignature_polygonal_product (extendSamples T)
    (fun j i => extendSamples (fun k => X k i) j) N (extendSamples_monotone T hT) (extendSamples_strict T hT)
  simpa only [extendSamples_of_le T (Nat.zero_le N), extendSamples_of_le T (le_refl N)] using! h

theorem curveSignature_eq_bvSignature {ι : Type*} (f : ι → ℝ → ℝ)
    (hf : ∀ i, BoundedVariationOn (f i) univ) (hc : ∀ i, Continuous (f i))
    {a b : ℝ} (hab : a ≤ b) :
    curveSignature f hab (fun i => (hf i).mono (subset_univ _)) (fun i => (hc i).continuousOn) =
      bvSignature f hf hc a b := by
  funext w
  apply curveSignature_eq_representation f hab _ _
    (fun i => bvPositive (hf i) (hc i) a) (fun i => bvNegative (hf i) (hc i) a)
    (fun i => (jordan_continuous (hf i) (hc i) a).1)
    (fun i => (jordan_continuous (hf i) (hc i) a).2) _ w
  intro i x _ y _
  change (jordanPositive (f i) a y - jordanPositive (f i) a x) -
    (jordanNegative (f i) a y - jordanNegative (f i) a x) = _
  linarith [jordan_difference (f i) a x, jordan_difference (f i) a y]

theorem curveSignature_interpolate_product {ι : Type*} {N : ℕ}
    (T : Fin (N + 1) → ℝ) (X : Fin (N + 1) → ι → ℝ) (hT : StrictMono T) :
    curveSignature (fun i => interpolate T (fun k => X k i)) (hT.monotone (Fin.zero_le (Fin.last N)))
      (fun i => (interpolate_boundedVariation T (fun k => X k i) hT).mono (subset_univ _))
      (fun i => (interpolate_continuous T (fun k => X k i)).continuousOn) = interpolateProduct X := by
  rw [curveSignature_eq_bvSignature]
  exact bvSignature_interpolate_product T X hT

/-- For every continuous curve on the compact interval, time-ordered samples
whose maximal gap tends to zero yield uniform polygonal approximation. -/
theorem interpolate_tendstoUniformlyOn_of_mesh {κ : Type*} {l : Filter κ}
    (N : κ → ℕ) (T : ∀ k, Fin (N k + 1) → ℝ) (hT : ∀ k, StrictMono (T k))
    (f : ℝ → ℝ) (a b : ℝ) (ha : ∀ k, T k 0 = a) (hb : ∀ k, T k (Fin.last (N k)) = b)
    (hf : ContinuousOn f (Icc a b))
    (hmesh : ∀ δ > 0, ∀ᶠ k in l, ∀ i : Fin (N k), T k i.succ - T k i.castSucc < δ) :
    TendstoUniformlyOn (fun k => interpolate (T k) (f ∘ T k)) f l (Icc a b) := by
  apply interpolate_tendstoUniformlyOn_of_oscillation N T hT f a b ha hb
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hf) ε hε
  filter_upwards [hmesh δ hδ] with k hk
  intro i t ht
  have hmem (j : Fin (N k + 1)) : T k j ∈ Icc a b := by
    rw [← ha k, ← hb k]
    exact ⟨(hT k).monotone (Fin.zero_le j), (hT k).monotone (Fin.le_last j)⟩
  have htm : t ∈ Icc a b := ⟨(hmem i.castSucc).1.trans ht.1, ht.2.trans (hmem i.succ).2⟩
  have hl : dist (T k i.castSucc) t < δ := by
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr ht.1)]
    exact (sub_le_sub_right ht.2 _).trans_lt (hk i)
  have hr : dist (T k i.succ) t < δ := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.2)]
    exact (sub_le_sub_left ht.1 _).trans_lt (hk i)
  exact ⟨by simpa only [Real.dist_eq] using (hclose _ (hmem i.castSucc) _ htm hl).le,
    by simpa only [Real.dist_eq] using (hclose _ (hmem i.succ) _ htm hr).le⟩

/-- The products of actual straight-edge signatures converge to the actual
BV signature whenever the corresponding time-ordered interpolants converge
uniformly. Uniform variation bounds are proved from sampling, not assumed. -/
theorem interpolateProduct_tendsto {ι κ : Type*} [Fintype ι] {l : Filter κ}
    (N : κ → ℕ) (T : ∀ k, Fin (N k + 1) → ℝ) (hT : ∀ k, StrictMono (T k))
    (f : ι → ℝ → ℝ) (hf : ∀ i, BoundedVariationOn (f i) univ) (hc : ∀ i, Continuous (f i))
    (a b : ℝ) (hab : a ≤ b) (ha : ∀ k, T k 0 = a) (hb : ∀ k, T k (Fin.last (N k)) = b)
    (hconv : ∀ i, TendstoUniformlyOn (fun k => interpolate (T k) (f i ∘ T k)) (f i) l (Icc a b)) :
    Tendsto (fun k => interpolateProduct (fun j i => f i (T k j))) l (𝓝 (bvSignature f hf hc a b)) := by
  let P := fun k i => interpolate (T k) (f i ∘ T k)
  have hP : ∀ k i, BoundedVariationOn (P k i) univ :=
    fun k i => interpolate_boundedVariation (T k) (f i ∘ T k) (hT k)
  have hPc : ∀ k i, Continuous (P k i) :=
    fun k i => interpolate_continuous (T k) (f i ∘ T k)
  let V := ∑ i, (eVariationOn (f i) (Icc a b)).toReal
  have hV : 0 ≤ V := Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)
  have hbound (k : κ) : (∑ i, (eVariationOn (P k i) (Icc a b)).toReal) + V ≤ 1 + 2 * V := by
    have hsum : (∑ i, (eVariationOn (P k i) (Icc a b)).toReal) ≤ V := by
      apply Finset.sum_le_sum
      intro i _
      have hi := interpolate_variation_le (T k) (hT k) (f i)
      rw [ha k, hb k] at hi
      exact ENNReal.toReal_mono ((hf i).mono (subset_univ _))
        ((eVariationOn.mono (P k i) (subset_univ _)).trans hi)
    linarith
  have h := bvSignature_tendsto_of_uniform_convergence P f hP hPc hf hc
    a b (1 + 2 * V) hab (by linarith) hbound hconv
  have he (k : κ) : bvSignature (P k) (hP k) (hPc k) a b =
      interpolateProduct (fun j i => f i (T k j)) := by
    have hk := bvSignature_interpolate_product (T k) (fun j i => f i (T k j)) (hT k)
    simpa only [ha k, hb k] using! hk
  simpa only [he] using h

theorem interpolateProduct_tendsto_of_mesh {ι κ : Type*} [Fintype ι] {l : Filter κ}
    (N : κ → ℕ) (T : ∀ k, Fin (N k + 1) → ℝ) (hT : ∀ k, StrictMono (T k))
    (f : ι → ℝ → ℝ) (hf : ∀ i, BoundedVariationOn (f i) univ) (hc : ∀ i, Continuous (f i))
    (a b : ℝ) (hab : a ≤ b) (ha : ∀ k, T k 0 = a) (hb : ∀ k, T k (Fin.last (N k)) = b)
    (hmesh : ∀ δ > 0, ∀ᶠ k in l, ∀ i : Fin (N k), T k i.succ - T k i.castSucc < δ) :
    Tendsto (fun k => interpolateProduct (fun j i => f i (T k j))) l (𝓝 (bvSignature f hf hc a b)) :=
  interpolateProduct_tendsto N T hT f hf hc a b hab ha hb
    (fun i => interpolate_tendstoUniformlyOn_of_mesh N T hT (f i) a b ha hb (hc i).continuousOn hmesh)

end LinearInputCurveWordPolygonal
