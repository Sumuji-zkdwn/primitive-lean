/-!
Deletion of an actual loop interval, followed by stopping at the original
terminal point. Geometry, variation, and signature preservation are proved
for the constructed curve, rather than assumed for a representative.
-/

noncomputable section

namespace LinearInputCurveWordBVLoopErase

open Set Real MeasureTheory
open scoped Topology

def tailClock (L s t u : ℝ) : ℝ := min L (u + (t - s))

def eraseLoop {E : Type*} (γ : ℝ → E) (L s t u : ℝ) : E :=
  if u ≤ s then γ u else γ (tailClock L s t u)

theorem tailClock_monotone (L s t : ℝ) : Monotone (tailClock L s t) := by
  intro u v huv
  exact min_le_min_left L (add_le_add huv le_rfl)

theorem tailClock_continuous (L s t : ℝ) : Continuous (tailClock L s t) :=
  continuous_const.min (continuous_id.add continuous_const)

theorem tailClock_lipschitz (L s t : ℝ) : LipschitzWith 1 (tailClock L s t) := by
  have hshift : LipschitzWith 1 (fun u : ℝ => u + (t - s)) := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    simp only [NNReal.coe_one, one_mul, dist_add_right]
    exact le_rfl
  exact hshift.const_min L

theorem tailClock_at_cut {L s t : ℝ} (ht : t ≤ L) : tailClock L s t s = t := by
  simp [tailClock, add_sub_cancel, min_eq_right ht]

theorem tailClock_mem {L s t u : ℝ} (ht : t ≤ L) (hu : s ≤ u) : tailClock L s t u ∈ Icc t L := by
  exact ⟨le_min ht (by linarith), min_le_left _ _⟩

theorem eraseLoop_before {E : Type*} (γ : ℝ → E) (L s t u : ℝ) (hu : u ≤ s) :
    eraseLoop γ L s t u = γ u := ite_eq_left hu

theorem eraseLoop_after {E : Type*} (γ : ℝ → E) {L s t u : ℝ}
    (ht : t ≤ L) (hloop : γ s = γ t) (hu : s ≤ u) :
    eraseLoop γ L s t u = γ (tailClock L s t u) := by
  by_cases hus : u ≤ s
  · have he : u = s := le_antisymm hus hu
    subst u
    rw [eraseLoop_before γ L s t s le_rfl, tailClock_at_cut ht]
    exact hloop
  · exact ite_eq_right hus

theorem eraseLoop_middle {E : Type*} (γ : ℝ → E) {L s t u : ℝ}
    (ht : t ≤ L) (hloop : γ s = γ t) (hu : u ∈ Icc s (L - (t - s))) :
    eraseLoop γ L s t u = γ (u + (t - s)) := by
  rw [eraseLoop_after γ ht hloop hu.1]
  unfold tailClock
  rw [min_eq_right (by linarith [hu.2])]

theorem eraseLoop_stopped {E : Type*} (γ : ℝ → E) {L s t u : ℝ}
    (ht : t ≤ L) (hloop : γ s = γ t) (hu : L - (t - s) ≤ u) :
    eraseLoop γ L s t u = γ L := by
  have hsu : s ≤ u := by linarith
  rw [eraseLoop_after γ ht hloop hsu]
  unfold tailClock
  rw [min_eq_left (by linarith)]

theorem eraseLoop_initial {E : Type*} (γ : ℝ → E) {L s t : ℝ} (hs : 0 ≤ s) :
    eraseLoop γ L s t 0 = γ 0 := eraseLoop_before γ L s t 0 hs

theorem eraseLoop_terminal {E : Type*} (γ : ℝ → E) {L s t : ℝ}
    (hst : s ≤ t) (ht : t ≤ L) (hloop : γ s = γ t) : eraseLoop γ L s t L = γ L :=
  eraseLoop_stopped γ ht hloop (by linarith)

theorem eraseLoop_lipschitz {E : Type*} [PseudoMetricSpace E] (γ : ℝ → E)
    (hγ : LipschitzWith 1 γ) {L s t : ℝ} (ht : t ≤ L) (hloop : γ s = γ t) :
    LipschitzWith 1 (eraseLoop γ L s t) := by
  have htail : LipschitzWith 1 (fun u => γ (tailClock L s t u)) := by
    simpa only [one_mul, Function.comp_apply] using! hγ.comp (tailClock_lipschitz L s t)
  have haux : ∀ x y : ℝ, x ≤ y → dist (eraseLoop γ L s t x) (eraseLoop γ L s t y) ≤ y - x := by
    intro x y hxy
    by_cases hy : y ≤ s
    · rw [eraseLoop_before γ L s t x (hxy.trans hy), eraseLoop_before γ L s t y hy]
      simpa only [NNReal.coe_one, one_mul, Real.dist_eq,
        abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub] using hγ.dist_le_mul x y
    · by_cases hx : x ≤ s
      · rw [eraseLoop_before γ L s t x hx, eraseLoop_after γ ht hloop (not_le.mp hy).le]
        have hdist1 := hγ.dist_le_mul x s
        have hdist2 := hγ.dist_le_mul t (tailClock L s t y)
        have hclock := tailClock_mem ht (not_le.mp hy).le
        simp only [NNReal.coe_one, one_mul, Real.dist_eq,
          abs_of_nonpos (sub_nonpos.mpr hx), neg_sub] at hdist1
        simp only [NNReal.coe_one, one_mul, Real.dist_eq,
          abs_of_nonpos (sub_nonpos.mpr hclock.1), neg_sub] at hdist2
        have htri := dist_triangle (γ x) (γ s) (γ (tailClock L s t y))
        rw [hloop] at htri
        rw [hloop] at hdist1
        have hle : tailClock L s t y ≤ y + (t - s) := min_le_right _ _
        linarith
      · rw [eraseLoop_after γ ht hloop (not_le.mp hx).le, eraseLoop_after γ ht hloop (not_le.mp hy).le]
        simpa only [NNReal.coe_one, one_mul, Real.dist_eq,
          abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub] using htail.dist_le_mul x y
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rcases le_total x y with hxy | hyx
  · simpa only [NNReal.coe_one, one_mul, Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub] using haux x y hxy
  · have h := haux y x hyx
    rw [dist_comm] at h
    simpa only [NNReal.coe_one, one_mul, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hyx)] using h

theorem lipschitz_boundedVariation {E : Type*} [PseudoMetricSpace E] (γ : ℝ → E)
    (hγ : LipschitzWith 1 γ) (a b : ℝ) : BoundedVariationOn γ (Icc a b) := by
  simpa only [univ_inter] using hγ.locallyBoundedVariationOn univ a b (mem_univ a) (mem_univ b)

theorem variation_shift {E : Type*} [PseudoEMetricSpace E] (γ : ℝ → E) (a b d : ℝ) :
    eVariationOn (fun u => γ (u + d)) (Icc a b) = eVariationOn γ (Icc (a + d) (b + d)) := by
  have hm : MonotoneOn (fun u : ℝ => u + d) univ := fun _ _ _ _ h => add_le_add h le_rfl
  have hs : (fun u : ℝ => u + d) '' univ = univ := by
    ext y
    simp only [mem_image, mem_univ, true_and, iff_true]
    exact ⟨y - d, by ring⟩
  simpa only [hs, univ_inter, Function.comp_apply] using!
    eVariationOn.comp_inter_Icc_eq_of_monotoneOn γ (fun u : ℝ => u + d) hm (mem_univ a) (mem_univ b)

/-- Deleting the loop removes exactly its variation. -/
theorem eraseLoop_variation_identity {E : Type*} [PseudoEMetricSpace E]
    (γ : ℝ → E) {L s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ L) (hloop : γ s = γ t) :
    eVariationOn (eraseLoop γ L s t) (Icc 0 L) + eVariationOn γ (Icc s t) = eVariationOn γ (Icc 0 L) := by
  let d := t - s
  have hcut : s ≤ L - d := by dsimp [d]; linarith
  have hstop : L - d ≤ L := by dsimp [d]; linarith
  have hfirst : eVariationOn (eraseLoop γ L s t) (Icc 0 s) = eVariationOn γ (Icc 0 s) :=
    eVariationOn.congr (fun u hu => eraseLoop_before γ L s t u hu.2)
  have hmiddle : eVariationOn (eraseLoop γ L s t) (Icc s (L - d)) = eVariationOn γ (Icc t L) := by
    rw [eVariationOn.congr (fun u hu => eraseLoop_middle γ ht hloop hu), variation_shift]
    have he1 : s + d = t := by dsimp [d]; ring
    have he2 : (L - d) + d = L := by ring
    rw [he1, he2]
  have hlast : eVariationOn (eraseLoop γ L s t) (Icc (L - d) L) = 0 := by
    apply (eVariationOn.eq_zero_iff _).mpr
    intro x hx y hy
    rw [eraseLoop_stopped γ ht hloop hx.1, eraseLoop_stopped γ ht hloop hy.1, edist_self]
  have he1 := eVariationOn.Icc_add_Icc (eraseLoop γ L s t) hs (hcut.trans hstop) (mem_univ s)
  have he2 := eVariationOn.Icc_add_Icc (eraseLoop γ L s t) hcut hstop (mem_univ (L - d))
  have hg1 := eVariationOn.Icc_add_Icc γ hs (hst.trans ht) (mem_univ s)
  have hg2 := eVariationOn.Icc_add_Icc γ hst ht (mem_univ t)
  simp only [univ_inter, hfirst, hmiddle, hlast, add_zero] at he1 he2 hg1 hg2
  rw [← he1, ← he2, ← hg1, ← hg2]
  ac_rfl

theorem eraseLoop_variation_strict {E : Type*} [PseudoMetricSpace E]
    (γ : ℝ → E) (hγ : LipschitzWith 1 γ) {L s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ L) (hloop : γ s = γ t)
    (hpositive : 0 < (eVariationOn γ (Icc s t)).toReal) :
    (eVariationOn (eraseLoop γ L s t) (Icc 0 L)).toReal < (eVariationOn γ (Icc 0 L)).toReal := by
  have h := congrArg ENNReal.toReal (eraseLoop_variation_identity γ hs hst ht hloop)
  rw [ENNReal.toReal_add (lipschitz_boundedVariation _ (eraseLoop_lipschitz γ hγ ht hloop) 0 L)
    (lipschitz_boundedVariation γ hγ s t)] at h
  linarith

theorem eraseLoop_variation_strict_of_nonconstant {E : Type*} [MetricSpace E]
    (γ : ℝ → E) (hγ : LipschitzWith 1 γ) {L s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ L) (hloop : γ s = γ t)
    (hne : ∃ u ∈ Icc s t, γ u ≠ γ s) :
    (eVariationOn (eraseLoop γ L s t) (Icc 0 L)).toReal < (eVariationOn γ (Icc 0 L)).toReal := by
  obtain ⟨u, hu, hune⟩ := hne
  have hd := (lipschitz_boundedVariation γ hγ s t).dist_le hu (left_mem_Icc.mpr hst)
  exact eraseLoop_variation_strict γ hγ hs hst ht hloop ((dist_pos.mpr hune).trans_le hd)

open LinearInputCurveWordBVCanonical LinearInputCurveWordFormalSeries
open LinearInputCurveWordBVPathOperations

def lipSignature {ι : Type*} [Fintype ι] (γ : ℝ → ι → ℝ) (hγ : LipschitzWith 1 γ)
    (a b : ℝ) (hab : a ≤ b) : Series ι :=
  pathSignature γ hab (lipschitz_boundedVariation γ hγ a b) hγ.continuous.continuousOn

theorem lipSignature_congr {ι : Type*} [Fintype ι]
    (γ η : ℝ → ι → ℝ) (hγ : LipschitzWith 1 γ) (hη : LipschitzWith 1 η)
    {a b : ℝ} (hab : a ≤ b) (he : EqOn γ η (Icc a b)) :
    lipSignature γ hγ a b hab = lipSignature η hη a b hab := by
  funext w
  exact pathSignature_congr hab _ _ _ _ he w

theorem lipSignature_endpoint_congr {ι : Type*} [Fintype ι]
    (γ : ℝ → ι → ℝ) (hγ : LipschitzWith 1 γ) {a b c : ℝ}
    (hab : a ≤ b) (hac : a ≤ c) (he : b = c) :
    lipSignature γ hγ a b hab = lipSignature γ hγ a c hac := by
  subst c
  rfl

theorem lipSignature_split {ι : Type*} [Fintype ι]
    (γ : ℝ → ι → ℝ) (hγ : LipschitzWith 1 γ) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    lipSignature γ hγ a c (hab.trans hbc) =
      product (lipSignature γ hγ a b hab) (lipSignature γ hγ b c hbc) :=
  pathSignature_split γ hab hbc (lipschitz_boundedVariation γ hγ a c) hγ.continuous.continuousOn

theorem lipSignature_reparametrize {ι : Type*} [Fintype ι]
    (γ : ℝ → ι → ℝ) (hγ : LipschitzWith 1 γ) (φ : ℝ → ℝ) (hφ : LipschitzWith 1 φ)
    (hm : Monotone φ) {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (ha : φ c = a) (hb : φ d = b) :
    lipSignature (γ ∘ φ) (by simpa only [one_mul] using hγ.comp hφ) c d hcd =
      lipSignature γ hγ a b hab :=
  pathSignature_reparametrize_endpoints γ hab hcd (hm.monotoneOn _) hφ.continuous.continuousOn ha hb
    (lipschitz_boundedVariation γ hγ a b) hγ.continuous.continuousOn

theorem eraseLoop_tail_signature {ι : Type*} [Fintype ι]
    (γ : ℝ → ι → ℝ) (hγ : LipschitzWith 1 γ) {L s t u : ℝ}
    (ht : t ≤ L) (hloop : γ s = γ t) (hu : s ≤ u) :
    lipSignature (eraseLoop γ L s t) (eraseLoop_lipschitz γ hγ ht hloop) s u hu =
      lipSignature γ hγ t (tailClock L s t u) (tailClock_mem ht hu).1 := by
  calc
    _ = lipSignature (γ ∘ tailClock L s t)
        (by simpa only [one_mul] using hγ.comp (tailClock_lipschitz L s t)) s u hu := by
      apply lipSignature_congr
      intro v hv
      exact eraseLoop_after γ ht hloop hv.1
    _ = _ := lipSignature_reparametrize γ hγ (tailClock L s t) (tailClock_lipschitz L s t)
      (tailClock_monotone L s t) (tailClock_mem ht hu).1 hu (tailClock_at_cut ht) rfl

def eraseClock (L s t u : ℝ) : ℝ := if u ≤ s then u else tailClock L s t u

theorem eraseClock_mem {L s t u : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ L)
    (hu : u ∈ Icc 0 L) : eraseClock L s t u ∈ Icc 0 L := by
  unfold eraseClock
  split_ifs with hus
  · exact hu
  · have hc := tailClock_mem ht (not_le.mp hus).le
    exact ⟨hs.trans (hst.trans hc.1), hc.2⟩

/-- Deleting a zero-signature loop preserves every prefix signature, with an
explicit time choice in the original interval, including the stopped tail. -/
theorem eraseLoop_prefix_signature {ι : Type*} [Fintype ι]
    (γ : ℝ → ι → ℝ) (hγ : LipschitzWith 1 γ) {L s t u : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ L) (hloop : γ s = γ t)
    (hzero : lipSignature γ hγ s t hst = unitSeries) (hu : u ∈ Icc 0 L) :
    lipSignature (eraseLoop γ L s t) (eraseLoop_lipschitz γ hγ ht hloop) 0 u hu.1 =
      lipSignature γ hγ 0 (eraseClock L s t u) (eraseClock_mem hs hst ht hu).1 := by
  by_cases hus : u ≤ s
  · have he : eraseClock L s t u = u := ite_eq_left hus
    exact (lipSignature_congr (eraseLoop γ L s t) γ
      (eraseLoop_lipschitz γ hγ ht hloop) hγ hu.1
      (fun v hv => eraseLoop_before γ L s t v (hv.2.trans hus))).trans
      (lipSignature_endpoint_congr γ hγ hu.1 (eraseClock_mem hs hst ht hu).1 he.symm)
  · have hsu : s ≤ u := (not_le.mp hus).le
    have he : eraseClock L s t u = tailClock L s t u := ite_eq_right hus
    have htu := (tailClock_mem ht hsu).1
    have hfirst : lipSignature (eraseLoop γ L s t) (eraseLoop_lipschitz γ hγ ht hloop) 0 s hs =
        lipSignature γ hγ 0 s hs :=
      lipSignature_congr _ _ _ _ hs (fun v hv => eraseLoop_before γ L s t v hv.2)
    have hwhole := lipSignature_split γ hγ hs (hst.trans htu)
    rw [lipSignature_split γ hγ hst htu, hzero, product_unit_left] at hwhole
    have hdel := lipSignature_split (eraseLoop γ L s t) (eraseLoop_lipschitz γ hγ ht hloop) hs hsu
    rw [hfirst, eraseLoop_tail_signature γ hγ ht hloop hsu, ← hwhole] at hdel
    exact hdel.trans (lipSignature_endpoint_congr γ hγ (hs.trans (hst.trans htu))
      (eraseClock_mem hs hst ht hu).1 he.symm)

theorem eraseClock_terminal (L s t : ℝ) (hst : s ≤ t) : eraseClock L s t L = L := by
  unfold eraseClock
  split_ifs
  · rfl
  · exact min_eq_left (by linarith)

theorem eraseLoop_signature {ι : Type*} [Fintype ι]
    (γ : ℝ → ι → ℝ) (hγ : LipschitzWith 1 γ) {L s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ L) (hloop : γ s = γ t)
    (hzero : lipSignature γ hγ s t hst = unitSeries) :
    lipSignature (eraseLoop γ L s t) (eraseLoop_lipschitz γ hγ ht hloop) 0 L (hs.trans (hst.trans ht)) =
      lipSignature γ hγ 0 L (hs.trans (hst.trans ht)) := by
  have h := eraseLoop_prefix_signature γ hγ hs hst ht hloop hzero ⟨hs.trans (hst.trans ht), le_rfl⟩
  exact h.trans (lipSignature_endpoint_congr γ hγ _ (hs.trans (hst.trans ht)) (eraseClock_terminal L s t hst))

/-- Every based prefix of the erased curve is an actual based prefix of the
original curve, hence any prescribed signature-image constraint is preserved. -/
theorem eraseLoop_based_prefix_mem {ι : Type*} [Fintype ι]
    (γ : ℝ → ι → ℝ) (hγ : LipschitzWith 1 γ) {L s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ L) (hloop : γ s = γ t)
    (hzero : lipSignature γ hγ s t hst = unitSeries) (P : Series ι) (K : Set (Series ι))
    (hK : ∀ u (hu : u ∈ Icc 0 L), product P (lipSignature γ hγ 0 u hu.1) ∈ K) :
    ∀ u (hu : u ∈ Icc 0 L),
      product P (lipSignature (eraseLoop γ L s t) (eraseLoop_lipschitz γ hγ ht hloop) 0 u hu.1) ∈ K := by
  intro u hu
  rw [eraseLoop_prefix_signature γ hγ hs hst ht hloop hzero hu]
  exact hK _ (eraseClock_mem hs hst ht hu)

/-- A nonconstant zero-signature loop gives a strictly shorter admissible
representative, with the same start and final signature and the same prescribed
based-prefix image constraint. The competitor is explicitly `eraseLoop`. -/
theorem exists_shorter_representative {ι : Type*} [Fintype ι]
    (γ : ℝ → ι → ℝ) (hγ : LipschitzWith 1 γ) {L s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ L) (hloop : γ s = γ t)
    (hzero : lipSignature γ hγ s t hst = unitSeries)
    (hne : ∃ u ∈ Icc s t, γ u ≠ γ s) (P : Series ι) (K : Set (Series ι))
    (hK : ∀ u (hu : u ∈ Icc 0 L), product P (lipSignature γ hγ 0 u hu.1) ∈ K) :
    ∃ (δ : ℝ → ι → ℝ) (hδ : LipschitzWith 1 δ),
      δ 0 = γ 0 ∧ δ L = γ L ∧
      lipSignature δ hδ 0 L (hs.trans (hst.trans ht)) = lipSignature γ hγ 0 L (hs.trans (hst.trans ht)) ∧
      (∀ u (hu : u ∈ Icc 0 L), product P (lipSignature δ hδ 0 u hu.1) ∈ K) ∧
      (eVariationOn δ (Icc 0 L)).toReal < (eVariationOn γ (Icc 0 L)).toReal := by
  refine ⟨eraseLoop γ L s t, eraseLoop_lipschitz γ hγ ht hloop,
    eraseLoop_initial γ hs, eraseLoop_terminal γ hst ht hloop,
    eraseLoop_signature γ hγ hs hst ht hloop hzero,
    eraseLoop_based_prefix_mem γ hγ hs hst ht hloop hzero P K hK, ?_⟩
  exact eraseLoop_variation_strict_of_nonconstant γ hγ hs hst ht hloop hne

end LinearInputCurveWordBVLoopErase
