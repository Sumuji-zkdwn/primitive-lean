/-!
Uniqueness of actual simple signature arcs. The topological construction first
extracts a real excursion of one arc outside the other arc's compact image.
Its two boundary intersections are actual attained times on both curves.
-/

noncomputable section

namespace LinearInputCurveWordBVArcUnique

open Set Real MeasureTheory
open scoped Topology

/-- An arc differing from another compact arc contains an open excursion
disjoint from that entire arc, with both endpoints attained on the other arc. -/
theorem exists_disjoint_arc_excursion {X : Type*} [TopologicalSpace X] [T2Space X]
    (A B : ℝ → X) (hA : Continuous A) (hB : Continuous B)
    {a b c d r : ℝ} (hcd : c ≤ d) (hr : r ∈ Icc a b)
    (hstart : A a = B c) (hend : A b = B d) (hinj : InjOn A (Icc a b))
    (hout : A r ∉ B '' Icc c d) :
    ∃ s t u v : ℝ, s ∈ Icc a r ∧ t ∈ Icc r b ∧ s < r ∧ r < t ∧
      u ∈ Icc c d ∧ v ∈ Icc c d ∧ A s = B u ∧ A t = B v ∧ u ≠ v ∧
      ∀ z ∈ Ioo s t, A z ∉ B '' Icc c d := by
  have hclosed : IsClosed (B '' Icc c d) := (isCompact_Icc.image hB).isClosed
  let S := Icc a r ∩ A ⁻¹' (B '' Icc c d)
  let T := Icc r b ∩ A ⁻¹' (B '' Icc c d)
  have hS : IsCompact S := isCompact_Icc.inter_right (hclosed.preimage hA)
  have hT : IsCompact T := isCompact_Icc.inter_right (hclosed.preimage hA)
  have haS : a ∈ S := ⟨⟨le_rfl, hr.1⟩, ⟨c, ⟨le_rfl, hcd⟩, hstart.symm⟩⟩
  have hbT : b ∈ T := ⟨⟨hr.2, le_rfl⟩, ⟨d, ⟨hcd, le_rfl⟩, hend.symm⟩⟩
  obtain ⟨s, hs, hsmax⟩ := hS.exists_isMaxOn ⟨a, haS⟩ (show ContinuousOn (fun x : ℝ => x) S from continuousOn_id)
  obtain ⟨t, ht, htmin⟩ := hT.exists_isMinOn ⟨b, hbT⟩ (show ContinuousOn (fun x : ℝ => x) T from continuousOn_id)
  have hsr : s < r := lt_of_le_of_ne hs.1.2 (by intro he; subst s; exact hout hs.2)
  have hrt : r < t := lt_of_le_of_ne ht.1.1 (by intro he; subst t; exact hout ht.2)
  obtain ⟨u, hu, hus⟩ := hs.2
  obtain ⟨v, hv, hvt⟩ := ht.2
  refine ⟨s, t, u, v, hs.1, ht.1, hsr, hrt, hu, hv, hus.symm, hvt.symm, ?_, ?_⟩
  · intro huv
    have hst : s = t := hinj ⟨hs.1.1, hs.1.2.trans hr.2⟩ ⟨hr.1.trans ht.1.1, ht.1.2⟩
      (hus.symm.trans (huv ▸ hvt))
    linarith
  · intro z hz hzB
    by_cases hzr : z ≤ r
    · have hzS : z ∈ S := ⟨⟨hs.1.1.trans hz.1.le, hzr⟩, hzB⟩
      have hzs := hsmax hzS
      exact (not_le.mpr hz.1) hzs
    · have hzT : z ∈ T := ⟨⟨(not_le.mp hzr).le, hz.2.le.trans ht.1.2⟩, hzB⟩
      have htz := htmin hzT
      exact (not_le.mpr hz.2) htz

def arcParameter (a b u : ℝ) : ℝ := a + u * (b - a)

theorem arcParameter_continuous (a b : ℝ) : Continuous (arcParameter a b) :=
  continuous_const.add (continuous_id.mul continuous_const)

theorem arcParameter_zero (a b : ℝ) : arcParameter a b 0 = a := by simp [arcParameter]

theorem arcParameter_one (a b : ℝ) : arcParameter a b 1 = b := by simp [arcParameter]

theorem arcParameter_mem {a b u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) : arcParameter a b u ∈ uIcc a b := by
  rcases le_total a b with hab | hba
  · rw [uIcc_of_le hab]
    dsimp [arcParameter]
    constructor
    · nlinarith [mul_nonneg hu.1 (sub_nonneg.mpr hab)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hu.2) (sub_nonneg.mpr hab)]
  · rw [uIcc_of_ge hba]
    dsimp [arcParameter]
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr hu.2) (sub_nonneg.mpr hba)]
    · nlinarith [mul_nonneg hu.1 (sub_nonneg.mpr hba)]

theorem arcParameter_injective {a b : ℝ} (hab : a ≠ b) : Function.Injective (arcParameter a b) := by
  intro u v huv
  dsimp [arcParameter] at huv
  exact (mul_right_cancel₀ (sub_ne_zero.mpr hab.symm)) (add_left_cancel huv)

def twoArcLoop {X : Type*} (A B : ℝ → X) (s t u v z : ℝ) : X :=
  if z ≤ 1 then A (arcParameter s t z) else B (arcParameter v u (z - 1))

theorem twoArcLoop_left {X : Type*} (A B : ℝ → X) (s t u v z : ℝ) (hz : z ≤ 1) :
    twoArcLoop A B s t u v z = A (arcParameter s t z) := if_pos hz

theorem twoArcLoop_right {X : Type*} (A B : ℝ → X) (s t u v z : ℝ)
    (hmatch : A t = B v) (hz : 1 ≤ z) :
    twoArcLoop A B s t u v z = B (arcParameter v u (z - 1)) := by
  by_cases he : z ≤ 1
  · have hz1 : z = 1 := le_antisymm he hz
    subst z
    simp only [twoArcLoop, le_refl, if_true, arcParameter_one, sub_self, arcParameter_zero]
    exact hmatch
  · exact if_neg he

theorem twoArcLoop_continuous {X : Type*} [TopologicalSpace X]
    (A B : ℝ → X) (hA : Continuous A) (hB : Continuous B) (s t u v : ℝ)
    (hmatch : A t = B v) : Continuous (twoArcLoop A B s t u v) := by
  apply Continuous.if_le (hA.comp (arcParameter_continuous s t))
    (hB.comp ((arcParameter_continuous v u).comp (continuous_id.sub continuous_const)))
    continuous_id continuous_const
  intro z hz
  change z = 1 at hz
  subst z
  change A (arcParameter s t 1) = B (arcParameter v u (1 - 1))
  simpa only [arcParameter_one, sub_self, arcParameter_zero] using hmatch

theorem twoArcLoop_closed {X : Type*} (A B : ℝ → X) (s t u v : ℝ)
    (hstart : A s = B u) (hmatch : A t = B v) :
    twoArcLoop A B s t u v 0 = twoArcLoop A B s t u v 2 := by
  rw [twoArcLoop_left A B s t u v 0 (by norm_num),
    twoArcLoop_right A B s t u v 2 hmatch (by norm_num)]
  norm_num only [arcParameter_zero, show (2 : ℝ) - 1 = 1 by norm_num, arcParameter_one]
  exact hstart

theorem arcParameter_in_ambient {a b c d z : ℝ} (hc : c ∈ Icc a b) (hd : d ∈ Icc a b)
    (hz : z ∈ Icc (0 : ℝ) 1) : arcParameter c d z ∈ Icc a b := by
  have hp := arcParameter_mem (a := c) (b := d) hz
  exact ⟨(le_min hc.1 hd.1).trans hp.1, hp.2.trans (max_le hc.2 hd.2)⟩

/-- The two reparametrized arcs can meet only at their two glued endpoints. -/
theorem disjoint_excursion_crossing {X : Type*}
    (A B : ℝ → X) {c d s t u v x y : ℝ} (hst : s < t)
    (hu : u ∈ Icc c d) (hv : v ∈ Icc c d) (huv : u ≠ v)
    (hBinj : InjOn B (Icc c d)) (hstart : A s = B u) (hmatch : A t = B v)
    (hdis : ∀ z ∈ Ioo s t, A z ∉ B '' Icc c d)
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (1 : ℝ) 2)
    (he : A (arcParameter s t x) = B (arcParameter v u (y - 1))) :
    (x = 0 ∧ y = 2) ∨ (x = 1 ∧ y = 1) := by
  have hym : y - 1 ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hy.1, hy.2]
  have hBmem := arcParameter_in_ambient hv hu hym
  by_cases hx0 : x = 0
  · left
    refine ⟨hx0, ?_⟩
    rw [hx0, arcParameter_zero, hstart] at he
    have hp := hBinj hu hBmem he
    have hz : (1 : ℝ) = y - 1 := (arcParameter_injective huv.symm)
      ((arcParameter_one v u).trans hp)
    linarith
  · by_cases hx1 : x = 1
    · right
      refine ⟨hx1, ?_⟩
      rw [hx1, arcParameter_one, hmatch] at he
      have hp := hBinj hv hBmem he
      have hz : (0 : ℝ) = y - 1 := (arcParameter_injective huv.symm)
        ((arcParameter_zero v u).trans hp)
      linarith
    · have hxi : 0 < x ∧ x < 1 := ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), lt_of_le_of_ne hx.2 hx1⟩
      have hparam : arcParameter s t x ∈ Ioo s t := by
        dsimp [arcParameter]
        constructor <;> nlinarith [mul_pos hxi.1 (sub_pos.mpr hst),
          mul_pos (sub_pos.mpr hxi.2) (sub_pos.mpr hst)]
      exact False.elim (hdis _ hparam ⟨_, hBmem, he.symm⟩)

/-- An excursion disjoint from the other arc produces a genuine simple
closed loop: the only repeated points are its two overall endpoints. -/
theorem twoArcLoop_simple {X : Type*} (A B : ℝ → X)
    {a b c d s t u v : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s < t)
    (hu : u ∈ Icc c d) (hv : v ∈ Icc c d) (huv : u ≠ v)
    (hAinj : InjOn A (Icc a b)) (hBinj : InjOn B (Icc c d))
    (hstart : A s = B u) (hmatch : A t = B v)
    (hdis : ∀ z ∈ Ioo s t, A z ∉ B '' Icc c d) :
    ∀ x ∈ Icc (0 : ℝ) 2, ∀ y ∈ Icc (0 : ℝ) 2,
      twoArcLoop A B s t u v x = twoArcLoop A B s t u v y →
      x = y ∨ (x = 0 ∧ y = 2) ∨ (x = 2 ∧ y = 0) := by
  intro x hx y hy he
  by_cases hx1 : x ≤ 1
  · by_cases hy1 : y ≤ 1
    · left
      rw [twoArcLoop_left A B s t u v x hx1, twoArcLoop_left A B s t u v y hy1] at he
      exact arcParameter_injective hst.ne (hAinj (arcParameter_in_ambient hs ht ⟨hx.1, hx1⟩)
        (arcParameter_in_ambient hs ht ⟨hy.1, hy1⟩) he)
    · rw [twoArcLoop_left A B s t u v x hx1,
        twoArcLoop_right A B s t u v y hmatch (not_le.mp hy1).le] at he
      rcases disjoint_excursion_crossing A B hst hu hv huv hBinj hstart hmatch hdis
        ⟨hx.1, hx1⟩ ⟨(not_le.mp hy1).le, hy.2⟩ he with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl (h.1.trans h.2.symm)
  · by_cases hy1 : y ≤ 1
    · rw [twoArcLoop_right A B s t u v x hmatch (not_le.mp hx1).le,
        twoArcLoop_left A B s t u v y hy1] at he
      rcases disjoint_excursion_crossing A B hst hu hv huv hBinj hstart hmatch hdis
        ⟨hy.1, hy1⟩ ⟨(not_le.mp hx1).le, hx.2⟩ he.symm with h | h
      · exact Or.inr (Or.inr ⟨h.2, h.1⟩)
      · exact Or.inl (h.2.trans h.1.symm)
    · left
      rw [twoArcLoop_right A B s t u v x hmatch (not_le.mp hx1).le,
        twoArcLoop_right A B s t u v y hmatch (not_le.mp hy1).le] at he
      have hxm : x - 1 ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hx.2]
      have hym : y - 1 ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hy.2]
      have hp := hBinj (arcParameter_in_ambient hv hu hxm) (arcParameter_in_ambient hv hu hym) he
      have hz := arcParameter_injective huv.symm hp
      linarith

open LinearInputCurveWordBVCanonical LinearInputCurveWordBVPathOperations
open LinearInputCurveWordBVOrientation LinearInputCurveWordStieltjes
open LinearInputCurveWordFormalSeries LinearInputCurveWordBVAlgebra

theorem product_left_injective {ι : Type*} (P : Series ι) (hP : P [] = 1) :
    Function.Injective (product P) := by
  intro F G he
  have hw : ∀ n : ℕ, ∀ w : List ι, w.length = n → F w = G w := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro w hlen
      have hew := congrFun he w
      unfold product at hew
      rw [Finset.sum_range_succ', Finset.sum_range_succ'] at hew
      simp only [List.take_zero, List.drop_zero, hP, one_mul] at hew
      have hrest : (∑ k ∈ Finset.range w.length, P (w.take (k + 1)) * F (w.drop (k + 1))) =
          ∑ k ∈ Finset.range w.length, P (w.take (k + 1)) * G (w.drop (k + 1)) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hlt : (w.drop (k + 1)).length < n := by
          simp only [List.length_drop]
          have := Finset.mem_range.mp hk
          omega
        rw [ih _ hlt _ rfl]
      linarith
  funext w
  exact hw w.length w rfl

theorem shiftedArcParameter_oriented (u v k c d : ℝ) :
    MonotoneOn (fun z => arcParameter u v (z - k)) (Icc c d) ∨
      AntitoneOn (fun z => arcParameter u v (z - k)) (Icc c d) := by
  rcases le_total u v with huv | hvu
  · left
    intro x _ y _ hxy
    dsimp [arcParameter]
    nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr huv)]
  · right
    intro x _ y _ hxy
    dsimp [arcParameter]
    nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hvu)]

theorem twoArcLoop_boundedVariation {E : Type*} [PseudoEMetricSpace E]
    (γ η : ℝ → E) {a b c d s t u v : ℝ}
    (hγ : BoundedVariationOn γ (Icc a b)) (hη : BoundedVariationOn η (Icc c d))
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    (hu : u ∈ Icc c d) (hv : v ∈ Icc c d) (he : γ t = η v) :
    BoundedVariationOn (twoArcLoop γ η s t u v) (Icc 0 2) := by
  have hleft : BoundedVariationOn (γ ∘ arcParameter s t) (Icc (0 : ℝ) 1) := by
    apply oriented_comp_boundedVariation hγ
    · simpa only [sub_zero] using shiftedArcParameter_oriented s t 0 0 1
    · exact fun _ hz => arcParameter_in_ambient hs ht hz
  have hright : BoundedVariationOn (η ∘ fun z => arcParameter v u (z - 1)) (Icc (1 : ℝ) 2) := by
    apply oriented_comp_boundedVariation hη (shiftedArcParameter_oriented v u 1 1 2)
    intro z hz
    apply arcParameter_in_ambient hv hu
    constructor <;> linarith [hz.1, hz.2]
  apply joinCurve_boundedVariation (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 2) _ hleft hright
  simpa only [Function.comp_apply, arcParameter_one, sub_self, arcParameter_zero] using he

/-- Joining actual reparametrized pieces realizes exactly the joined based
signature arcs, at every intermediate time. -/
theorem twoArcLoop_signature {ι : Type*} [Fintype ι]
    (γ η : ℝ → ι → ℝ) (p m q n : ι → StieltjesFunction ℝ)
    (hp : ∀ i, Continuous (p i : ℝ → ℝ)) (hm : ∀ i, Continuous (m i : ℝ → ℝ))
    (hq : ∀ i, Continuous (q i : ℝ → ℝ)) (hn : ∀ i, Continuous (n i : ℝ → ℝ))
    (P : Series ι) {a b c d s t u v : ℝ}
    (hγ : BoundedVariationOn γ (Icc a b)) (hη : BoundedVariationOn η (Icc c d))
    (hcγ : Continuous γ) (hcη : Continuous η)
    (hrepγ : ∀ i, RepresentsOn (p i) (m i) (fun r => γ r i) a b)
    (hrepη : ∀ i, RepresentsOn (q i) (n i) (fun r => η r i) c d)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    (hu : u ∈ Icc c d) (hv : v ∈ Icc c d) (he : γ t = η v)
    (hmatch : product P (stieltjesSignature p m a t) = product P (stieltjesSignature q n c v))
    {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 2) :
    product (product P (stieltjesSignature p m a s))
      (pathSignature (twoArcLoop γ η s t u v) hz.1
        ((twoArcLoop_boundedVariation γ η hγ hη hs ht hu hv he).mono (Icc_subset_Icc le_rfl hz.2))
        ((twoArcLoop_continuous γ η hcγ hcη s t u v he).continuousOn)) =
      twoArcLoop (fun r => product P (stieltjesSignature p m a r))
        (fun r => product P (stieltjesSignature q n c r)) s t u v z := by
  let κ := twoArcLoop γ η s t u v
  have hκ := twoArcLoop_boundedVariation γ η hγ hη hs ht hu hv he
  have hcκ := twoArcLoop_continuous γ η hcγ hcη s t u v he
  have hleft (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
      pathSignature κ hr.1 (hκ.mono (Icc_subset_Icc le_rfl (hr.2.trans (by norm_num))))
        hcκ.continuousOn = stieltjesSignature p m s (arcParameter s t r) := by
    have hmap : MapsTo (arcParameter s t) (Icc 0 r) (Icc a b) :=
      fun z hz => arcParameter_in_ambient hs ht ⟨hz.1, hz.2.trans hr.2⟩
    have ho : MonotoneOn (arcParameter s t) (Icc 0 r) ∨ AntitoneOn (arcParameter s t) (Icc 0 r) := by
      simpa only [sub_zero] using shiftedArcParameter_oriented s t 0 0 r
    have hsige := pathSignature_oriented_reparametrize γ p m hp hm hr.1 hγ hcγ.continuousOn
      hrepγ ho (arcParameter_continuous s t).continuousOn hmap
    have heq : pathSignature κ hr.1 (hκ.mono (Icc_subset_Icc le_rfl (hr.2.trans (by norm_num))))
        hcκ.continuousOn = pathSignature (γ ∘ arcParameter s t) hr.1
        (oriented_comp_boundedVariation hγ ho hmap) (hcγ.comp (arcParameter_continuous s t)).continuousOn := by
      funext w
      exact pathSignature_congr hr.1 _ _ _ _ (fun z hz => twoArcLoop_left γ η s t u v z (hz.2.trans hr.2)) w
    exact heq.trans (by simpa only [arcParameter_zero] using hsige)
  by_cases hz1 : z ≤ 1
  · rw [twoArcLoop_left _ _ s t u v z hz1, hleft z ⟨hz.1, hz1⟩, product_assoc,
      ← LinearInputCurveWordBVAlgebra.signature_product p m hp hm a s (arcParameter s t z)]
  · have h1z : 1 ≤ z := (not_le.mp hz1).le
    have hmap : MapsTo (fun r => arcParameter v u (r - 1)) (Icc 1 z) (Icc c d) := by
      intro r hr
      apply arcParameter_in_ambient hv hu
      constructor <;> linarith [hr.1, hr.2, hz.2]
    have ho := shiftedArcParameter_oriented v u 1 1 z
    have hsige := pathSignature_oriented_reparametrize η q n hq hn h1z hη hcη.continuousOn hrepη ho
      ((arcParameter_continuous v u).comp (continuous_id.sub continuous_const)).continuousOn hmap
    have hright : pathSignature κ h1z (hκ.mono (Icc_subset_Icc (by norm_num) hz.2)) hcκ.continuousOn =
        stieltjesSignature q n v (arcParameter v u (z - 1)) := by
      have heq : pathSignature κ h1z (hκ.mono (Icc_subset_Icc (by norm_num) hz.2)) hcκ.continuousOn =
          pathSignature (η ∘ fun r => arcParameter v u (r - 1)) h1z
          (oriented_comp_boundedVariation hη ho hmap)
          (hcη.comp ((arcParameter_continuous v u).comp (continuous_id.sub continuous_const))).continuousOn := by
        funext w
        exact pathSignature_congr h1z _ _ _ _ (fun r hr => twoArcLoop_right γ η s t u v r he hr.1) w
      exact heq.trans (by simpa only [sub_self, arcParameter_zero] using hsige)
    rw [twoArcLoop_right _ _ s t u v z hmatch h1z,
      pathSignature_split κ (by norm_num : (0 : ℝ) ≤ 1) h1z, hleft 1 ⟨by norm_num, le_rfl⟩,
      arcParameter_one, hright, ← product_assoc, product_assoc P,
      ← LinearInputCurveWordBVAlgebra.signature_product p m hp hm a s t,
      hmatch, product_assoc, ← LinearInputCurveWordBVAlgebra.signature_product q n hq hn c v]

open LinearInputCurveWordBVSubinterval LinearInputCurveWordBVTopology

theorem represented_signature_singleton {ι : Type*} (γ : ℝ → ι → ℝ)
    (p m : ι → StieltjesFunction ℝ) {a b r : ℝ}
    (hrep : ∀ i, RepresentsOn (p i) (m i) (fun t => γ t i) a b)
    (hr : r ∈ Icc a b) (i : ι) : stieltjesSignature p m a r [i] = γ r i - γ a i := by
  change stieltjesIntegral (p i) (m i) a r (fun _ => 1) = _
  rw [stieltjesIntegral_one _ _ hr.1]
  exact hrep i a ⟨le_rfl, hr.1.trans hr.2⟩ r hr

theorem represented_lift_point_eq {ι : Type*}
    (γ η : ℝ → ι → ℝ) (p m q n : ι → StieltjesFunction ℝ)
    (P : Series ι) (hP : P [] = 1) {a b c d s t : ℝ}
    (hrepγ : ∀ i, RepresentsOn (p i) (m i) (fun r => γ r i) a b)
    (hrepη : ∀ i, RepresentsOn (q i) (n i) (fun r => η r i) c d)
    (hbase : γ a = η c) (hs : s ∈ Icc a b) (ht : t ∈ Icc c d)
    (he : product P (stieltjesSignature p m a s) = product P (stieltjesSignature q n c t)) :
    γ s = η t := by
  have hsig := product_left_injective P hP he
  funext i
  have hi := congrFun hsig [i]
  rw [represented_signature_singleton γ p m hrepγ hs,
    represented_signature_singleton η q n hrepη ht] at hi
  have h0 := congrFun hbase i
  linarith

theorem represented_lift_continuous {ι : Type*} (P : Series ι)
    (p m : ι → StieltjesFunction ℝ)
    (hp : ∀ i, Continuous (p i : ℝ → ℝ)) (hm : ∀ i, Continuous (m i : ℝ → ℝ)) (a : ℝ) :
    Continuous (fun t => product P (stieltjesSignature p m a t)) := by
  apply continuous_pi
  intro w
  apply continuous_finset_sum
  intro k _
  exact continuous_const.mul ((continuous_apply (w.drop k)).comp (signature_lift_continuous hp hm a))

/-- Two actual simple signature arcs with the same endpoints have the same
image. The proof constructs a genuine BV simple closed loop from any alleged
excursion, and contradicts the analytic no-simple-signature-loop theorem. -/
theorem represented_injective_signature_image_subset {ι : Type*} [Fintype ι]
    (γ η : ℝ → ι → ℝ) (p m q n : ι → StieltjesFunction ℝ)
    (hp : ∀ i, Continuous (p i : ℝ → ℝ)) (hm : ∀ i, Continuous (m i : ℝ → ℝ))
    (hq : ∀ i, Continuous (q i : ℝ → ℝ)) (hn : ∀ i, Continuous (n i : ℝ → ℝ))
    (P : Series ι) (hP : P [] = 1) {a b c d : ℝ} (_hab : a ≤ b) (hcd : c ≤ d)
    (hγ : BoundedVariationOn γ (Icc a b)) (hη : BoundedVariationOn η (Icc c d))
    (hcγ : Continuous γ) (hcη : Continuous η)
    (hrepγ : ∀ i, RepresentsOn (p i) (m i) (fun r => γ r i) a b)
    (hrepη : ∀ i, RepresentsOn (q i) (n i) (fun r => η r i) c d)
    (hbase : γ a = η c)
    (hAinj : InjOn (fun r => product P (stieltjesSignature p m a r)) (Icc a b))
    (hBinj : InjOn (fun r => product P (stieltjesSignature q n c r)) (Icc c d))
    (hend : product P (stieltjesSignature p m a b) = product P (stieltjesSignature q n c d)) :
    (fun r => product P (stieltjesSignature p m a r)) '' Icc a b ⊆
      (fun r => product P (stieltjesSignature q n c r)) '' Icc c d := by
  rintro _ ⟨r, hr, rfl⟩
  by_contra hout
  let A := fun r => product P (stieltjesSignature p m a r)
  let B := fun r => product P (stieltjesSignature q n c r)
  have hstart : A a = B c := by
    dsimp [A, B]
    rw [LinearInputCurveWordBVPathOperations.stieltjesSignature_same,
      LinearInputCurveWordBVPathOperations.stieltjesSignature_same]
  obtain ⟨s, t, u, v, hs, ht, hsr, hrt, hu, hv, has, hat, huv, hdis⟩ :=
    exists_disjoint_arc_excursion A B (represented_lift_continuous P p m hp hm a)
      (represented_lift_continuous P q n hq hn c) hcd hr hstart hend hAinj hout
  have hsmem : s ∈ Icc a b := ⟨hs.1, hs.2.trans hr.2⟩
  have htmem : t ∈ Icc a b := ⟨hr.1.trans ht.1, ht.2⟩
  have hst : s < t := hsr.trans hrt
  have hematch : γ t = η v := represented_lift_point_eq γ η p m q n P hP
    hrepγ hrepη hbase htmem hv hat
  let κ := twoArcLoop γ η s t u v
  have hκ := twoArcLoop_boundedVariation γ η hγ hη hsmem htmem hu hv hematch
  have hcκ := twoArcLoop_continuous γ η hcγ hcη s t u v hematch
  let pk (i : ι) := canonicalPositive (by norm_num : (0 : ℝ) ≤ 2)
    (coordinate_boundedVariation hκ i) (coordinate_continuousOn hcκ.continuousOn i)
  let mk (i : ι) := canonicalNegative (by norm_num : (0 : ℝ) ≤ 2)
    (coordinate_boundedVariation hκ i) (coordinate_continuousOn hcκ.continuousOn i)
  have hpk (i : ι) : Continuous (pk i : ℝ → ℝ) := canonicalPositive_continuous _ _ _
  have hmk (i : ι) : Continuous (mk i : ℝ → ℝ) := canonicalNegative_continuous _ _ _
  have hcanonical (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 2) :
      pathSignature κ hz.1 (hκ.mono (Icc_subset_Icc le_rfl hz.2)) hcκ.continuousOn =
        stieltjesSignature pk mk 0 z := by
    funext w
    apply pathSignature_eq_representation κ hz.1 _ _ pk mk hpk hmk _ w
    intro i x hx y hy
    exact canonical_represents (by norm_num) (coordinate_boundedVariation hκ i)
      (coordinate_continuousOn hcκ.continuousOn i) x ⟨hx.1, hx.2.trans hz.2⟩ y ⟨hy.1, hy.2.trans hz.2⟩
  have hlift (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 2) :
      product (A s) (stieltjesSignature pk mk 0 z) = twoArcLoop A B s t u v z := by
    have hh := twoArcLoop_signature γ η p m q n hp hm hq hn P hγ hη hcγ hcη hrepγ hrepη
      hsmem htmem hu hv hematch hat hz
    rw [hcanonical z hz] at hh
    exact hh
  have hR : A s [] = 1 := by
    change product P (stieltjesSignature p m a s) [] = 1
    rw [LinearInputCurveWordFormalSeries.product_empty, hP, one_mul]
    rfl
  have hunit : stieltjesSignature pk mk 0 2 = unitSeries := by
    apply product_left_injective (A s) hR
    rw [hlift 2 ⟨by norm_num, le_rfl⟩,
      twoArcLoop_right A B s t u v 2 hat (by norm_num), product_unit_right]
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num, arcParameter_one] using has.symm
  apply signature_lift_not_simple_loop pk mk hpk hmk (by norm_num : (0 : ℝ) < 2)
    (fun w hw => by rw [hunit]; cases w <;> simp_all [unitSeries])
  intro x hx y hy he
  apply twoArcLoop_simple A B hsmem htmem hst hu hv huv hAinj hBinj has hat hdis x hx y hy
  rw [← hlift x hx, ← hlift y hy, he]

theorem represented_injective_signature_images_eq {ι : Type*} [Fintype ι]
    (γ η : ℝ → ι → ℝ) (p m q n : ι → StieltjesFunction ℝ)
    (hp : ∀ i, Continuous (p i : ℝ → ℝ)) (hm : ∀ i, Continuous (m i : ℝ → ℝ))
    (hq : ∀ i, Continuous (q i : ℝ → ℝ)) (hn : ∀ i, Continuous (n i : ℝ → ℝ))
    (P : Series ι) (hP : P [] = 1) {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hγ : BoundedVariationOn γ (Icc a b)) (hη : BoundedVariationOn η (Icc c d))
    (hcγ : Continuous γ) (hcη : Continuous η)
    (hrepγ : ∀ i, RepresentsOn (p i) (m i) (fun r => γ r i) a b)
    (hrepη : ∀ i, RepresentsOn (q i) (n i) (fun r => η r i) c d)
    (hbase : γ a = η c)
    (hAinj : InjOn (fun r => product P (stieltjesSignature p m a r)) (Icc a b))
    (hBinj : InjOn (fun r => product P (stieltjesSignature q n c r)) (Icc c d))
    (hend : product P (stieltjesSignature p m a b) = product P (stieltjesSignature q n c d)) :
    (fun r => product P (stieltjesSignature p m a r)) '' Icc a b =
      (fun r => product P (stieltjesSignature q n c r)) '' Icc c d := by
  apply Set.Subset.antisymm
  · exact represented_injective_signature_image_subset γ η p m q n hp hm hq hn P hP hab hcd
      hγ hη hcγ hcη hrepγ hrepη hbase hAinj hBinj hend
  · exact represented_injective_signature_image_subset η γ q n p m hq hn hp hm P hP hcd hab
      hη hγ hcη hcγ hrepη hrepγ hbase.symm hBinj hAinj hend.symm

open LinearInputCurveWordBVLoopErase

theorem exists_lipSignature_representation {ι : Type*} [Fintype ι]
    (γ : ℝ → ι → ℝ) (hγ : LipschitzWith 1 γ) {L : ℝ} (hL : 0 ≤ L) :
    ∃ p m : ι → StieltjesFunction ℝ,
      (∀ i, Continuous (p i : ℝ → ℝ)) ∧ (∀ i, Continuous (m i : ℝ → ℝ)) ∧
      (∀ i, RepresentsOn (p i) (m i) (fun r => γ r i) 0 L) ∧
      ∀ r ∈ Icc 0 L, ∀ hr : 0 ≤ r, lipSignature γ hγ 0 r hr = stieltjesSignature p m 0 r := by
  have hBV := lipschitz_boundedVariation γ hγ 0 L
  let p (i : ι) := canonicalPositive hL (coordinate_boundedVariation hBV i)
    (coordinate_continuousOn hγ.continuous.continuousOn i)
  let m (i : ι) := canonicalNegative hL (coordinate_boundedVariation hBV i)
    (coordinate_continuousOn hγ.continuous.continuousOn i)
  have hp (i : ι) : Continuous (p i : ℝ → ℝ) := canonicalPositive_continuous _ _ _
  have hm (i : ι) : Continuous (m i : ℝ → ℝ) := canonicalNegative_continuous _ _ _
  have hrep (i : ι) : RepresentsOn (p i) (m i) (fun r => γ r i) 0 L := canonical_represents _ _ _
  refine ⟨p, m, hp, hm, hrep, ?_⟩
  intro r hr h0r
  funext w
  exact pathSignature_eq_representation γ h0r _ _ p m hp hm
    (fun i x hx y hy => hrep i x ⟨hx.1, hx.2.trans hr.2⟩ y ⟨hy.1, hy.2.trans hr.2⟩) w

/-- The directly usable arc-uniqueness API for the actual arclength
representatives. Degenerate intervals are included. -/
theorem injective_lipSignature_ranges_eq {ι : Type*} [Fintype ι]
    (γ η : ℝ → ι → ℝ) (hγ : LipschitzWith 1 γ) (hη : LipschitzWith 1 η)
    {L M : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M) (P : Series ι) (hP : P [] = 1)
    (hbase : γ 0 = η 0)
    (hAinj : Function.Injective (fun r : Icc (0 : ℝ) L => product P (lipSignature γ hγ 0 r.val r.property.1)))
    (hBinj : Function.Injective (fun r : Icc (0 : ℝ) M => product P (lipSignature η hη 0 r.val r.property.1)))
    (hend : product P (lipSignature γ hγ 0 L hL) = product P (lipSignature η hη 0 M hM)) :
    Set.range (fun r : Icc (0 : ℝ) L => product P (lipSignature γ hγ 0 r.val r.property.1)) =
      Set.range (fun r : Icc (0 : ℝ) M => product P (lipSignature η hη 0 r.val r.property.1)) := by
  obtain ⟨p, m, hp, hm, hrepγ, hsigγ⟩ := exists_lipSignature_representation γ hγ hL
  obtain ⟨q, n, hq, hn, hrepη, hsigη⟩ := exists_lipSignature_representation η hη hM
  have hAi : InjOn (fun r => product P (stieltjesSignature p m 0 r)) (Icc 0 L) := by
    intro x hx y hy he
    have hh : product P (lipSignature γ hγ 0 x hx.1) = product P (lipSignature γ hγ 0 y hy.1) := by
      rwa [hsigγ x hx hx.1, hsigγ y hy hy.1]
    exact congrArg Subtype.val (hAinj (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hh)
  have hBi : InjOn (fun r => product P (stieltjesSignature q n 0 r)) (Icc 0 M) := by
    intro x hx y hy he
    have hh : product P (lipSignature η hη 0 x hx.1) = product P (lipSignature η hη 0 y hy.1) := by
      rwa [hsigη x hx hx.1, hsigη y hy hy.1]
    exact congrArg Subtype.val (hBinj (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hh)
  have hEnd : product P (stieltjesSignature p m 0 L) = product P (stieltjesSignature q n 0 M) := by
    rwa [hsigγ L ⟨hL, le_rfl⟩ hL, hsigη M ⟨hM, le_rfl⟩ hM] at hend
  have he := represented_injective_signature_images_eq γ η p m q n hp hm hq hn P hP hL hM
    (lipschitz_boundedVariation γ hγ 0 L) (lipschitz_boundedVariation η hη 0 M)
    hγ.continuous hη.continuous hrepγ hrepη hbase hAi hBi hEnd
  have hImageγ : Set.range (fun r : Icc (0 : ℝ) L => product P (lipSignature γ hγ 0 r.val r.property.1)) =
      (fun r => product P (stieltjesSignature p m 0 r)) '' Icc 0 L := by
    ext S
    constructor
    · rintro ⟨r, rfl⟩
      exact ⟨r.val, r.property, congrArg (product P) (hsigγ r.val r.property r.property.1).symm⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨⟨r, hr⟩, congrArg (product P) (hsigγ r hr hr.1)⟩
  have hImageη : Set.range (fun r : Icc (0 : ℝ) M => product P (lipSignature η hη 0 r.val r.property.1)) =
      (fun r => product P (stieltjesSignature q n 0 r)) '' Icc 0 M := by
    ext S
    constructor
    · rintro ⟨r, rfl⟩
      exact ⟨r.val, r.property, congrArg (product P) (hsigη r.val r.property r.property.1).symm⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨⟨r, hr⟩, congrArg (product P) (hsigη r hr hr.1)⟩
  exact hImageγ.trans (he.trans hImageη.symm)

end LinearInputCurveWordBVArcUnique
