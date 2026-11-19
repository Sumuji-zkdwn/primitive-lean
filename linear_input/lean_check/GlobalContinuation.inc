import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.Basic
import Mathlib.Tactic.Linarith

/-! Forward continuation by actual overlapping solutions and their uniqueness. -/

noncomputable section
open Set Filter Metric
open scoped Topology
namespace LinearInputGlobalContinuation

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem local_unique {F : V → V} (hF : ContDiff ℝ 1 F)
    {t₀ : ℝ} {z w : ℝ → V}
    (hz : IsIntegralCurveAt z (fun _ => F) t₀)
    (hw : IsIntegralCurveAt w (fun _ => F) t₀)
    (heq : z t₀ = w t₀) : z =ᶠ[𝓝 t₀] w := by
  obtain ⟨K, s, hs, hlip⟩ := hF.contDiffAt (x := z t₀) |>.exists_lipschitzOnWith
  have hzs : ∀ᶠ t in 𝓝 t₀, z t ∈ s := hz.continuousAt.preimage_mem_nhds hs
  have hws : ∀ᶠ t in 𝓝 t₀, w t ∈ s := hw.continuousAt.preimage_mem_nhds (heq ▸ hs)
  exact ODE_solution_unique_of_eventually (v := fun _ => F)
    (s := fun _ => s) (Eventually.of_forall fun _ => hlip) (hz.and hzs) (hw.and hws) heq

theorem unique_on_Ioo {F : V → V} (hF : ContDiff ℝ 1 F)
    {a c t₀ : ℝ} {z w : ℝ → V}
    (ht₀ : t₀ ∈ Ioo a c)
    (hz : ∀ t ∈ Ioo a c, HasDerivAt z (F (z t)) t)
    (hw : ∀ t ∈ Ioo a c, HasDerivAt w (F (w t)) t)
    (heq : z t₀ = w t₀) : EqOn z w (Ioo a c) := by
  let s := {t | z t = w t} ∩ Ioo a c
  suffices hsub : Ioo a c ⊆ s from fun t ht => (hsub ht).1
  apply isPreconnected_Ioo.subset_of_closure_inter_subset (s := Ioo a c) (u := s) _
    ⟨t₀, ⟨ht₀, ⟨heq, ht₀⟩⟩⟩
  · change closure ({t | z t = w t} ∩ Ioo a c) ∩ Ioo a c ⊆
      {t | z t = w t} ∩ Ioo a c
    rw [inter_comm, ← Subtype.image_preimage_val, inter_comm, ← Subtype.image_preimage_val,
      image_subset_image_iff Subtype.val_injective, preimage_ofPred_eq]
    intro t ht
    change (t : ℝ) ∈ closure (Subtype.val '' (Subtype.val ⁻¹' {t | z t = w t})) at ht
    rw [← closure_subtype] at ht
    revert ht t
    apply IsClosed.closure_subset (isClosed_eq _ _)
    · rw [continuous_iff_continuousAt]
      rintro ⟨t, ht⟩
      exact (hz t ht).continuousAt.comp continuousAt_subtype_val
    · rw [continuous_iff_continuousAt]
      rintro ⟨t, ht⟩
      exact (hw t ht).continuousAt.comp continuousAt_subtype_val
  · rw [isOpen_iff_mem_nhds]
    intro t ht
    have hmem := Ioo_mem_nhds ht.2.1 ht.2.2
    have hzl : IsIntegralCurveAt z (fun _ => F) t := by
      filter_upwards [hmem] with q hq
      exact hz q hq
    have hwl : IsIntegralCurveAt w (fun _ => F) t := by
      filter_upwards [hmem] with q hq
      exact hw q hq
    exact (local_unique hF hzl hwl ht.1).and hmem

/-- The piecewise extension agrees with the second solution everywhere on its interval. -/
theorem piecewise_eqOn {F : V → V} (hF : ContDiff ℝ 1 F)
    {a b c d t₀ : ℝ} {z w : ℝ → V}
    (hz : ∀ t ∈ Ioo a b, HasDerivAt z (F (z t)) t)
    (hw : ∀ t ∈ Ioo c d, HasDerivAt w (F (w t)) t)
    (ht₀ : t₀ ∈ Ioo a b ∩ Ioo c d) (heq : z t₀ = w t₀) :
    EqOn ((Ioo a b).piecewise z w) w (Ioo c d) := by
  classical
  have hu : EqOn z w (Ioo (max a c) (min b d)) :=
    unique_on_Ioo hF ⟨max_lt ht₀.1.1 ht₀.2.1, lt_min ht₀.1.2 ht₀.2.2⟩
      (fun t ht => hz t ⟨lt_of_le_of_lt (le_max_left _ _) ht.1,
        lt_of_lt_of_le ht.2 (min_le_left _ _)⟩)
      (fun t ht => hw t ⟨lt_of_le_of_lt (le_max_right _ _) ht.1,
        lt_of_lt_of_le ht.2 (min_le_right _ _)⟩) heq
  intro t ht
  by_cases hmem : t ∈ Ioo a b
  · rw [piecewise, ite_eq_left hmem]
    exact hu ⟨max_lt hmem.1 ht.1, lt_min hmem.2 ht.2⟩
  · rw [piecewise, ite_eq_right hmem]

/-- Overlapping actual solutions glue to an actual solution on the union. -/
theorem hasDerivAt_piecewise {F : V → V} (hF : ContDiff ℝ 1 F)
    {a b c d t₀ : ℝ} {z w : ℝ → V}
    (hz : ∀ t ∈ Ioo a b, HasDerivAt z (F (z t)) t)
    (hw : ∀ t ∈ Ioo c d, HasDerivAt w (F (w t)) t)
    (ht₀ : t₀ ∈ Ioo a b ∩ Ioo c d) (heq : z t₀ = w t₀) :
    ∀ t ∈ Ioo a b ∪ Ioo c d,
      HasDerivAt ((Ioo a b).piecewise z w) (F (((Ioo a b).piecewise z w) t)) t := by
  classical
  intro t ht
  by_cases hmem : t ∈ Ioo a b
  · have hh : (Ioo a b).piecewise z w =ᶠ[𝓝 t] z := by
      filter_upwards [Ioo_mem_nhds hmem.1 hmem.2] with s hs
      exact piecewise_eq_of_mem (Ioo a b) z w hs
    have hv := hh.eq_of_nhds
    rw [hv]
    exact (hz t hmem).congr_of_eventuallyEq hh
  · have hmem' : t ∈ Ioo c d := ht.resolve_left hmem
    have hh : (Ioo a b).piecewise z w =ᶠ[𝓝 t] w := by
      filter_upwards [Ioo_mem_nhds hmem'.1 hmem'.2] with s hs
      exact piecewise_eqOn hF hz hw ht₀ heq hs
    have hv := hh.eq_of_nhds
    rw [hv]
    exact (hw t hmem').congr_of_eventuallyEq hh

/-- Uniform local existence on an invariant set prevents a finite forward endpoint. -/
theorem exists_arbitrarily_long_solution
    {F : V → V} (hF : ContDiff ℝ 1 F)
    {K : Set V} {z₀ : V} (hz₀ : z₀ ∈ K)
    {ε : ℝ} (hε : 0 < ε)
    (hloc : ∀ x ∈ K, ∃ z : ℝ → V, z 0 = x ∧
      ∀ t ∈ Ioo (-ε) ε, HasDerivAt z (F (z t)) t)
    (hstay : ∀ (a : ℝ) (z : ℝ → V), z 0 = z₀ →
      (∀ t ∈ Ioo (-ε) a, HasDerivAt z (F (z t)) t) →
      ∀ t : ℝ, 0 ≤ t → t < a → z t ∈ K) :
    ∀ a : ℝ, ∃ z : ℝ → V, z 0 = z₀ ∧
      ∀ t ∈ Ioo (-ε) a, HasDerivAt z (F (z t)) t := by
  classical
  let S : Set ℝ := {a | ∃ z : ℝ → V, z 0 = z₀ ∧
    ∀ t ∈ Ioo (-ε) a, HasDerivAt z (F (z t)) t}
  have hbase : ε ∈ S := hloc z₀ hz₀
  have hnbdd : ¬ BddAbove S := by
    intro hbdd
    let A := sSup S
    have hεA : ε ≤ A := le_csSup hbdd hbase
    obtain ⟨a, ha, hlt⟩ := Real.add_neg_lt_sSup
      (⟨ε, hbase⟩ : S.Nonempty) (ε := -(ε / 2)) (by linarith)
    change sSup S + -(ε / 2) < a at hlt
    have hta : A - ε / 2 < a := by dsimp [A]; linarith
    obtain ⟨z, hzinit, hz⟩ := ha
    have hstate : z (A - ε / 2) ∈ K :=
      hstay a z hzinit hz (A - ε / 2) (by linarith) hta
    obtain ⟨w, hwinit, hw⟩ := hloc _ hstate
    let v : ℝ → V := fun t => w (t - (A - ε / 2))
    have hvinit : v (A - ε / 2) = z (A - ε / 2) := by
      simp only [v, sub_self, hwinit]
    have hv : ∀ t ∈ Ioo (A - ε / 2 - ε) (A - ε / 2 + ε),
        HasDerivAt v (F (v t)) t := by
      intro t ht
      have ht' : t - (A - ε / 2) ∈ Ioo (-ε) ε := by constructor <;> linarith [ht.1, ht.2]
      have hshift : HasDerivAt (fun s : ℝ => s - (A - ε / 2)) 1 t := by
        simpa using (hasDerivAt_id t).sub_const (A - ε / 2)
      simpa only [v, one_smul, Function.comp_def] using (hw _ ht').scomp t hshift
    let q : ℝ → V := (Ioo (-ε) a).piecewise z v
    have hqinit : q 0 = z₀ := by
      change (Ioo (-ε) a).piecewise z v 0 = z₀
      rw [piecewise, ite_eq_left (show (0 : ℝ) ∈ Ioo (-ε) a from ⟨by linarith, by linarith⟩)]
      exact hzinit
    have hq : ∀ t ∈ Ioo (-ε) (A + ε / 2), HasDerivAt q (F (q t)) t := by
      have hpatch := hasDerivAt_piecewise hF hz hv
        (t₀ := A - ε / 2)
        (show A - ε / 2 ∈ Ioo (-ε) a ∩ Ioo (A - ε / 2 - ε) (A - ε / 2 + ε)
          from ⟨⟨by linarith, hta⟩, ⟨by linarith, by linarith⟩⟩) hvinit.symm
      intro t ht
      apply hpatch t
      by_cases hta' : t < a
      · exact Or.inl ⟨ht.1, hta'⟩
      · exact Or.inr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hmem : A + ε / 2 ∈ S := ⟨q, hqinit, hq⟩
    have hbound : A + ε / 2 ≤ A := le_csSup hbdd hmem
    linarith
  rw [not_bddAbove_iff] at hnbdd
  intro a
  obtain ⟨c, ⟨z, hzinit, hz⟩, hac⟩ := hnbdd a
  exact ⟨z, hzinit, fun t ht => hz t ⟨ht.1, lt_trans ht.2 hac⟩⟩

/-- Arbitrarily long compatible actual solutions give a forward-global solution. -/
theorem exists_forward_solution
    {F : V → V} (hF : ContDiff ℝ 1 F)
    {K : Set V} {z₀ : V} (hz₀ : z₀ ∈ K)
    {ε : ℝ} (hε : 0 < ε)
    (hloc : ∀ x ∈ K, ∃ z : ℝ → V, z 0 = x ∧
      ∀ t ∈ Ioo (-ε) ε, HasDerivAt z (F (z t)) t)
    (hstay : ∀ (a : ℝ) (z : ℝ → V), z 0 = z₀ →
      (∀ t ∈ Ioo (-ε) a, HasDerivAt z (F (z t)) t) →
      ∀ t : ℝ, 0 ≤ t → t < a → z t ∈ K) :
    ∃ z : ℝ → V, z 0 = z₀ ∧
      ∀ t : ℝ, 0 ≤ t → HasDerivAt z (F (z t)) t := by
  classical
  have hall := exists_arbitrarily_long_solution hF hz₀ hε hloc hstay
  choose q hqinit hq using hall
  let z : ℝ → V := fun t => q (max t 0 + 1) t
  have hagree (a : ℝ) (ha : 0 < a) : EqOn z (q a) (Ioo (-ε) a) := by
    intro t ht
    have hc : 0 < max t 0 + 1 := by linarith [le_max_right t (0 : ℝ)]
    have hu : EqOn (q (max t 0 + 1)) (q a) (Ioo (-ε) (min (max t 0 + 1) a)) :=
      unique_on_Ioo hF ⟨by linarith, lt_min hc ha⟩
        (fun s hs => hq _ s ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_left _ _)⟩)
        (fun s hs => hq _ s ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_right _ _)⟩)
        ((hqinit _).trans (hqinit _).symm)
    exact hu ⟨ht.1, lt_min (by linarith [le_max_left t (0 : ℝ)]) ht.2⟩
  refine ⟨z, by dsimp [z]; exact hqinit _, fun t ht => ?_⟩
  have hdom : t ∈ Ioo (-ε) (t + 1) := ⟨by linarith, by linarith⟩
  have hh : z =ᶠ[𝓝 t] q (t + 1) := by
    filter_upwards [Ioo_mem_nhds hdom.1 hdom.2] with s hs
    exact hagree (t + 1) (by linarith) hs
  rw [hh.eq_of_nhds]
  exact (hq (t + 1) t hdom).congr_of_eventuallyEq hh

end LinearInputGlobalContinuation
