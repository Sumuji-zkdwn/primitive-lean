import KerrKoopman.HilbertShear
import Mathlib.Analysis.ODE.PicardLindelof

/-!
# Global physical-time flow for the actual bounded Hilbert vector field

The nonlinear map is only required to be globally Lipschitz. In particular, no
Frechet differentiability of a pointwise nonlinear map on L2 is assumed.
The interval-gluing argument adapts the uniform-time proof in Mathlib's
`Geometry/Manifold/IntegralCurve/UniformTime.lean` (Winston Yin, 2023,
Apache 2.0), replacing the C1 manifold uniqueness hypothesis with Lipschitz
uniqueness in a Banach space.
-/

namespace KerrKoopman.HilbertFlow

noncomputable section

open Set Metric
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def SolvesOn (F : E → E) (u : ℝ → E) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, HasDerivAt u (F (u t)) t

theorem solvesOn_mono {F : E → E} {u : ℝ → E} {s r : Set ℝ}
    (h : SolvesOn F u s) (hrs : r ⊆ s) : SolvesOn F u r :=
  fun t ht => h t (hrs ht)

theorem interval_unique {F : E → E} {K : ℝ≥0} (hF : LipschitzWith K F)
    {u v : ℝ → E} {a b t₀ : ℝ} (hu : SolvesOn F u (Ioo a b))
    (hv : SolvesOn F v (Ioo a b)) (ht₀ : t₀ ∈ Ioo a b) (h₀ : u t₀ = v t₀) :
    EqOn u v (Ioo a b) :=
  ODE_solution_unique_of_mem_Ioo (v := fun _ => F) (s := fun _ => univ)
    (fun _ _ => hF.lipschitzOnWith) ht₀
    (fun t ht => ⟨hu t ht, mem_univ _⟩)
    (fun t ht => ⟨hv t ht, mem_univ _⟩) h₀

theorem family_agrees {F : E → E} {K : ℝ≥0} (hF : LipschitzWith K F)
    {x : E} (u : ℝ → ℝ → E) (h₀ : ∀ a, u a 0 = x)
    (hu : ∀ a > 0, SolvesOn F (u a) (Ioo (-a) a))
    {a b : ℝ} (hb : 0 < b) (hba : b ≤ a) :
    EqOn (u b) (u a) (Ioo (-b) b) := by
  apply interval_unique hF (hu b hb)
    (solvesOn_mono (hu a (lt_of_lt_of_le hb hba))
      (Ioo_subset_Ioo (neg_le_neg hba) hba))
    (show (0 : ℝ) ∈ Ioo (-b) b from ⟨by linarith, hb⟩)
  rw [h₀, h₀]

theorem family_diagonal_agrees {F : E → E} {K : ℝ≥0} (hF : LipschitzWith K F)
    {x : E} (u : ℝ → ℝ → E) (h₀ : ∀ a, u a 0 = x)
    (hu : ∀ a > 0, SolvesOn F (u a) (Ioo (-a) a)) (a : ℝ) :
    EqOn (fun t => u (|t| + 1) t) (u a) (Ioo (-a) a) := by
  intro t ht
  by_cases! hlt : |t| + 1 < a
  · exact family_agrees hF u h₀ hu (by positivity) hlt.le
      (abs_lt.mp (lt_add_one _))
  · exact (family_agrees hF u h₀ hu
      (by linarith [ht.1, ht.2]) hlt ht).symm

theorem global_of_all_intervals {F : E → E} {K : ℝ≥0} (hF : LipschitzWith K F)
    (x : E) (h : ∀ a : ℝ, ∃ u : ℝ → E, u 0 = x ∧ SolvesOn F u (Ioo (-a) a)) :
    ∃ u : ℝ → E, u 0 = x ∧ ∀ t, HasDerivAt u (F (u t)) t := by
  choose u h₀ hu using h
  refine ⟨fun t => u (|t| + 1) t, h₀ _, fun t => ?_⟩
  have ht : t ∈ Ioo (-(|t| + 1)) (|t| + 1) := abs_lt.mp (lt_add_one _)
  have heq : (fun s => u (|s| + 1) s) =ᶠ[𝓝 t] u (|t| + 1) := by
    exact Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨Ioo (-(|t| + 1)) (|t| + 1), Ioo_mem_nhds ht.1 ht.2,
        family_diagonal_agrees hF u h₀ (fun a _ => hu a) _⟩
  exact (hu (|t| + 1) t ht).congr_of_eventuallyEq heq

theorem piecewise_agrees {F : E → E} {K : ℝ≥0} (hF : LipschitzWith K F)
    {u v : ℝ → E} {a b c d t₀ : ℝ} (hu : SolvesOn F u (Ioo a b))
    (hv : SolvesOn F v (Ioo c d)) (ht₀ : t₀ ∈ Ioo a b ∩ Ioo c d)
    (h₀ : u t₀ = v t₀) : EqOn (piecewise (Ioo a b) u v) v (Ioo c d) := by
  classical
  have heq := interval_unique hF
    (solvesOn_mono hu (Ioo_subset_Ioo (le_max_left a c) (min_le_left b d)))
    (solvesOn_mono hv (Ioo_subset_Ioo (le_max_right a c) (min_le_right b d)))
    (show t₀ ∈ Ioo (max a c) (min b d) from
      ⟨max_lt ht₀.1.1 ht₀.2.1, lt_min ht₀.1.2 ht₀.2.2⟩) h₀
  intro t ht
  by_cases ht' : t ∈ Ioo a b
  · rw [piecewise, if_pos ht']
    exact heq ⟨max_lt ht'.1 ht.1, lt_min ht'.2 ht.2⟩
  · rw [piecewise, if_neg ht']

theorem piecewise_solution {F : E → E} {K : ℝ≥0} (hF : LipschitzWith K F)
    {u v : ℝ → E} {a b c d t₀ : ℝ} (hu : SolvesOn F u (Ioo a b))
    (hv : SolvesOn F v (Ioo c d)) (ht₀ : t₀ ∈ Ioo a b ∩ Ioo c d)
    (h₀ : u t₀ = v t₀) : SolvesOn F (piecewise (Ioo a b) u v)
      (Ioo a b ∪ Ioo c d) := by
  classical
  intro t ht
  by_cases ht' : t ∈ Ioo a b
  · have heq : piecewise (Ioo a b) u v =ᶠ[𝓝 t] u :=
      Filter.eventuallyEq_iff_exists_mem.mpr
        ⟨Ioo a b, Ioo_mem_nhds ht'.1 ht'.2, piecewise_eqOn _ _ _⟩
    rw [heq.eq_of_nhds]
    exact (hu t ht').congr_of_eventuallyEq heq
  · have ht'' : t ∈ Ioo c d := ht.resolve_left ht'
    have heq : piecewise (Ioo a b) u v =ᶠ[𝓝 t] v :=
      Filter.eventuallyEq_iff_exists_mem.mpr
        ⟨Ioo c d, Ioo_mem_nhds ht''.1 ht''.2, piecewise_agrees hF hu hv ht₀ h₀⟩
    rw [heq.eq_of_nhds]
    exact (hv t ht'').congr_of_eventuallyEq heq

theorem exists_uniform_local [CompleteSpace E] {F : E → E} {K : ℝ≥0}
    (hF : LipschitzWith K F) (x : E) :
    ∃ u : ℝ → E, u 0 = x ∧
      SolvesOn F u (Ioo (-((K : ℝ) + 1)⁻¹) ((K : ℝ) + 1)⁻¹) := by
  let δ : ℝ := ((K : ℝ) + 1)⁻¹
  have hd : 0 < δ := by dsimp [δ]; positivity
  let a : ℝ≥0 := ‖F x‖₊ + 1
  let L : ℝ≥0 := (K + 1) * a
  let t₀ : Icc (-δ) δ := ⟨0, by constructor <;> linarith⟩
  have hb : ∀ y ∈ closedBall x (a : ℝ), ‖F y‖ ≤ (L : ℝ) := by
    intro y hy
    have hdist : ‖y - x‖ ≤ (a : ℝ) := mem_closedBall_iff_norm.mp hy
    have hnorm := norm_le_norm_sub_add (F y) (F x)
    have hLip := hF.norm_sub_le y x
    have ha : (a : ℝ) = ‖F x‖ + 1 := by simp [a]
    have hL : (L : ℝ) = ((K : ℝ) + 1) * (a : ℝ) := by simp [L]
    rw [hL]
    nlinarith [mul_le_mul_of_nonneg_left hdist K.coe_nonneg]
  have hm : (L : ℝ) * max (δ - (t₀ : ℝ)) ((t₀ : ℝ) - (-δ)) ≤
      (a : ℝ) - (0 : ℝ≥0) := by
    simp only [t₀, sub_zero, zero_sub, neg_neg, max_self, NNReal.coe_zero]
    dsimp [L, δ]
    have hn : (K : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    exact le_rfl
  have hp : IsPicardLindelof (fun _ => F) t₀ x a 0 L K :=
    IsPicardLindelof.of_time_independent hb hF.lipschitzOnWith hm
  obtain ⟨u, h₀, hu⟩ := hp.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨u, h₀, fun t ht => ?_⟩
  exact (hu t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

theorem global_of_uniform_local {F : E → E} {K : ℝ≥0}
    (hF : LipschitzWith K F) {δ : ℝ} (hd : 0 < δ)
    (h : ∀ x : E, ∃ u : ℝ → E, u 0 = x ∧ SolvesOn F u (Ioo (-δ) δ))
    (x : E) : ∃ u : ℝ → E, u 0 = x ∧ ∀ t, HasDerivAt u (F (u t)) t := by
  classical
  let s := {a : ℝ | ∃ u : ℝ → E, u 0 = x ∧ SolvesOn F u (Ioo (-a) a)}
  suffices hbdd : ¬BddAbove s by
    rw [not_bddAbove_iff] at hbdd
    apply global_of_all_intervals hF x
    intro a
    obtain ⟨b, ⟨u, h₀, hu⟩, hab⟩ := hbdd a
    exact ⟨u, h₀, solvesOn_mono hu (Ioo_subset_Ioo (neg_le_neg hab.le) hab.le)⟩
  intro hbdd
  set A := sSup s with hA
  obtain ⟨a, ha, hlt⟩ := Real.add_neg_lt_sSup (⟨δ, h x⟩ : s.Nonempty)
    (ε := -(δ / 2)) (by linarith)
  rw [← hA, ← sub_eq_add_neg] at hlt
  obtain ⟨u, h₀, hu⟩ := ha
  obtain ⟨u₁, h₁, hu₁⟩ := h (u (-(A - δ / 2)))
  obtain ⟨u₂, h₂, hu₂⟩ := h (u (A - δ / 2))
  let v₁ : ℝ → E := fun t => u₁ (t + (A - δ / 2))
  let v₂ : ℝ → E := fun t => u₂ (t - (A - δ / 2))
  have hv₁ : SolvesOn F v₁ (Ioo (-(A + δ / 2)) (-A + 3 * δ / 2)) := by
    intro t ht
    have ht' : t + (A - δ / 2) ∈ Ioo (-δ) δ := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    simpa only [v₁, one_smul] using
      (hu₁ _ ht').scomp t ((hasDerivAt_id t).add_const (A - δ / 2))
  have hv₂ : SolvesOn F v₂ (Ioo (A - 3 * δ / 2) (A + δ / 2)) := by
    intro t ht
    have ht' : t - (A - δ / 2) ∈ Ioo (-δ) δ := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    simpa only [v₂, one_smul] using
      (hu₂ _ ht').scomp t ((hasDerivAt_id t).sub_const (A - δ / 2))
  have heq₁ : v₁ (-(A - δ / 2)) = u (-(A - δ / 2)) := by simp [v₁, h₁]
  have heq₂ : v₂ (A - δ / 2) = u (A - δ / 2) := by simp [v₂, h₂]
  have hdA : δ ≤ A := le_csSup hbdd (h x)
  let w : ℝ → E := piecewise (Ioo (-(A + δ / 2)) a)
    (piecewise (Ioo (-a) a) u v₁) v₂
  have hw₀ : w 0 = x := by
    dsimp only [w]
    rw [piecewise, if_pos ⟨by linarith, by linarith⟩,
      piecewise, if_pos ⟨by linarith, by linarith⟩, h₀]
  suffices hw : SolvesOn F w (Ioo (-(A + δ / 2)) (A + δ / 2)) from
    (not_lt.mpr (le_csSup hbdd ⟨w, hw₀, hw⟩)) (by linarith)
  have hleft : SolvesOn F (piecewise (Ioo (-a) a) u v₁)
      (Ioo (-(A + δ / 2)) a) := by
    apply solvesOn_mono (piecewise_solution hF hu hv₁
      (show -(A - δ / 2) ∈ Ioo (-a) a ∩
          Ioo (-(A + δ / 2)) (-A + 3 * δ / 2) from
        ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩) heq₁.symm)
    exact union_comm _ _ ▸ Ioo_subset_Ioo_union_Ioo (by linarith) (by linarith) le_rfl
  apply solvesOn_mono (piecewise_solution hF hleft hv₂
    (show A - δ / 2 ∈ Ioo (-(A + δ / 2)) a ∩
        Ioo (A - 3 * δ / 2) (A + δ / 2) from
      ⟨⟨by linarith, hlt⟩, ⟨by linarith, by linarith⟩⟩)
    (by rw [piecewise, if_pos ⟨by linarith, hlt⟩, heq₂]))
  exact Ioo_subset_Ioo_union_Ioo le_rfl (by linarith) (by linarith)

/-- Global existence follows from the actual global Lipschitz estimate, with
no differentiability hypothesis on the vector field. -/
theorem exists_global [CompleteSpace E] {F : E → E} {K : ℝ≥0}
    (hF : LipschitzWith K F) (x : E) :
    ∃ u : ℝ → E, u 0 = x ∧ ∀ t, HasDerivAt u (F (u t)) t :=
  global_of_uniform_local hF (by positivity) (exists_uniform_local hF) x

variable [CompleteSpace E]

/-- The unique solution selected from the proved global existence theorem.
This is a mathematical flow, not a claim of a finite closed evaluation formula. -/
def globalFlow {F : E → E} {K : ℝ≥0} (hF : LipschitzWith K F) (t : ℝ) (x : E) : E :=
  (exists_global hF x).choose t

theorem globalFlow_zero {F : E → E} {K : ℝ≥0} (hF : LipschitzWith K F) (x : E) :
    globalFlow hF 0 x = x := (exists_global hF x).choose_spec.1

theorem hasDerivAt_globalFlow {F : E → E} {K : ℝ≥0}
    (hF : LipschitzWith K F) (t : ℝ) (x : E) :
    HasDerivAt (fun s => globalFlow hF s x) (F (globalFlow hF t x)) t :=
  (exists_global hF x).choose_spec.2 t

omit [CompleteSpace E] in
theorem global_unique {F : E → E} {K : ℝ≥0} (hF : LipschitzWith K F)
    {u v : ℝ → E} (hu : ∀ t, HasDerivAt u (F (u t)) t)
    (hv : ∀ t, HasDerivAt v (F (v t)) t) (h₀ : u 0 = v 0) : u = v :=
  ODE_solution_unique_univ (v := fun _ => F) (s := fun _ => univ)
    (fun _ => hF.lipschitzOnWith) (fun t => ⟨hu t, mem_univ _⟩)
    (fun t => ⟨hv t, mem_univ _⟩) h₀

theorem globalFlow_add {F : E → E} {K : ℝ≥0}
    (hF : LipschitzWith K F) (t s : ℝ) (x : E) :
    globalFlow hF (t + s) x = globalFlow hF t (globalFlow hF s x) := by
  have heq : (fun r => globalFlow hF (r + s) x) =
      (fun r => globalFlow hF r (globalFlow hF s x)) := by
    apply global_unique hF
    · intro r
      simpa only [one_smul] using
        (hasDerivAt_globalFlow hF (r + s) x).scomp r ((hasDerivAt_id r).add_const s)
    · exact fun r => hasDerivAt_globalFlow hF r _
    · simp only [zero_add, globalFlow_zero]
  exact congrFun heq t

theorem globalFlow_inverse {F : E → E} {K : ℝ≥0}
    (hF : LipschitzWith K F) (t : ℝ) (x : E) :
    globalFlow hF (-t) (globalFlow hF t x) = x := by
  rw [← globalFlow_add, neg_add_cancel, globalFlow_zero]

/-- Actual continuous dependence follows by Gronwall from the differential
equation; it is not postulated as a property of the chosen flow. -/
theorem globalFlow_norm_sub_le {F : E → E} {K : ℝ≥0}
    (hF : LipschitzWith K F) (t : ℝ) (ht : 0 ≤ t) (x y : E) :
    ‖globalFlow hF t x - globalFlow hF t y‖ ≤
      Real.exp ((K : ℝ) * t) * ‖x - y‖ := by
  let u : ℝ → E := fun s => globalFlow hF s x - globalFlow hF s y
  have hu (s : ℝ) : HasDerivAt u
      (F (globalFlow hF s x) - F (globalFlow hF s y)) s :=
    (hasDerivAt_globalFlow hF s x).sub (hasDerivAt_globalFlow hF s y)
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := u) (f' := fun s => F (globalFlow hF s x) - F (globalFlow hF s y))
    (δ := ‖x - y‖) (K := (K : ℝ)) (ε := 0)
    (fun s _ => (hu s).continuousAt.continuousWithinAt)
    (fun s _ => (hu s).hasDerivWithinAt)
    (show ‖u 0‖ ≤ ‖x - y‖ by simp [u, globalFlow_zero])
    (fun s _ => by
      simpa only [add_zero] using
        hF.norm_sub_le (globalFlow hF s x) (globalFlow hF s y)) t ⟨ht, le_rfl⟩
  simpa only [gronwallBound_ε0, sub_zero, mul_comm] using hg

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- The actual bounded spatial Kerr system has a global solution for every
initial state and every globally nonexpansive material map. -/
theorem exists_hilbert_solution (Q : V →L[ℝ] V) (G : V → V)
    (hG : LipschitzWith 1 G) (z : HilbertShear.State V) :
    ∃ u : ℝ → HilbertShear.State V, u 0 = z ∧
      ∀ t, HasDerivAt u (HilbertShear.field Q G (u t)) t :=
  exists_global (HilbertShear.field_lipschitz Q G hG) z

def flow (Q : V →L[ℝ] V) (G : V → V) (hG : LipschitzWith 1 G)
    (t : ℝ) (z : HilbertShear.State V) : HilbertShear.State V :=
  globalFlow (HilbertShear.field_lipschitz Q G hG) t z

theorem flow_zero (Q : V →L[ℝ] V) (G : V → V) (hG : LipschitzWith 1 G)
    (z : HilbertShear.State V) : flow Q G hG 0 z = z := globalFlow_zero _ _

theorem hasDerivAt_flow (Q : V →L[ℝ] V) (G : V → V) (hG : LipschitzWith 1 G)
    (t : ℝ) (z : HilbertShear.State V) :
    HasDerivAt (fun s => flow Q G hG s z) (HilbertShear.field Q G (flow Q G hG t z)) t :=
  hasDerivAt_globalFlow _ _ _

theorem flow_add (Q : V →L[ℝ] V) (G : V → V) (hG : LipschitzWith 1 G)
    (t s : ℝ) (z : HilbertShear.State V) :
    flow Q G hG (t + s) z = flow Q G hG t (flow Q G hG s z) :=
  globalFlow_add _ _ _ _

theorem flow_norm_sub_le (Q : V →L[ℝ] V) (G : V → V) (hG : LipschitzWith 1 G)
    (t : ℝ) (ht : 0 ≤ t) (z w : HilbertShear.State V) :
    ‖flow Q G hG t z - flow Q G hG t w‖ ≤ Real.exp (‖Q‖ * t) * ‖z - w‖ :=
  globalFlow_norm_sub_le _ t ht z w

theorem flow_norm_le (Q : V →L[ℝ] V) (G : V → V) (hG : LipschitzWith 1 G)
    (hG0 : G 0 = 0) (t : ℝ) (ht : 0 ≤ t) (z : HilbertShear.State V) :
    ‖flow Q G hG t z‖ ≤ Real.exp (‖Q‖ * t) * ‖z‖ := by
  have hg := HilbertShear.solution_growth Q G hG hG0
    (fun s => flow Q G hG s z) t (fun s _ => hasDerivAt_flow Q G hG s z) t ⟨ht, le_rfl⟩
  simpa only [flow_zero] using hg

end

end KerrKoopman.HilbertFlow
