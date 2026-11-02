import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.Basic

/-!
Actual local existence and uniqueness for the autonomous feedback vector field.
The derivatives hold on an open time interval containing the initial time.
No forward-global solution or continuation theorem is asserted here.
-/

noncomputable section
open Real Set Filter Metric
open scoped Topology
namespace LinearInputTrajectoryExistence

open LinearInputDesign LinearInputGradient LinearInputRegularBand

/-- Fixed-input autonomous feedback with a state-dependent tangential coefficient. -/
def vectorField (lam r u gamma target : ℝ) (b : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (-gamma * (E lam r u z.1 z.2 - target) * gx lam r u z.1 z.2 - b z * gy z.1 z.2,
   -gamma * (E lam r u z.1 z.2 - target) * gy z.1 z.2 + b z * gx lam r u z.1 z.2)

theorem contDiff_vectorField {n : WithTop ℕ∞} {b : ℝ × ℝ → ℝ}
    (hb : ContDiff ℝ n b) (lam r u gamma target : ℝ) :
    ContDiff ℝ n (vectorField lam r u gamma target b) := by
  unfold vectorField E f gx gy
  fun_prop

/-- Picard-Lindelof supplies an actual solution on a two-sided open time interval. -/
theorem exists_local_solution {b : ℝ × ℝ → ℝ} (hb : ContDiff ℝ 1 b)
    (lam r u gamma target : ℝ) (z₀ : ℝ × ℝ) (t₀ : ℝ) :
    ∃ z : ℝ → ℝ × ℝ, z t₀ = z₀ ∧ ∃ ε > (0 : ℝ),
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
        HasDerivAt z (vectorField lam r u gamma target b (z t)) t := by
  exact ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀
    ((contDiff_vectorField hb lam r u gamma target).contDiffAt (x := z₀)) t₀

/-- C1 coefficients give local uniqueness without a global Lipschitz hypothesis. -/
theorem local_solution_unique {b : ℝ × ℝ → ℝ} (hb : ContDiff ℝ 1 b)
    {lam r u gamma target t₀ : ℝ} {z w : ℝ → ℝ × ℝ}
    (hz : IsIntegralCurveAt z (fun _ => vectorField lam r u gamma target b) t₀)
    (hw : IsIntegralCurveAt w (fun _ => vectorField lam r u gamma target b) t₀)
    (heq : z t₀ = w t₀) : z =ᶠ[𝓝 t₀] w := by
  obtain ⟨K, s, hs, hlip⟩ :=
    (contDiff_vectorField hb lam r u gamma target).contDiffAt
      (x := z t₀) |>.exists_lipschitzOnWith
  have hzs : ∀ᶠ t in 𝓝 t₀, z t ∈ s := hz.continuousAt.preimage_mem_nhds hs
  have hws : ∀ᶠ t in 𝓝 t₀, w t ∈ s := hw.continuousAt.preimage_mem_nhds (heq ▸ hs)
  exact ODE_solution_unique_of_eventually (v := fun _ => vectorField lam r u gamma target b)
    (s := fun _ => s) (Eventually.of_forall fun _ => hlip) (hz.and hzs) (hw.and hws) heq

/-- Local uniqueness propagates over the common open interval of two actual solutions. -/
theorem solution_unique_on_interval {b : ℝ × ℝ → ℝ} (hb : ContDiff ℝ 1 b)
    {lam r u gamma target a c t₀ : ℝ} {z w : ℝ → ℝ × ℝ}
    (ht₀ : t₀ ∈ Ioo a c)
    (hz : ∀ t ∈ Ioo a c, HasDerivAt z (vectorField lam r u gamma target b (z t)) t)
    (hw : ∀ t ∈ Ioo a c, HasDerivAt w (vectorField lam r u gamma target b (w t)) t)
    (heq : z t₀ = w t₀) : EqOn z w (Ioo a c) := by
  let s := {t | z t = w t} ∩ Ioo a c
  suffices hsub : Ioo a c ⊆ s from fun t ht => (hsub ht).1
  apply isPreconnected_Ioo.subset_of_closure_inter_subset (s := Ioo a c) (u := s) _
    ⟨t₀, ⟨ht₀, ⟨heq, ht₀⟩⟩⟩
  · change closure ({t | z t = w t} ∩ Ioo a c) ∩ Ioo a c ⊆
      {t | z t = w t} ∩ Ioo a c
    rw [inter_comm, ← Subtype.image_preimage_val, inter_comm, ← Subtype.image_preimage_val,
      image_subset_image_iff Subtype.val_injective, preimage_setOf_eq]
    intro t ht
    rw [mem_preimage, ← closure_subtype] at ht
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
    have hzl : IsIntegralCurveAt z (fun _ => vectorField lam r u gamma target b) t := by
      filter_upwards [hmem] with q hq
      exact hz q hq
    have hwl : IsIntegralCurveAt w (fun _ => vectorField lam r u gamma target b) t := by
      filter_upwards [hmem] with q hq
      exact hw q hq
    exact (local_solution_unique hb hzl hwl ht.1).and hmem

/-- Existence and uniqueness are combined at the actual initial state. -/
theorem exists_local_unique_solution {b : ℝ × ℝ → ℝ} (hb : ContDiff ℝ 1 b)
    (lam r u gamma target : ℝ) (z₀ : ℝ × ℝ) (t₀ : ℝ) :
    ∃ z : ℝ → ℝ × ℝ, z t₀ = z₀ ∧
      IsIntegralCurveAt z (fun _ => vectorField lam r u gamma target b) t₀ ∧
      ∀ w : ℝ → ℝ × ℝ, w t₀ = z₀ →
        IsIntegralCurveAt w (fun _ => vectorField lam r u gamma target b) t₀ →
        z =ᶠ[𝓝 t₀] w := by
  obtain ⟨z, hz₀, ε, hε, hz⟩ := exists_local_solution hb lam r u gamma target z₀ t₀
  have hlocal : IsIntegralCurveAt z (fun _ => vectorField lam r u gamma target b) t₀ := by
    filter_upwards [Ioo_mem_nhds (by linarith : t₀ - ε < t₀)
      (by linarith : t₀ < t₀ + ε)] with t ht
    exact hz t ht
  refine ⟨z, hz₀, hlocal, fun w hw₀ hw => ?_⟩
  exact local_solution_unique hb hlocal hw (hz₀.trans hw₀.symm)

/-- The original positive rotation coefficient is a direct instance for every C1 Q. -/
theorem exists_local_solution_one_add_sq {Q : ℝ × ℝ → ℝ} (hQ : ContDiff ℝ 1 Q)
    (lam r u gamma target : ℝ) (z₀ : ℝ × ℝ) (t₀ : ℝ) :
    ∃ z : ℝ → ℝ × ℝ, z t₀ = z₀ ∧ ∃ ε > (0 : ℝ),
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
        HasDerivAt z (vectorField lam r u gamma target (fun q => 1 + Q q ^ 2) (z t)) t :=
  exists_local_solution (contDiff_const.add (hQ.pow 2)) lam r u gamma target z₀ t₀

/-- The vector ODE is exactly the two coordinate equations used in the energy proofs. -/
theorem hasDerivAt_vectorField_iff {lam r u gamma target : ℝ}
    {b : ℝ × ℝ → ℝ} {x y : ℝ → ℝ} {t : ℝ} :
    HasDerivAt (fun s => (x s, y s))
      (vectorField lam r u gamma target b (x t, y t)) t ↔
      HasDerivAt x
        (-gamma * (E lam r u (x t) (y t) - target) * gx lam r u (x t) (y t)
          - b (x t, y t) * gy (x t) (y t)) t ∧
      HasDerivAt y
        (-gamma * (E lam r u (x t) (y t) - target) * gy (x t) (y t)
          + b (x t, y t) * gx lam r u (x t) (y t)) t := by
  constructor
  · intro h
    exact ⟨h.fst, h.snd⟩
  · rintro ⟨hx, hy⟩
    exact hx.prodMk hy

/-- A genuine local solution exists in the coordinate notation of the original ODE. -/
theorem exists_local_coordinate_solution {b : ℝ × ℝ → ℝ} (hb : ContDiff ℝ 1 b)
    (lam r u gamma target x₀ y₀ : ℝ) :
    ∃ ε > (0 : ℝ), ∃ x y : ℝ → ℝ, x 0 = x₀ ∧ y 0 = y₀ ∧
      ∀ t ∈ Ioo (-ε) ε,
        HasDerivAt x
          (-gamma * (E lam r u (x t) (y t) - target) * gx lam r u (x t) (y t)
            - b (x t, y t) * gy (x t) (y t)) t ∧
        HasDerivAt y
          (-gamma * (E lam r u (x t) (y t) - target) * gy (x t) (y t)
            + b (x t, y t) * gx lam r u (x t) (y t)) t := by
  obtain ⟨z, hz₀, ε, hε, hz⟩ := exists_local_solution hb lam r u gamma target (x₀, y₀) 0
  refine ⟨ε, hε, fun t => (z t).1, fun t => (z t).2,
    congrArg Prod.fst hz₀, congrArg Prod.snd hz₀, fun t ht => ?_⟩
  have h := hz t (by simpa only [zero_sub, zero_add] using ht)
  exact ⟨h.fst, h.snd⟩

/-- The actual local solution satisfies the proved energy identity. -/
theorem hasDerivAt_energy_of_solution {lam r u gamma target : ℝ}
    {b : ℝ × ℝ → ℝ} {z : ℝ → ℝ × ℝ} {t : ℝ}
    (hz : HasDerivAt z (vectorField lam r u gamma target b (z t)) t) :
    HasDerivAt (fun s => E lam r u (z s).1 (z s).2)
      (-gamma * (E lam r u (z t).1 (z t).2 - target) *
        gSq lam r u (z t).1 (z t).2) t := by
  exact hasDerivAt_energy_fixed_input lam r u gamma target (b (z t)) hz.fst hz.snd

/-- An actually constructed solution obeys the exact energy formula on a nonzero
closed forward interval. This conclusion does not presume a global trajectory. -/
theorem exists_local_solution_energy_formula {b : ℝ × ℝ → ℝ} (hb : ContDiff ℝ 1 b)
    (lam r u gamma target : ℝ) (z₀ : ℝ × ℝ) :
    ∃ T > (0 : ℝ), ∃ z : ℝ → ℝ × ℝ, z 0 = z₀ ∧
      (∀ t ∈ Icc (0 : ℝ) T,
        HasDerivAt z (vectorField lam r u gamma target b (z t)) t) ∧
      ∀ t ∈ Icc (0 : ℝ) T,
        E lam r u (z t).1 (z t).2 - target =
          (E lam r u z₀.1 z₀.2 - target) *
            Real.exp (-gamma * (∫ s in 0..t, gSq lam r u (z s).1 (z s).2)) := by
  obtain ⟨z, hz₀, ε, hε, hz⟩ := exists_local_solution hb lam r u gamma target z₀ 0
  have hd : ∀ t ∈ Icc (0 : ℝ) (ε / 2),
      HasDerivAt z (vectorField lam r u gamma target b (z t)) t := by
    intro t ht
    apply hz t
    constructor <;> dsimp
    · linarith [ht.1]
    · linarith [ht.2]
  refine ⟨ε / 2, half_pos hε, z, hz₀, hd, fun t ht => ?_⟩
  have he := LinearInputStrictEnergy.energy_gap_exact_on_Icc
    (lam := lam) (r := r) (u := u) (gamma := gamma) (target := target)
    (x := fun s => (z s).1) (y := fun s => (z s).2) (b := fun s => b (z s))
    (le_of_lt (half_pos hε)) (fun s hs => ⟨(hd s hs).fst, (hd s hs).snd⟩) ht
  simpa only [hz₀] using he

/-- A supplied forward-global vector solution matches the existing trajectory predicate.
This bridge does not claim that the local solution is already global. -/
theorem isTrajectory_of_global_solution {lam r u gamma target : ℝ}
    {b : ℝ × ℝ → ℝ} {z : ℝ → ℝ × ℝ}
    (hz : ∀ t ∈ Ici (0 : ℝ), HasDerivAt z (vectorField lam r u gamma target b (z t)) t) :
    IsTrajectory lam r u gamma target (fun t => (z t).1) (fun t => (z t).2)
      (fun t => b (z t)) :=
  fun t ht => ⟨(hz t ht).fst, (hz t ht).snd⟩

end LinearInputTrajectoryExistence
