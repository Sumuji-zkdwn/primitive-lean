import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.Compact

/-!
Actual finite-dimensional feedback with damped internally updated coefficients.
The input u is fixed; the tangential coefficient may depend on all coordinates.
-/

noncomputable section
namespace LinearInputCoupledTrajectory

open Real Set
open LinearInputDesign LinearInputGradient LinearInputRegularBand

abbrev State (n : ℕ) := (ℝ × ℝ) × (Fin n → ℝ)

/-- The original spatial feedback, coupled to finitely many damped internal
coordinates whose forcing depends only on the spatial state. -/
def vectorField {n : ℕ} (lam r u gamma target : ℝ) (b : State n → ℝ)
    (kappa rho : Fin n → ℝ) (Phi : ℝ × ℝ → (Fin n → ℝ)) (q : State n) : State n :=
  (LinearInputTrajectoryExistence.vectorField lam r u gamma target (fun _ => b q) q.1,
   fun i => -kappa i * q.2 i + rho i * Phi q.1 i)

theorem contDiff_vectorField {n : ℕ} {m : WithTop ℕ∞} {b : State n → ℝ}
    {Phi : ℝ × ℝ → (Fin n → ℝ)} (hb : ContDiff ℝ m b) (hPhi : ContDiff ℝ m Phi)
    (lam r u gamma target : ℝ) (kappa rho : Fin n → ℝ) :
    ContDiff ℝ m (vectorField lam r u gamma target b kappa rho Phi) := by
  unfold vectorField LinearInputTrajectoryExistence.vectorField E f gx gy
  fun_prop

/-- The actual internal coordinate derivative is obtained by projection. -/
theorem hasDerivAt_internal {n : ℕ} {lam r u gamma target t : ℝ}
    {b : State n → ℝ} {kappa rho : Fin n → ℝ} {Phi : ℝ × ℝ → (Fin n → ℝ)}
    {q : ℝ → State n}
    (hq : HasDerivAt q (vectorField lam r u gamma target b kappa rho Phi (q t)) t)
    (i : Fin n) :
    HasDerivAt (fun s => (q s).2 i)
      (-kappa i * (q t).2 i + rho i * Phi (q t).1 i) t :=
  (hasDerivAt_pi.mp hq.snd) i

/-- Internal updates do not change the exact spatial energy derivative. -/
theorem hasDerivAt_energy {n : ℕ} {lam r u gamma target t : ℝ}
    {b : State n → ℝ} {kappa rho : Fin n → ℝ} {Phi : ℝ × ℝ → (Fin n → ℝ)}
    {q : ℝ → State n}
    (hq : HasDerivAt q (vectorField lam r u gamma target b kappa rho Phi (q t)) t) :
    HasDerivAt (fun s => E lam r u (q s).1.1 (q s).1.2)
      (-gamma * (E lam r u (q t).1.1 (q t).1.2 - target) *
        gSq lam r u (q t).1.1 (q t).1.2) t :=
  hasDerivAt_energy_fixed_input lam r u gamma target (b (q t)) hq.fst.fst hq.fst.snd

/-- Spatial energy confinement holds on every actual finite solution interval,
even though the tangential coefficient changes with the internal state. -/
theorem energy_band_on_Icc {n : ℕ} {lam r u gamma target T : ℝ}
    {b : State n → ℝ} {kappa rho : Fin n → ℝ} {Phi : ℝ × ℝ → (Fin n → ℝ)}
    {q : ℝ → State n} (hgamma : 0 ≤ gamma) (hT : 0 ≤ T)
    (hq : ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivAt q (vectorField lam r u gamma target b kappa rho Phi (q s)) s)
    (hinit : target ≤ E lam r u (q 0).1.1 (q 0).1.2)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    target ≤ E lam r u (q t).1.1 (q t).1.2 ∧
      E lam r u (q t).1.1 (q t).1.2 ≤ E lam r u (q 0).1.1 (q 0).1.2 := by
  have hg : ContinuousOn (fun s => gSq lam r u (q s).1.1 (q s).1.2)
      (Icc (0 : ℝ) T) := by
    intro s hs
    exact ((continuous_gSq lam r u).continuousAt.comp
      (hq s hs).continuousAt.fst).continuousWithinAt
  have he := LinearInputFiniteBand.error_band_on_Icc hgamma hT hg
    (fun s hs => (hasDerivAt_energy (hq s hs)).sub_const target)
    (fun s _ => gSq_nonneg lam r u (q s).1.1 (q s).1.2) (sub_nonneg.mpr hinit) ht
  constructor <;> linarith [he.1, he.2]

/-- A supplied global coupled solution projects to the original spatial
trajectory predicate with the actual time-dependent coefficient. -/
theorem isTrajectory_of_global_solution {n : ℕ} {lam r u gamma target : ℝ}
    {b : State n → ℝ} {kappa rho : Fin n → ℝ} {Phi : ℝ × ℝ → (Fin n → ℝ)}
    {q : ℝ → State n}
    (hq : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt q (vectorField lam r u gamma target b kappa rho Phi (q t)) t) :
    IsTrajectory lam r u gamma target (fun t => (q t).1.1) (fun t => (q t).1.2)
      (fun t => b (q t)) :=
  fun t ht => ⟨(hq t ht).fst.fst, (hq t ht).fst.snd⟩

/-- A compact spatial set supplies finite coordinate bounds compatible with
strictly positive damping and every initial internal state. -/
theorem exists_internal_bounds {n : ℕ} {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    {Phi : ℝ × ℝ → (Fin n → ℝ)} (hPhi : Continuous Phi)
    (kappa rho theta₀ : Fin n → ℝ) (hkappa : ∀ i, 0 < kappa i) :
    ∃ M : Fin n → ℝ, (∀ i, 0 ≤ M i) ∧ (∀ i, |theta₀ i| ≤ M i) ∧
      ∀ z ∈ K, ∀ i, |rho i * Phi z i| ≤ kappa i * M i := by
  have hbounded (i : Fin n) : ∃ B : ℝ, ∀ z ∈ K, |rho i * Phi z i| ≤ B := by
    simpa only [Real.norm_eq_abs, Pi.mul_apply, Function.comp_def] using hK.exists_bound_of_continuousOn
      ((continuous_const.mul ((continuous_apply i).comp hPhi)).continuousOn)
  choose B hB using hbounded
  let M : Fin n → ℝ := fun i => max |theta₀ i| (max (B i) 0 / kappa i)
  refine ⟨M, fun i => (abs_nonneg _).trans (le_max_left _ _),
    fun i => le_max_left _ _, ?_⟩
  intro z hz i
  have hM : max (B i) 0 ≤ kappa i * M i := by
    have hm : max (B i) 0 / kappa i ≤ M i := le_max_right _ _
    have hh := (div_le_iff₀ (hkappa i)).mp hm
    simpa only [mul_comm] using hh
  exact (hB i z hz).trans ((le_max_left _ _).trans hM)

/-- Every finite solution segment stays in its spatial energy band and its
internal coordinate box. Both conclusions follow from the actual ODE. -/
theorem band_box_on_Icc {n : ℕ} {lam r u gamma target T : ℝ}
    {b : State n → ℝ} {kappa rho M : Fin n → ℝ} {Phi : ℝ × ℝ → (Fin n → ℝ)}
    {q : ℝ → State n} (hgamma : 0 ≤ gamma) (hT : 0 ≤ T)
    (hkappa : ∀ i, 0 < kappa i) (hM : ∀ i, 0 ≤ M i)
    (hforce : ∀ z : ℝ × ℝ,
      target ≤ E lam r u z.1 z.2 ∧ E lam r u z.1 z.2 ≤ E lam r u (q 0).1.1 (q 0).1.2 →
      ∀ i, |rho i * Phi z i| ≤ kappa i * M i)
    (hinit : target ≤ E lam r u (q 0).1.1 (q 0).1.2)
    (htheta : ∀ i, |(q 0).2 i| ≤ M i)
    (hq : ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivAt q (vectorField lam r u gamma target b kappa rho Phi (q s)) s)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    (target ≤ E lam r u (q t).1.1 (q t).1.2 ∧
      E lam r u (q t).1.1 (q t).1.2 ≤ E lam r u (q 0).1.1 (q 0).1.2) ∧
      ∀ i, |(q t).2 i| ≤ M i := by
  refine ⟨energy_band_on_Icc hgamma hT hq hinit ht, fun i => ?_⟩
  exact LinearInputFiniteInternalUpdate.abs_le_on_Icc (hkappa i) (hM i) hT
    (fun s hs => hasDerivAt_internal (hq s hs) i)
    (fun s hs => hforce (q s).1 (energy_band_on_Icc hgamma hT hq hinit hs) i)
    (htheta i) ht

/-- Damped internal updates and spatial confinement yield an actual
forward-global coupled solution, with a fixed compact coordinate box. -/
theorem exists_global_solution {n : ℕ} {lam r u gamma target : ℝ}
    {b : State n → ℝ} {kappa rho : Fin n → ℝ} {Phi : ℝ × ℝ → (Fin n → ℝ)}
    (hb : ContDiff ℝ 1 b) (hPhi : ContDiff ℝ 1 Phi)
    (hlam : 0 < lam) (hgamma : 0 ≤ gamma) (hkappa : ∀ i, 0 < kappa i)
    (q₀ : State n) (hinit : target ≤ E lam r u q₀.1.1 q₀.1.2) :
    ∃ M : Fin n → ℝ, (∀ i, 0 ≤ M i) ∧ ∃ q : ℝ → State n, q 0 = q₀ ∧
      (∀ t : ℝ, 0 ≤ t →
        HasDerivAt q (vectorField lam r u gamma target b kappa rho Phi (q t)) t) ∧
      ∀ t : ℝ, 0 ≤ t →
        (target ≤ E lam r u (q t).1.1 (q t).1.2 ∧
          E lam r u (q t).1.1 (q t).1.2 ≤ E lam r u q₀.1.1 q₀.1.2) ∧
        ∀ i, |(q t).2 i| ≤ M i := by
  let K : Set (ℝ × ℝ) := {z | target ≤ E lam r u z.1 z.2 ∧
    E lam r u z.1 z.2 ≤ E lam r u q₀.1.1 q₀.1.2}
  have hK : IsCompact K :=
    LinearInputCoercivity.isCompact_band hlam r u target (E lam r u q₀.1.1 q₀.1.2)
  obtain ⟨M, hM, htheta, hforce⟩ :=
    exists_internal_bounds hK hPhi.continuous kappa rho q₀.2 hkappa
  let S : Set (State n) := K ×ˢ Icc (-M) M
  have hS : IsCompact S := hK.prod isCompact_Icc
  have hstart : q₀ ∈ S := by
    exact ⟨⟨hinit, le_rfl⟩, (fun i => (abs_le.mp (htheta i)).1),
      fun i => (abs_le.mp (htheta i)).2⟩
  have hF : ContDiff ℝ 1 (vectorField lam r u gamma target b kappa rho Phi) :=
    contDiff_vectorField hb hPhi lam r u gamma target kappa rho
  obtain ⟨eps, heps, hlocal⟩ := LinearInputCompactLocalExistence.exists_uniform_local_time hF hS
  have hstay : ∀ (a : ℝ) (q : ℝ → State n), q 0 = q₀ →
      (∀ t ∈ Ioo (-eps) a,
        HasDerivAt q (vectorField lam r u gamma target b kappa rho Phi (q t)) t) →
      ∀ t : ℝ, 0 ≤ t → t < a → q t ∈ S := by
    intro a q hq₀ hq t ht hta
    have hi : target ≤ E lam r u (q 0).1.1 (q 0).1.2 := by simpa only [hq₀] using hinit
    have hitheta : ∀ i, |(q 0).2 i| ≤ M i := by simpa only [hq₀] using htheta
    have hiforce : ∀ z : ℝ × ℝ,
        target ≤ E lam r u z.1 z.2 ∧
          E lam r u z.1 z.2 ≤ E lam r u (q 0).1.1 (q 0).1.2 →
        ∀ i, |rho i * Phi z i| ≤ kappa i * M i := by
      simpa only [K, mem_ofPred_eq, hq₀] using hforce
    have hbound := band_box_on_Icc hgamma ht hkappa hM hiforce hi hitheta
      (fun s hs => hq s ⟨by linarith [hs.1], hs.2.trans_lt hta⟩)
      (show t ∈ Icc (0 : ℝ) t from ⟨ht, le_rfl⟩)
    refine ⟨?_, (fun i => (abs_le.mp (hbound.2 i)).1),
      fun i => (abs_le.mp (hbound.2 i)).2⟩
    simpa only [K, mem_ofPred_eq, hq₀] using hbound.1
  obtain ⟨q, hq₀, hq⟩ :=
    LinearInputGlobalContinuation.exists_forward_solution hF hstart heps hlocal hstay
  refine ⟨M, hM, q, hq₀, hq, fun t ht => ?_⟩
  have hi : target ≤ E lam r u (q 0).1.1 (q 0).1.2 := by simpa only [hq₀] using hinit
  have hitheta : ∀ i, |(q 0).2 i| ≤ M i := by simpa only [hq₀] using htheta
  have hiforce : ∀ z : ℝ × ℝ,
      target ≤ E lam r u z.1 z.2 ∧
        E lam r u z.1 z.2 ≤ E lam r u (q 0).1.1 (q 0).1.2 →
      ∀ i, |rho i * Phi z i| ≤ kappa i * M i := by
    simpa only [K, mem_ofPred_eq, hq₀] using hforce
  have hbound := band_box_on_Icc hgamma ht hkappa hM hiforce hi hitheta
    (fun s hs => hq s hs.1) (show t ∈ Icc (0 : ℝ) t from ⟨ht, le_rfl⟩)
  simpa only [hq₀] using hbound

/-- The actual coupled solution is unique on the nonnegative time domain.
Uniqueness itself needs no damping, energy or coefficient sign assumptions. -/
theorem solution_unique_on_Ici {n : ℕ} {lam r u gamma target : ℝ}
    {b : State n → ℝ} {kappa rho : Fin n → ℝ} {Phi : ℝ × ℝ → (Fin n → ℝ)}
    (hb : ContDiff ℝ 1 b) (hPhi : ContDiff ℝ 1 Phi) {q v : ℝ → State n}
    (hq : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt q (vectorField lam r u gamma target b kappa rho Phi (q t)) t)
    (hv : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt v (vectorField lam r u gamma target b kappa rho Phi (v t)) t)
    (heq : q 0 = v 0) : EqOn q v (Ici (0 : ℝ)) :=
  LinearInputForwardUniqueness.solution_unique_on_Ici
    (contDiff_vectorField hb hPhi lam r u gamma target kappa rho) hq hv heq

/-- Every finite coefficient expansion has the smoothness required by the
coupled theorem; polynomial spatial basis functions are included. -/
theorem contDiff_finite_expansion {n : ℕ} {m : WithTop ℕ∞}
    {psi : Fin n → (ℝ × ℝ) → ℝ} (hpsi : ∀ i, ContDiff ℝ m (psi i)) :
    ContDiff ℝ m (fun q : State n => ∑ i, q.2 i * psi i q.1) := by
  apply ContDiff.sum
  intro i _
  have hi : ContDiff ℝ m (fun q : State n => q.2 i) := by
    simpa only [Function.comp_def] using
      (contDiff_apply ℝ (fun _ : Fin n => ℝ) i).comp (contDiff_snd (E := ℝ × ℝ))
  have hp : ContDiff ℝ m (fun q : State n => psi i q.1) := by
    simpa only [Function.comp_def] using (hpsi i).comp (contDiff_fst (F := Fin n → ℝ))
  exact hi.mul hp

/-- The original coefficient 1 + Qθ², now with genuinely evolving finite
internal coefficients, has an actual forward-global coupled solution. -/
theorem exists_global_solution_one_add_sq {n : ℕ} {lam r u gamma target : ℝ}
    {Q : State n → ℝ} {kappa rho : Fin n → ℝ} {Phi : ℝ × ℝ → (Fin n → ℝ)}
    (hQ : ContDiff ℝ 1 Q) (hPhi : ContDiff ℝ 1 Phi)
    (hlam : 0 < lam) (hgamma : 0 ≤ gamma) (hkappa : ∀ i, 0 < kappa i)
    (q₀ : State n) (hinit : target ≤ E lam r u q₀.1.1 q₀.1.2) :
    ∃ M : Fin n → ℝ, (∀ i, 0 ≤ M i) ∧ ∃ q : ℝ → State n, q 0 = q₀ ∧
      (∀ t : ℝ, 0 ≤ t → HasDerivAt q
        (vectorField lam r u gamma target (fun v => 1 + Q v ^ 2) kappa rho Phi (q t)) t) ∧
      ∀ t : ℝ, 0 ≤ t →
        (target ≤ E lam r u (q t).1.1 (q t).1.2 ∧
          E lam r u (q t).1.1 (q t).1.2 ≤ E lam r u q₀.1.1 q₀.1.2) ∧
        ∀ i, |(q t).2 i| ≤ M i :=
  exists_global_solution (contDiff_const.add (hQ.pow 2)) hPhi hlam hgamma hkappa q₀ hinit

end LinearInputCoupledTrajectory
