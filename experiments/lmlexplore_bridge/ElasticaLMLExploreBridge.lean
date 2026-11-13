import Elastica.Variation
import LMLExplore.OnlineLearning.ExponentialWeights
import LMLExplore.InformationTheory.KullbackLeibler.Finite

/-!
# A minimal interoperability experiment

This file combines Elastica's curvature energy with LMLExplore's finite
softmax and relative entropy. It retains the imported definitions; the
separate compatibility overlay changes one proof tactic in Elastica.Variation.

The first three statements identify definitions and reuse the softmax API.
The finite Gibbs variational principle below additionally reuses LMLExplore's
relative-entropy theorems: the free-energy gap is a KL divergence, and the
Gibbs weights are its unique minimizer when the inverse temperature is positive.
This is a specialization of existing mathematics to a finite indexed family,
not a claim about new variational dynamics or minimizers among all curves.
-/

noncomputable section
open Finset

namespace ElasticaLMLExploreBridge

variable {α : Type*} [Fintype α]

/-- The Gibbs distribution on a finite set of candidate curves, formed with
LMLExplore's softmax and Elastica's energy. -/
def curveGibbs (β : ℝ) (ε : ℝ → ℝ)
    (θ : α → ℝ → ℝ) (ℓ : ℝ) : α → ℝ :=
  LMLExplore.OnlineLearning.softmax
    (fun a => -β * Elastica.energy ε (θ a) ℓ)

/-- The exact curvature-energy definition imported from Elastica.Variation
agrees with LMLExplore's finite softmax weighting formula. -/
theorem curveGibbs_apply (β : ℝ) (ε : ℝ → ℝ)
    (θ : α → ℝ → ℝ) (ℓ : ℝ) (a : α) :
    curveGibbs β ε θ ℓ a =
      Real.exp (-β * Elastica.energy ε (θ a) ℓ) /
        ∑ b, Real.exp (-β * Elastica.energy ε (θ b) ℓ) := by
  rfl

/-- A nonempty family of Elastica candidates gives an LMLExplore simplex
element, as a consequence of the imported softmax theorem. -/
theorem curveGibbs_mem_simplex [Nonempty α]
    (β : ℝ) (ε : ℝ → ℝ) (θ : α → ℝ → ℝ) (ℓ : ℝ) :
    curveGibbs β ε θ ℓ ∈ LMLExplore.simplex α := by
  exact LMLExplore.OnlineLearning.softmax_mem_simplex
    (fun a => -β * Elastica.energy ε (θ a) ℓ)

/-- Each normalized weight is strictly positive on a nonempty candidate
family, using LMLExplore's previously formalized positivity result. -/
theorem curveGibbs_pos [Nonempty α]
    (β : ℝ) (ε : ℝ → ℝ) (θ : α → ℝ → ℝ) (ℓ : ℝ) (a : α) :
    0 < curveGibbs β ε θ ℓ a := by
  exact LMLExplore.OnlineLearning.softmax_pos
    (fun b => -β * Elastica.energy ε (θ b) ℓ) a

/-- Expected curvature energy plus the negative Shannon entropy divided by
the inverse temperature. The probability vector is supplied separately, so
its simplex hypothesis is explicit in the theorems. Zero coordinates are
allowed, with Lean's convention `0 * Real.log 0 = 0`. -/
def curveFreeEnergy (β : ℝ) (ε : ℝ → ℝ)
    (θ : α → ℝ → ℝ) (ℓ : ℝ) (q : α → ℝ) : ℝ :=
  (∑ a, q a * Elastica.energy ε (θ a) ℓ) +
    (∑ a, q a * Real.log (q a)) / β

/-- The imported finite relative-entropy identity splits free energy into
the negative log-partition value and a KL divergence divided by `β`.
This algebraic identity needs only `β ≠ 0`; the minimum statements below
add `β > 0`. No sign assumption on the curvature energy is needed. -/
theorem curveFreeEnergy_eq_neg_log_partition_add_kl [Nonempty α]
    {β : ℝ} (hβ : β ≠ 0) (ε : ℝ → ℝ)
    (θ : α → ℝ → ℝ) (ℓ : ℝ) {q : α → ℝ}
    (hq : q ∈ LMLExplore.simplex α) :
    curveFreeEnergy β ε θ ℓ q =
      -Real.log (∑ a, Real.exp (-β * Elastica.energy ε (θ a) ℓ)) / β +
        (∑ a, q a * Real.log (q a / curveGibbs β ε θ ℓ a)) / β := by
  have hZ : 0 < ∑ a, Real.exp (-β * Elastica.energy ε (θ a) ℓ) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  have h := LMLExplore.sum_mul_log_div_mul_exp_div_eq
    (p := fun _ : α => (1 : ℝ)) (q := q)
    (v := fun a => -β * Elastica.energy ε (θ a) ℓ)
    (LMLExplore.mem_simplex_iff.mp hq).2
    (fun _ hz => False.elim (one_ne_zero hz)) (by simpa using hZ.ne')
  simp only [one_mul, div_one] at h
  have hmul : (∑ a, q a * (-β * Elastica.energy ε (θ a) ℓ)) =
      -β * ∑ a, q a * Elastica.energy ε (θ a) ℓ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [hmul] at h
  have hscaled : curveFreeEnergy β ε θ ℓ q * β =
      (∑ a, q a * Real.log (q a / curveGibbs β ε θ ℓ a)) -
        Real.log (∑ a, Real.exp (-β * Elastica.energy ε (θ a) ℓ)) := by
    unfold curveFreeEnergy
    rw [add_mul, div_mul_cancel₀ _ hβ]
    simp only [curveGibbs_apply]
    linarith [h]
  apply mul_right_cancel₀ hβ
  rw [hscaled, add_mul, div_mul_cancel₀ _ hβ, div_mul_cancel₀ _ hβ]
  ring

/-- The value at the Gibbs weights is the finite log-partition free energy.
It has the same scalar expression used by the existing finite-temperature
partition-function development. -/
theorem curveFreeEnergy_gibbs_eq [Nonempty α]
    {β : ℝ} (hβ : β ≠ 0) (ε : ℝ → ℝ)
    (θ : α → ℝ → ℝ) (ℓ : ℝ) :
    curveFreeEnergy β ε θ ℓ (curveGibbs β ε θ ℓ) =
      -Real.log (∑ a, Real.exp (-β * Elastica.energy ε (θ a) ℓ)) / β := by
  have h := curveFreeEnergy_eq_neg_log_partition_add_kl hβ ε θ ℓ
    (curveGibbs_mem_simplex β ε θ ℓ)
  simpa only [Real.log_div_self, mul_zero, Finset.sum_const_zero, zero_div, add_zero]
    using h

/-- The free-energy gap is exactly the imported finite KL expression,
scaled by the inverse temperature. Candidate probabilities may vanish. -/
theorem curveFreeEnergy_gap_eq_kl [Nonempty α]
    {β : ℝ} (hβ : β ≠ 0) (ε : ℝ → ℝ)
    (θ : α → ℝ → ℝ) (ℓ : ℝ) {q : α → ℝ}
    (hq : q ∈ LMLExplore.simplex α) :
    curveFreeEnergy β ε θ ℓ q -
        curveFreeEnergy β ε θ ℓ (curveGibbs β ε θ ℓ) =
      (∑ a, q a * Real.log (q a / curveGibbs β ε θ ℓ a)) / β := by
  rw [curveFreeEnergy_eq_neg_log_partition_add_kl hβ ε θ ℓ hq,
    curveFreeEnergy_gibbs_eq hβ ε θ ℓ]
  ring

/-- On the finite probability simplex, the Gibbs weights minimize the
entropy-regularized expected energy for positive inverse temperature.
This does not assert a minimum over the space of all admissible curves. -/
theorem curveFreeEnergy_min [Nonempty α]
    {β : ℝ} (hβ : 0 < β) (ε : ℝ → ℝ)
    (θ : α → ℝ → ℝ) (ℓ : ℝ) {q : α → ℝ}
    (hq : q ∈ LMLExplore.simplex α) :
    curveFreeEnergy β ε θ ℓ (curveGibbs β ε θ ℓ) ≤
      curveFreeEnergy β ε θ ℓ q := by
  have hg := curveGibbs_mem_simplex β ε θ ℓ
  have hkl := LMLExplore.sum_mul_log_div_nonneg
    (LMLExplore.mem_simplex_iff.mp hq).1 (LMLExplore.mem_simplex_iff.mp hg).1
    (fun a hz => False.elim ((curveGibbs_pos β ε θ ℓ a).ne' hz))
    (by rw [(LMLExplore.mem_simplex_iff.mp hg).2,
      (LMLExplore.mem_simplex_iff.mp hq).2])
  apply sub_nonneg.mp
  rw [curveFreeEnergy_gap_eq_kl hβ.ne' ε θ ℓ hq]
  exact div_nonneg hkl hβ.le

/-- Equality in the finite free-energy minimum holds exactly at the Gibbs
probability vector, by the imported KL equality theorem. Distinct labels
may represent the same curve; uniqueness is of probabilities on the labels. -/
theorem curveFreeEnergy_eq_iff [Nonempty α]
    {β : ℝ} (hβ : 0 < β) (ε : ℝ → ℝ)
    (θ : α → ℝ → ℝ) (ℓ : ℝ) {q : α → ℝ}
    (hq : q ∈ LMLExplore.simplex α) :
    curveFreeEnergy β ε θ ℓ q =
        curveFreeEnergy β ε θ ℓ (curveGibbs β ε θ ℓ) ↔
      q = curveGibbs β ε θ ℓ := by
  have hz : curveFreeEnergy β ε θ ℓ q -
      curveFreeEnergy β ε θ ℓ (curveGibbs β ε θ ℓ) = 0 ↔
        q = curveGibbs β ε θ ℓ := by
    rw [curveFreeEnergy_gap_eq_kl hβ.ne' ε θ ℓ hq]
    simp only [div_eq_zero_iff, hβ.ne', or_false]
    exact LMLExplore.sum_mul_log_div_eq_zero_iff hq
      (curveGibbs_mem_simplex β ε θ ℓ)
      (fun a heq => False.elim ((curveGibbs_pos β ε θ ℓ a).ne' heq))
  simpa only [sub_eq_zero] using hz

end ElasticaLMLExploreBridge
