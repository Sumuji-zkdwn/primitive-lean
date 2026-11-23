import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-!
# Compactness of nested gate constraints

The key continuum passage for the Laakso gate sweep is a compactness
argument, not a finite experiment. For arbitrary closed nested subsets
F_n of a compact ambient set and any continuous real cost f, the following
theorem shows that satisfying EVERY finite constraint at a common
cost threshold A is equivalent to a single point satisfying ALL constraints.

The hypotheses that the actual ternary gate constraints are closed,
nested and nonempty, and the identification of finite walk costs with
these constraints, remain to be supplied in the model-specific module.
-/

namespace LaaksoNestedGateCompactness

universe u
variable {X : Type u} [TopologicalSpace X]

/-- Compactness upgrades uniform finite-stage feasibility at a fixed
cost threshold into a common solution of all stages. -/
theorem exists_global_bounded_of_all_finite_bounded
    (K : Set X) (hK : IsCompact K)
    (F : ℕ → Set X)
    (hFK : ∀ n, F n ⊆ K)
    (hclosed : ∀ n, IsClosed (F n))
    (hdecr : ∀ n, F (n + 1) ⊆ F n)
    (f : X → ℝ) (hf : Continuous f) (A : ℝ)
    (hfeasible : ∀ n, ∃ x : X, x ∈ F n ∧ f x ≤ A) :
    ∃ x : X, (∀ n, x ∈ F n) ∧ f x ≤ A := by
  let T : ℕ → Set X := fun n => F n ∩ {x | f x ≤ A}
  have hTc : ∀ n, IsClosed (T n) := by
    intro n
    exact (hclosed n).inter (isClosed_Iic.preimage hf)
  have hTdecr : ∀ n, T (n + 1) ⊆ T n := by
    intro n x hx
    exact ⟨hdecr n hx.1, hx.2⟩
  have hTnonempty : ∀ n, (T n).Nonempty := by
    intro n
    obtain ⟨x, hx, hfx⟩ := hfeasible n
    exact ⟨x, ⟨hx, hfx⟩⟩
  have hTK : T 0 ⊆ K := by
    intro x hx
    exact hFK 0 hx.1
  have hTcompact : IsCompact (T 0) :=
    hK.of_isClosed_subset (hTc 0) hTK
  obtain ⟨x, hx⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      T hTdecr hTnonempty hTcompact hTc
  have hall : ∀ n, x ∈ T n := Set.mem_iInter.mp hx
  exact ⟨x, (fun n => (hall n).1), (hall 0).2⟩

/-- The exact threshold-level equivalence behind the limit of finite
gate metrics. In particular, it forbids 'phantom' limiting finite
paths without a common admissible interval when compactness holds. -/
theorem infinite_cost_threshold_iff
    (K : Set X) (hK : IsCompact K)
    (F : ℕ → Set X)
    (hFK : ∀ n, F n ⊆ K)
    (hclosed : ∀ n, IsClosed (F n))
    (hdecr : ∀ n, F (n + 1) ⊆ F n)
    (f : X → ℝ) (hf : Continuous f) (A : ℝ) :
    (∃ x : X, (∀ n, x ∈ F n) ∧ f x ≤ A) ↔
      (∀ n, ∃ x : X, x ∈ F n ∧ f x ≤ A) := by
  constructor
  · rintro ⟨x, hx, hfx⟩ n
    exact ⟨x, hx n, hfx⟩
  · exact exists_global_bounded_of_all_finite_bounded
      K hK F hFK hclosed hdecr f hf A

#print axioms exists_global_bounded_of_all_finite_bounded
#print axioms infinite_cost_threshold_iff

end LaaksoNestedGateCompactness
