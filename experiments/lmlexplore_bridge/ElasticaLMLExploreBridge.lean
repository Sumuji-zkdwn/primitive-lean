import Elastica.Variation
import LMLExplore.OnlineLearning.ExponentialWeights

/-!
# A minimal interoperability experiment

This file combines two independently developed definitions without rewriting
either source: Elastica's curve energy/exponential weight and LMLExplore's
softmax on finite types.

The crucial statement is an *identification of definitions*, not a claim
about new variational dynamics or a newly discovered mathematical theorem.
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

end ElasticaLMLExploreBridge
