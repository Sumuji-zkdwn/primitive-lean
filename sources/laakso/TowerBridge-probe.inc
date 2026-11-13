/-!
# Set-level inverse-tower feasibility probe

This is an abstract algebraic bridge for a prospective Laakso construction.
It does not construct a Laakso space, topology, metric, measure, geodesics,
Hausdorff dimension, or a Poincare inequality. No geometric conclusion is
inferred from the compatible-coordinate equations.

The preceding source fragment is primitive-lean's exact FutureObservations.inc.
See source_manifest.json for its commit, tree, path, and SHA-256.
-/

namespace LaaksoTowerProbe

universe u v

variable (X : ℕ → Type u) (p : (n : ℕ) → X (n + 1) → X n)

/-- Set-level compatible sequences of a tower. -/
def Limit := {x : (n : ℕ) → X n // ∀ n, p n (x (n + 1)) = x n}

def project (n : ℕ) (x : Limit X p) : X n := x.val n

theorem project_compatible (n : ℕ) (x : Limit X p) :
    p n (project X p (n + 1) x) = project X p n x := x.property n

variable (U : (n : ℕ) → X n → X n)
variable (hU : ∀ n z, p n (U (n + 1) z) = U n (p n z))

/-- A compatible family of updates acts coordinatewise on the limit set. -/
def update (x : Limit X p) : Limit X p :=
  ⟨fun n => U n (x.val n), fun n => by
    calc
      p n (U (n + 1) (x.val (n + 1))) = U n (p n (x.val (n + 1))) := hU n _
      _ = U n (x.val n) := congrArg (U n) (x.property n)⟩

/-- Every projection is an exact semiconjugacy. -/
theorem project_update (n : ℕ) (x : Limit X p) :
    project X p n (update X p U hU x) = U n (project X p n x) := rfl

/-- The existing representation-iterate theorem gives all finite times. -/
theorem project_iterate (n t : ℕ) (x : Limit X p) :
    project X p n ((update X p U hU)^[t] x) =
      (U n)^[t] (project X p n x) :=
  LinearInputFutureObservation.representation_iterate
    (update X p U hU) (U n) (project X p n) (project_update X p U hU n) t x

/-- Existing predictive-kernel minimality applies to each level observation. -/
theorem same_projection_same_future (n : ℕ) {ω : Type v} (K : X n → ω)
    {x y : Limit X p} (hxy : project X p n x = project X p n y) :
    LinearInputFutureObservation.FutureEq
      (fun z => K (project X p n z)) (update X p U hU) x y :=
  LinearInputFutureObservation.predictive_kernel_sub
    (fun z => K (project X p n z)) (update X p U hU)
    (project X p n) (U n) K (fun _ => rfl)
    (project_update X p U hU n) hxy

/-- Full projected traces agree exactly with the corresponding level traces. -/
theorem projected_future_iff (n : ℕ) {ω : Type v} (K : X n → ω)
    (x y : Limit X p) :
    LinearInputFutureObservation.FutureEq
      (fun z => K (project X p n z)) (update X p U hU) x y ↔
    LinearInputFutureObservation.FutureEq K (U n)
      (project X p n x) (project X p n y) := by
  constructor
  · intro h t
    have ht := h t
    change K (project X p n ((update X p U hU)^[t] x)) =
      K (project X p n ((update X p U hU)^[t] y)) at ht
    simpa only [project_iterate] using ht
  · intro h t
    change K (project X p n ((update X p U hU)^[t] x)) =
      K (project X p n ((update X p U hU)^[t] y))
    simpa only [project_iterate] using h t

/-- All coordinates jointly separate compatible sequences; one need not. -/
theorem all_projections_separate (x y : Limit X p) :
    (∀ n, project X p n x = project X p n y) ↔ x = y := by
  constructor
  · intro h
    apply Subtype.ext
    funext n
    exact h n
  · intro h
    subst y
    intro n
    rfl

/-! A concrete scalar obstruction from the discussed cubic reaction.
This is a two-scalar algebraic witness, not a formalization of a graph
Laplacian or of an entire Laakso approximant. -/

def pairAverage (z : ℝ × ℝ) : ℝ := (z.1 + z.2) / 2

def reaction (a : ℝ) : ℝ := 3 * a - 4 * a ^ 3

def reactionPair (z : ℝ × ℝ) : ℝ × ℝ := (reaction z.1, reaction z.2)

theorem cubic_average_witness :
    pairAverage ((1 / 2 : ℝ), (1 / 2 : ℝ)) =
      pairAverage ((3 / 4 : ℝ), (1 / 4 : ℝ)) ∧
    pairAverage (reactionPair ((1 / 2 : ℝ), (1 / 2 : ℝ))) = 1 ∧
    pairAverage (reactionPair ((3 / 4 : ℝ), (1 / 4 : ℝ))) = 5 / 8 := by
  norm_num [pairAverage, reactionPair, reaction]

/-- No deterministic scalar update exactly represents this pair reaction
through averaging on every real pair. -/
theorem cubic_reaction_does_not_descend :
    ¬ ∃ V : ℝ → ℝ, ∀ z : ℝ × ℝ,
      pairAverage (reactionPair z) = V (pairAverage z) := by
  rintro ⟨V, h⟩
  have hx := h ((1 / 2 : ℝ), (1 / 2 : ℝ))
  have hy := h ((3 / 4 : ℝ), (1 / 4 : ℝ))
  norm_num [pairAverage, reactionPair, reaction] at hx hy
  have hbad : (1 : ℝ) = 5 / 8 := hx.trans hy.symm
  norm_num at hbad

#print axioms Limit
#print axioms project
#print axioms project_compatible
#print axioms update
#print axioms project_update
#print axioms project_iterate
#print axioms same_projection_same_future
#print axioms projected_future_iff
#print axioms all_projections_separate
#print axioms pairAverage
#print axioms reaction
#print axioms reactionPair
#print axioms cubic_average_witness
#print axioms cubic_reaction_does_not_descend

end LaaksoTowerProbe
