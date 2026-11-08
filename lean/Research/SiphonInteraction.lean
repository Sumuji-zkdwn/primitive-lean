import Mathlib

/-!
# Siphon paths as a minimal interaction/rewriting model

The path observable is a *chosen* integer-valued potential difference.
It is not a claim that geometric height alone determines water flow.
The complete directed interaction law is a potential difference exactly when
its triple-composition law holds.  The numerical path-cost counterexample
exhibits a quantity that is not determined by endpoints.

Independent check: tests/test_siphon_interaction.py
-/

namespace Elastica.SiphonInteraction

variable {α : Type*}

/-- The local interaction induced by a chosen state observable E. -/
def step (E : α → ℤ) (a b : α) : ℤ := E b - E a

/-- An exact local interaction composes through every intermediate state. -/
theorem step_comp (E : α → ℤ) (a b c : α) :
    step E a b + step E b c = step E a c := by
  dsimp [step]
  omega

/-- Read an operation word as consecutive changes of a single state E. -/
def pathSum (E : α → ℤ) (a : α) : List α → ℤ
  | [] => 0
  | b :: bs => step E a b + pathSum E b bs

/-- The endpoint reached after reading the operation word. -/
def endpoint (a : α) : List α → α
  | [] => a
  | b :: bs => endpoint b bs

/-- Every finite word telescopes, including the empty word. -/
theorem path_sum_eq_endpoint (E : α → ℤ) (a : α) (bs : List α) :
    pathSum E a bs = E (endpoint a bs) - E a := by
  induction bs generalizing a with
  | nil => simp [pathSum, endpoint]
  | cons b bs ih =>
      simp only [pathSum, endpoint]
      rw [ih b]
      dsimp [step]
      omega

/-- Any rewriting of the interior of a word that preserves endpoints also
preserves its accumulated exact interaction. -/
theorem rewrite_invariant (E : α → ℤ) (a : α) (xs ys : List α)
    (h : endpoint a xs = endpoint a ys) :
    pathSum E a xs = pathSum E a ys := by
  rw [path_sum_eq_endpoint, path_sum_eq_endpoint, h]

/-- A general pair interaction; no potential is assumed. -/
def HasChain (w : α → α → ℤ) : Prop :=
  ∀ a b c, w a b + w b c = w a c

/-- The interaction is induced by a single state observable. -/
def HasPotential (w : α → α → ℤ) : Prop :=
  ∃ E : α → ℤ, ∀ a b, w a b = E b - E a

/-- On a nonempty complete network, the triple-composition law is *equivalent*
to the existence of a state potential. The anchor fixes the additive gauge. -/
theorem chain_iff_potential (w : α → α → ℤ) (anchor : α) :
    HasChain w ↔ HasPotential w := by
  constructor
  · intro h
    refine ⟨fun x => w anchor x, ?_⟩
    intro a b
    have hab := h anchor a b
    omega
  · rintro ⟨E, hE⟩
    intro a b c
    rw [hE a b, hE b c, hE a c]
    omega

/-- Non-exact path costs need not be insensitive to refinement. -/
def pathCost (w : α → α → ℤ) (a : α) : List α → ℤ
  | [] => 0
  | b :: bs => w a b + pathCost w b bs

/-- The two paths have the same starting and ending heights. -/
example :
    pathSum (fun x : ℤ => x) 1 [4, 0] =
    pathSum (fun x : ℤ => x) 1 [4, 2, 0] := by
  norm_num [pathSum, step]

/-- One unit of interaction cost per segment distinguishes the two paths. -/
example :
    pathCost (fun (_ : ℤ) (_ : ℤ) => (1 : ℤ)) 1 [4, 0] ≠
    pathCost (fun (_ : ℤ) (_ : ℤ) => (1 : ℤ)) 1 [4, 2, 0] := by
  norm_num [pathCost]

/-- A three-state pair law can fail the chain law and thus cannot be obtained
from any globally defined scalar E. -/
theorem nonexact_three :
    ¬ HasChain (fun (a b : Fin 3) =>
      if a = 0 ∧ b = 1 then (1 : ℤ) else 0) := by
  intro h
  have h012 := h 0 1 2
  norm_num at h012

end Elastica.SiphonInteraction

#print axioms Elastica.SiphonInteraction.path_sum_eq_endpoint
#print axioms Elastica.SiphonInteraction.rewrite_invariant
#print axioms Elastica.SiphonInteraction.chain_iff_potential
#print axioms Elastica.SiphonInteraction.nonexact_three
