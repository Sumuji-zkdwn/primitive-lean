/-!
# A finite Elastica/operator-vocabulary bridge

Four unit-length straight rods are represented by their constant tangent angles
0, pi/2, pi, -pi/2. The readout is the existing Elastica horizontal endpoint.
The old operation is horizontal reflection; the fresh operation is a quarter-turn
on the four tangent directions (modulo full turns).

This is an existence witness for a strict quotient refinement, not a theorem
about every Elastica curve or all physically admissible deformations.
-/

noncomputable section

namespace LinearInputElasticaOperatorBridge

open LinearInputOperatorWords
open LinearInputOperatorRefinement

/-- A four-element family of constant tangent-angle lifts. -/
def angle (i : Fin 4) : ℝ :=
  if i = 0 then 0 else if i = 1 then Real.pi / 2
  else if i = 2 then Real.pi else -(Real.pi / 2)

/-- Horizontal endpoint at arclength one, reconstructed from the actual curve. -/
def observer (i : Fin 4) : ℝ :=
  Elastica.xCoord (fun _ : ℝ => angle i) 0 1

/-- Reflect the oriented straight rod across the horizontal axis. -/
def reflect (_ : Unit) (i : Fin 4) : Fin 4 :=
  if i = 1 then 3 else if i = 3 then 1 else i

/-- Rotate the geometric tangent through a quarter-turn, modulo full turns. -/
def quarterTurn (_ : Unit) (i : Fin 4) : Fin 4 :=
  if i = 0 then 1 else if i = 1 then 2
  else if i = 2 then 3 else 0

/-- All four represented Elastica rods have zero signed curvature. -/
theorem straight (i : Fin 4) (s : ℝ) :
    Elastica.curvature (fun _ : ℝ => angle i) s = 0 := by
  exact Elastica.curvature_const (angle i) s

/-- The next four results use the *existing* reconstruction theorem. -/
theorem observer_zero : observer (0 : Fin 4) = 1 := by
  simp [observer, angle, Elastica.xCoord_const]

theorem observer_one : observer (1 : Fin 4) = 0 := by
  simp [observer, angle, Elastica.xCoord_const]

theorem observer_two : observer (2 : Fin 4) = -1 := by
  simp [observer, angle, Elastica.xCoord_const]

theorem observer_three : observer (3 : Fin 4) = 0 := by
  simp [observer, angle, Elastica.xCoord_const]

/-- Every old reflection leaves this horizontal observation unchanged. -/
theorem reflect_preserves_readout (i : Fin 4) :
    observer (reflect () i) = observer i := by
  by_cases h1 : i = 1
  · subst i
    simpa [reflect] using observer_three.trans observer_one.symm
  · by_cases h3 : i = 3
    · subst i
      simpa [reflect] using observer_one.trans observer_three.symm
    · simp [reflect, h1, h3]

/-- Every word of old reflections preserves the readout. -/
theorem run_reflect_readout (word : List Unit) (i : Fin 4) :
    observer (run reflect word i) = observer i := by
  induction word generalizing i with
  | nil => rfl
  | cons a word ih =>
      change observer (run reflect word (reflect a i)) = observer i
      rw [ih (reflect a i)]
      cases a
      exact reflect_preserves_readout i

/-- The upward and downward vertical rods are old-word equivalent. -/
theorem old_indistinguishable :
    WordEq observer reflect (1 : Fin 4) (3 : Fin 4) := by
  intro word
  rw [run_reflect_readout, run_reflect_readout, observer_one, observer_three]

/-- One new quarter-turn distinguishes the same two actual rods. -/
theorem new_distinguishes :
    ¬ WordEq observer (sumStep reflect quarterTurn)
      (1 : Fin 4) (3 : Fin 4) := by
  intro h
  have hneq : observer (2 : Fin 4) ≠ observer (0 : Fin 4) := by
    rw [observer_two, observer_zero]
    norm_num
  apply hneq
  simpa [run, sumStep, quarterTurn] using (h [Sum.inr ()])

/-- Actual Elastica coordinates yield a strict split of predictive quotient states. -/
theorem elastica_quotient_splits :
    ∃ q r : State observer (sumStep reflect quarterTurn),
      q ≠ r ∧
        forget observer reflect quarterTurn q =
          forget observer reflect quarterTurn r := by
  exact strict_refinement_splits_quotient
    observer reflect quarterTurn (1 : Fin 4) (3 : Fin 4)
    old_indistinguishable new_distinguishes

end LinearInputElasticaOperatorBridge
