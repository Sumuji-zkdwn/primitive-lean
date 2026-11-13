/-!
# Quartic reaction on the first finite Laakso multigraph

The graph is the genuine first ternary binary-sheet refinement, with six
separately labelled edges (including two parallel edges). The vector field
below is a separately chosen finite-dimensional reaction-diffusion model.
It is not a theorem about a continuous Laakso space or an ODE flow.

We prove that pair averaging cannot give an autonomous update on all states.
On the synchronized four-variable subspace, the correctly mass-weighted
quotient vector field and every explicit Euler iterate do intertwine exactly.
The future-observation bridge concerns these discrete Euler maps only; no
stability, convergence to an ODE, or continuous-time existence is asserted.
-/

noncomputable section

namespace LinearInputLaaksoNonlinear

open LinearInputLaaksoFiniteGraph

theorem vectorSix_apply_two {α : Type*} (a b c d e f : α) :
    (![a, b, c, d, e, f] : Fin 6 → α) 2 = c := rfl
theorem vectorSix_apply_three {α : Type*} (a b c d e f : α) :
    (![a, b, c, d, e, f] : Fin 6 → α) 3 = d := rfl
theorem vectorSix_apply_four {α : Type*} (a b c d e f : α) :
    (![a, b, c, d, e, f] : Fin 6 → α) 4 = e := rfl
theorem vectorSix_apply_five {α : Type*} (a b c d e f : α) :
    (![a, b, c, d, e, f] : Fin 6 → α) 5 = f := rfl
theorem vectorFour_apply_two {α : Type*} (a b c d : α) :
    (![a, b, c, d] : Fin 4 → α) 2 = c := rfl
theorem vectorFour_apply_three {α : Type*} (a b c d : α) :
    (![a, b, c, d] : Fin 4 → α) 3 = d := rfl
theorem vectorThree_apply_two {α : Type*} (a b c : α) :
    (![a, b, c] : Fin 3 → α) 2 = c := rfl

attribute [local simp] vectorSix_apply_two vectorSix_apply_three vectorSix_apply_four
  vectorSix_apply_five vectorFour_apply_two vectorFour_apply_three vectorThree_apply_two

abbrev FineState := Fin 6 → ℝ
abbrev SyncState := Fin 4 → ℝ

/-- The local reaction chosen in the previous Laakso experiments. -/
def reaction (x : ℝ) : ℝ := 3 * x - 4 * x ^ 3

/-- Incidence-sum Laplacian; summing edge IDs counts both parallel edges. -/
def fineLaplacian (x : FineState) (v : Fin 6) : ℝ :=
  ∑ e : Fin 6,
    ((if firstSource e = v then x v - x (firstTarget e) else 0) +
      (if firstTarget e = v then x v - x (firstSource e) else 0))

set_option maxRecDepth 4096 in
/-- Coordinate form derived from the six labelled graph edges. -/
theorem fineLaplacian_coordinates (x : FineState) :
    fineLaplacian x =
      ![x 0 - x 4, x 1 - x 4, x 2 - x 5, x 3 - x 5,
        4 * x 4 - x 0 - x 1 - 2 * x 5,
        4 * x 5 - x 2 - x 3 - 2 * x 4] := by
  funext v
  fin_cases v <;>
    simp only [fineLaplacian, firstSource, firstTarget, Fin.sum_univ_succ,
      Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_succ', add_zero] <;>
    norm_num [Fin.ext_iff] <;> ring!

/-- An explicitly chosen cubic reaction with graph diffusion. -/
def fineField (coupling : ℝ) (x : FineState) : FineState :=
  fun v => reaction (x v) - coupling * fineLaplacian x v

/-- Mean of the two left endpoints and mean of the two right endpoints.
The internal wormholes are deliberately forgotten by this observation. -/
def pairMean (x : FineState) : ℝ × ℝ :=
  ((x 0 + x 1) / 2, (x 2 + x 3) / 2)

def uniformWitness : FineState := ![1/2, 1/2, 1/2, 1/2, 1/2, 1/2]
def splitWitness : FineState := ![3/4, 1/4, 1/2, 1/2, 1/2, 1/2]

theorem witnesses_same_mean : pairMean uniformWitness = pairMean splitWitness := by
  norm_num [pairMean, uniformWitness, splitWitness]

theorem uniformWitness_projected_field (coupling : ℝ) :
    pairMean (fineField coupling uniformWitness) = (1, 1) := by
  simp only [pairMean, fineField, fineLaplacian_coordinates]
  norm_num [uniformWitness, reaction]

theorem splitWitness_projected_field (coupling : ℝ) :
    pairMean (fineField coupling splitWitness) = (5 / 8, 1) := by
  simp only [pairMean, fineField, fineLaplacian_coordinates]
  ext <;> norm_num [splitWitness, reaction]

/-- Failure of factorization holds for every real diffusion coefficient. -/
theorem pairMean_field_does_not_descend (coupling : ℝ) :
    ¬ ∃ V : (ℝ × ℝ) → (ℝ × ℝ),
      ∀ x, pairMean (fineField coupling x) = V (pairMean x) := by
  rintro ⟨V, h⟩
  have hx := h uniformWitness
  have hy := h splitWitness
  rw [uniformWitness_projected_field] at hx
  rw [splitWitness_projected_field] at hy
  rw [← witnesses_same_mean] at hy
  have hbad := congrArg Prod.fst (hx.trans hy.symm)
  norm_num at hbad

/-- Embed four variables by synchronizing only the duplicate endpoints.
The two wormhole variables remain separate. -/
def syncLift (q : SyncState) : FineState := ![q 0, q 0, q 1, q 1, q 2, q 3]

def syncRead (x : FineState) : SyncState := ![x 0, x 2, x 4, x 5]

theorem syncRead_syncLift (q : SyncState) : syncRead (syncLift q) = q := by
  funext v
  fin_cases v <;> rfl

theorem syncLift_injective : Function.Injective syncLift := by
  intro q r h
  simpa only [syncRead_syncLift] using congrArg syncRead h

/-- Quotient path: left--first wormhole--second wormhole--right. -/
def syncSource : Fin 3 → Fin 4 := ![0, 2, 3]
def syncTarget : Fin 3 → Fin 4 := ![2, 3, 1]

/-- These masses are the multiplicities of vertices under synchronization. -/
def syncMass : Fin 4 → ℝ := ![2, 2, 1, 1]

/-- Each quotient path edge collects two fine edges. -/
def syncConductance (_ : Fin 3) : ℝ := 2

/-- The vertex and edge maps underlying the synchronized quotient. -/
def syncVertexMap : Fin 6 → Fin 4 := ![0, 0, 1, 1, 2, 3]
def syncEdgeMap : Fin 6 → Fin 3 := ![0, 0, 1, 1, 2, 2]

theorem syncLift_apply (q : SyncState) (v : Fin 6) :
    syncLift q v = q (syncVertexMap v) := by
  fin_cases v <;> rfl

theorem syncSource_commutes (e : Fin 6) :
    syncVertexMap (firstSource e) = syncSource (syncEdgeMap e) := by
  fin_cases e <;> rfl

theorem syncTarget_commutes (e : Fin 6) :
    syncVertexMap (firstTarget e) = syncTarget (syncEdgeMap e) := by
  fin_cases e <;> rfl

/-- Vertex masses and edge conductances are counted from the actual fine
graph; they are not weights assumed merely to force intertwining. -/
theorem syncMass_eq_multiplicity (v : Fin 4) :
    syncMass v = ∑ w : Fin 6, (if syncVertexMap w = v then (1 : ℝ) else 0) := by
  fin_cases v <;>
    simp only [syncMass, syncVertexMap, Fin.sum_univ_succ, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Matrix.cons_val_succ', Fin.sum_univ_zero, add_zero]
    <;> norm_num [Fin.ext_iff]

theorem syncConductance_eq_multiplicity (e : Fin 3) :
    syncConductance e = ∑ f : Fin 6, (if syncEdgeMap f = e then (1 : ℝ) else 0) := by
  fin_cases e <;>
    simp only [syncConductance, syncEdgeMap, Fin.sum_univ_succ, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero]
    <;> norm_num [Fin.ext_iff]

theorem syncMass_pos (v : Fin 4) : 0 < syncMass v := by
  fin_cases v <;> norm_num [syncMass]

/-- Mass-weighted graph Laplacian of the synchronized four-variable model. -/
def syncLaplacian (q : SyncState) (v : Fin 4) : ℝ :=
  (∑ e : Fin 3, syncConductance e *
    ((if syncSource e = v then q v - q (syncTarget e) else 0) +
      (if syncTarget e = v then q v - q (syncSource e) else 0))) / syncMass v

set_option maxRecDepth 4096 in
theorem syncLaplacian_coordinates (q : SyncState) :
    syncLaplacian q =
      ![q 0 - q 2, q 1 - q 3,
        4 * q 2 - 2 * q 0 - 2 * q 3,
        4 * q 3 - 2 * q 1 - 2 * q 2] := by
  funext v
  fin_cases v <;>
    simp only [syncLaplacian, syncSource, syncTarget, syncMass,
      syncConductance, Fin.sum_univ_succ, Fin.sum_univ_zero,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_succ', add_zero] <;>
    norm_num [Fin.ext_iff] <;> ring!

def syncField (coupling : ℝ) (q : SyncState) : SyncState :=
  fun v => reaction (q v) - coupling * syncLaplacian q v

/-- Exact vector-field intertwining on the synchronized subspace. -/
theorem fineField_syncLift (coupling : ℝ) (q : SyncState) :
    fineField coupling (syncLift q) = syncLift (syncField coupling q) := by
  funext v
  fin_cases v <;>
    simp only [fineField, syncField, fineLaplacian_coordinates,
      syncLaplacian_coordinates, syncLift, Matrix.cons_val_zero,
      Matrix.cons_val_zero', Matrix.cons_val_one, Matrix.cons_val_succ', vectorSix_apply_two,
      vectorSix_apply_three, vectorSix_apply_four, vectorSix_apply_five,
      vectorFour_apply_two, vectorFour_apply_three] <;> ring

/-- Explicit Euler is used as a discrete update, at any real step size. -/
def fineStep (coupling step : ℝ) (x : FineState) : FineState :=
  fun v => x v + step * fineField coupling x v

def syncStep (coupling step : ℝ) (q : SyncState) : SyncState :=
  fun v => q v + step * syncField coupling q v

/-- A discrete semiconjugacy, not an analytic integration theorem. -/
theorem fineStep_syncLift (coupling step : ℝ) (q : SyncState) :
    fineStep coupling step (syncLift q) = syncLift (syncStep coupling step q) := by
  funext v
  simp only [fineStep, fineField_syncLift]
  fin_cases v <;> rfl

/-- Existing predictive-representation machinery propagates this identity
through every finite number of Euler steps. -/
theorem fineStep_iterate_syncLift (coupling step : ℝ) (t : ℕ) (q : SyncState) :
    (fineStep coupling step)^[t] (syncLift q) =
      syncLift ((syncStep coupling step)^[t] q) := by
  symm
  exact LinearInputFutureObservation.representation_iterate
    (syncStep coupling step) (fineStep coupling step) syncLift
    (fun q => (fineStep_syncLift coupling step q).symm) t q

/-- Observations of the synchronized fine evolution are precisely those
of the four-variable discrete model. -/
theorem synchronized_future_iff {Ω : Type*} (K : FineState → Ω)
    (coupling step : ℝ) (q r : SyncState) :
    LinearInputFutureObservation.FutureEq K (fineStep coupling step)
        (syncLift q) (syncLift r) ↔
      LinearInputFutureObservation.FutureEq (fun z => K (syncLift z))
        (syncStep coupling step) q r := by
  constructor <;> intro h t
  · simpa only [fineStep_iterate_syncLift] using h t
  · simpa only [fineStep_iterate_syncLift] using h t

theorem uniformWitness_projected_step (coupling step : ℝ) :
    pairMean (fineStep coupling step uniformWitness) =
      (1 / 2 + step, 1 / 2 + step) := by
  simp only [pairMean, fineStep, fineField, fineLaplacian_coordinates]
  ext <;> norm_num [uniformWitness, reaction]

theorem splitWitness_projected_step (coupling step : ℝ) :
    pairMean (fineStep coupling step splitWitness) =
      (1 / 2 + step * (5 / 8), 1 / 2 + step) := by
  simp only [pairMean, fineStep, fineField, fineLaplacian_coordinates]
  ext <;> norm_num [splitWitness, reaction]
  ring

theorem witnesses_different_next_mean (coupling step : ℝ) (hstep : step ≠ 0) :
    pairMean (fineStep coupling step uniformWitness) ≠
      pairMean (fineStep coupling step splitWitness) := by
  intro h
  rw [uniformWitness_projected_step, splitWitness_projected_step] at h
  have hleft := congrArg Prod.fst h
  apply hstep
  linarith

/-- Even discrete Euler updates cannot descend through endpoint means on
all states, for any nonzero step size. -/
theorem pairMean_step_does_not_descend (coupling step : ℝ) (hstep : step ≠ 0) :
    ¬ ∃ V : (ℝ × ℝ) → (ℝ × ℝ),
      ∀ x, pairMean (fineStep coupling step x) = V (pairMean x) := by
  rintro ⟨V, h⟩
  apply witnesses_different_next_mean coupling step hstep
  rw [h, h, witnesses_same_mean]

/-- Same current observation, but distinct future-observation classes. -/
theorem witnesses_not_futureEq (coupling step : ℝ) (hstep : step ≠ 0) :
    ¬ LinearInputFutureObservation.FutureEq pairMean (fineStep coupling step)
      uniformWitness splitWitness := by
  intro h
  apply witnesses_different_next_mean coupling step hstep
  simpa only [Function.iterate_one] using h 1

theorem witnesses_predictive_states_distinct (coupling step : ℝ) (hstep : step ≠ 0) :
    LinearInputFutureObservation.encode pairMean (fineStep coupling step) uniformWitness ≠
      LinearInputFutureObservation.encode pairMean (fineStep coupling step) splitWitness := by
  intro h
  exact witnesses_not_futureEq coupling step hstep
    ((LinearInputFutureObservation.encode_iff_future uniformWitness splitWitness).1 h)

end LinearInputLaaksoNonlinear
