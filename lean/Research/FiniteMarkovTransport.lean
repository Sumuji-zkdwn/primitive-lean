import Mathlib.Tactic
import Research.OkanoharaTransport

/-!
## A finite Markov derivation of history-conditioned quadratic effort

The state space and action alphabet are finite. A past operation updates a
hidden two-valued history while leaving the observed position unchanged. The
future transition kernel then has history-dependent gain 1 or 1/3. For the
target mass 1/3, exact finite optimization derives the one-step effort ratio
1:9 and the two-step effort ratio 1:9. The two-step result agrees with the
curvature Gramian special case already present in `OkanoharaTransport`.

This is a chosen finite controlled kernel. The gain law is not derived from
measured fibers, continuum fluid mechanics, or Okanohara's general theory.
-/

namespace Elastica
namespace FiniteMarkov

abbrev Position := Fin 2
abbrev History := Fin 2
abbrev Control := Fin 4
abbrev ExtendedState := Position × History

/-- A rational Markov kernel on `Fin n`, with each row a probability mass. -/
def IsProbabilityKernel {n : ℕ} (K : Fin n → Fin n → ℚ) : Prop :=
  (∀ x y, 0 ≤ K x y) ∧ ∀ x, ∑ y : Fin n, K x y = 1

inductive PastOperation where
  | relax
  | prime
  deriving DecidableEq, Fintype

/-- The last operation is retained as a two-state hidden history. -/
def updateHistory (_old : History) (op : PastOperation) : History :=
  match op with
  | .relax => 0
  | .prime => 1

/-- The observable reads position and forgets the history register. -/
def observe (s : ExtendedState) : Position := s.1

def applyPastOperation (s : ExtendedState) (op : PastOperation) : ExtendedState :=
  (s.1, updateHistory s.2 op)

/-- A deterministic probability kernel for the hidden-history update. -/
def historyKernel (op : PastOperation) (h h' : History) : ℚ :=
  if h' = updateHistory h op then 1 else 0

theorem historyKernel_is_probability_kernel (op : PastOperation) :
    IsProbabilityKernel (historyKernel op) := by
  unfold IsProbabilityKernel
  constructor
  · intro h h'
    by_cases hh : h' = updateHistory h op <;>
      simp [historyKernel, hh]
  · intro h
    fin_cases h <;> cases op <;>
      norm_num [historyKernel, updateHistory, Fin.sum_univ_two]

theorem same_readout_after_different_operations :
    observe (applyPastOperation ((0 : Position), (0 : History)) .relax) =
      observe (applyPastOperation ((0 : Position), (0 : History)) .prime) ∧
    (applyPastOperation ((0 : Position), (0 : History)) .relax).2 ≠
      (applyPastOperation ((0 : Position), (0 : History)) .prime).2 := by
  simp [observe, applyPastOperation, updateHistory]

/-- The two histories select unit stiffness or stiffness three. -/
def historyStiffness (h : History) : ℚ := if h = 0 then 1 else 3

/-- Each finite control contributes a value in {0, 1/6, 1/3, 1/2}. -/
def controlValue (a : Control) : ℚ := (a.val : ℚ) / 6

/-- Two signed scalar controls produce endpoint mass `(u+v)/k(h)`.
The endpoint is a two-state probability distribution because `u+v ≤ 1`. -/
def endpointMass (h : History) (a b : Control) : ℚ :=
  (controlValue a + controlValue b) / historyStiffness h

/-- Controlled transition kernel on the finite position state `Fin 2`.
State 0 moves to 1 with the endpoint probability; state 1 is absorbing. -/
def controlledKernel (h : History) (a b : Control) (x y : Position) : ℚ :=
  if x = 0 then
    if y = 1 then endpointMass h a b else 1 - endpointMass h a b
  else if y = 1 then 1 else 0

theorem controlledKernel_is_probability_kernel (h : History) (a b : Control) :
    IsProbabilityKernel (controlledKernel h a b) := by
  unfold IsProbabilityKernel
  constructor
  · intro x y
    fin_cases x <;> fin_cases y <;> fin_cases h <;> fin_cases a <;>
      fin_cases b <;>
      norm_num [controlledKernel, endpointMass, controlValue, historyStiffness]
  · intro x
    fin_cases x <;> fin_cases h <;> fin_cases a <;> fin_cases b <;>
      norm_num [controlledKernel, endpointMass, controlValue, historyStiffness,
        Fin.sum_univ_two]

/-- The quadratic action is kept separate from the transition rule. -/
def quadraticAction (a b : Control) : ℚ :=
  controlValue a ^ 2 + controlValue b ^ 2

def bestPair (h : History) : Control × Control :=
  if h = 0 then (1, 1) else (3, 3)

def finiteMinimumAction (h : History) : ℚ :=
  quadraticAction (bestPair h).1 (bestPair h).2

def reachesTarget (h : History) (a b : Control) : Prop :=
  endpointMass h a b = 1 / 3

theorem best_pair_reaches_target (h : History) :
    reachesTarget h (bestPair h).1 (bestPair h).2 := by
  fin_cases h <;>
    norm_num [reachesTarget, endpointMass, bestPair, controlValue, historyStiffness]

/-- The selected action pair attains the minimum over this finite control set. -/
theorem every_target_pair_has_minimum_action
    (h : History) (a b : Control) (ht : reachesTarget h a b) :
    finiteMinimumAction h ≤ quadraticAction a b := by
  fin_cases h <;> fin_cases a <;> fin_cases b <;>
    norm_num [reachesTarget, endpointMass, finiteMinimumAction, bestPair,
      quadraticAction, controlValue, historyStiffness] at ht <;>
    norm_num [finiteMinimumAction, bestPair, quadraticAction, controlValue,
      historyStiffness]

theorem finite_minimum_action_values :
    finiteMinimumAction (0 : History) = 1 / 18 ∧
    finiteMinimumAction (1 : History) = 1 / 2 := by
  norm_num [finiteMinimumAction, bestPair, quadraticAction, controlValue,
    historyStiffness]

theorem finite_markov_action_matches_curvature_gramian :
    ((finiteMinimumAction (0 : History) : ℚ) : ℝ) =
        curvatureTwoStepMinCost false (1 / 3) ∧
    ((finiteMinimumAction (1 : History) : ℚ) : ℝ) =
        curvatureTwoStepMinCost true (1 / 3) := by
  constructor
  · norm_num [finiteMinimumAction, bestPair, quadraticAction, controlValue,
      historyStiffness, curvatureTwoStepMinCost, wellStiffness,
      wellCurvatureResponse, leftCurvatureResponse, rightCurvatureResponse]
  · norm_num [finiteMinimumAction, bestPair, quadraticAction, controlValue,
      historyStiffness, curvatureTwoStepMinCost, wellStiffness,
      wellCurvatureResponse, leftCurvatureResponse, rightCurvatureResponse]

theorem finite_markov_action_is_half_existing_required_action :
    ((finiteMinimumAction (0 : History) : ℚ) : ℝ) =
        requiredAction 0 (1 / 3) / 2 ∧
    ((finiteMinimumAction (1 : History) : ℚ) : ℝ) =
        requiredAction 2 (1 / 3) / 2 := by
  constructor <;>
    norm_num [finiteMinimumAction, bestPair, quadraticAction, controlValue,
      historyStiffness, requiredAction, requiredInput]

/-! The finite optimal transport comparison uses the squared two-point metric:
the cost is one for a move from 0 to 1 and zero for staying put. A coupling
from `δ₀` to mass `d` at 1 is forced, so its cost is exactly `d`. -/

abbrev TransportPlan := Position → Position → ℚ

def canonicalPlan (d : ℚ) (x y : Position) : ℚ :=
  if x = 0 then if y = 0 then 1 - d else if y = 1 then d else 0 else 0

def sourceMarginal (π : TransportPlan) (x : Position) : ℚ :=
  π x 0 + π x 1

def targetMarginal (π : TransportPlan) (y : Position) : ℚ :=
  π 0 y + π 1 y

/-- Couplings from source `δ₀` to `((1-d)δ₀ + dδ₁)`, stated by marginals
and nonnegative rational masses rather than by fixing their four entries. -/
def IsTargetCoupling (d : ℚ) (π : TransportPlan) : Prop :=
  0 ≤ d ∧ d ≤ 1 ∧
  (∀ x y, 0 ≤ π x y) ∧
  sourceMarginal π 0 = 1 ∧ sourceMarginal π 1 = 0 ∧
  targetMarginal π 0 = 1 - d ∧ targetMarginal π 1 = d

def twoPointTransportCost (π : TransportPlan) : ℚ := π 0 1 + π 1 0

theorem canonical_plan_is_target_coupling (d : ℚ) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    IsTargetCoupling d (canonicalPlan d) := by
  refine ⟨hd0, hd1, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    fin_cases x <;> fin_cases y <;> norm_num [canonicalPlan] <;> linarith
  · norm_num [sourceMarginal, canonicalPlan]
  · norm_num [sourceMarginal, canonicalPlan]
  · norm_num [targetMarginal, canonicalPlan]
  · norm_num [targetMarginal, canonicalPlan]

theorem every_target_coupling_has_cost (d : ℚ) (π : TransportPlan)
    (hc : IsTargetCoupling d π) : twoPointTransportCost π = d := by
  rcases hc with ⟨_, _, hnonneg, _, hrow1, _, hcol1⟩
  change π 1 0 + π 1 1 = 0 at hrow1
  change π 0 1 + π 1 1 = d at hcol1
  have h10 : π 1 0 = 0 := by nlinarith [hnonneg 1 0, hnonneg 1 1]
  have h11 : π 1 1 = 0 := by nlinarith [hnonneg 1 0, hnonneg 1 1]
  have h01 : π 0 1 = d := by linarith
  unfold twoPointTransportCost
  rw [h01, h10]
  ring

def inducedPlan (h : History) (a b : Control) : TransportPlan :=
  fun x y => if x = 0 then controlledKernel h a b 0 y else 0

theorem best_pair_induces_target_coupling (h : History) :
    IsTargetCoupling (1 / 3)
      (inducedPlan h (bestPair h).1 (bestPair h).2) := by
  have hplan : inducedPlan h (bestPair h).1 (bestPair h).2 = canonicalPlan (1 / 3) := by
    funext x
    funext y
    fin_cases x <;> fin_cases y <;> fin_cases h <;>
      norm_num [inducedPlan, canonicalPlan, controlledKernel, endpointMass,
        bestPair, controlValue, historyStiffness]
  rw [hplan]
  exact canonical_plan_is_target_coupling (by norm_num) (by norm_num)

theorem finite_transport_cost_same_across_histories :
    twoPointTransportCost (inducedPlan (0 : History) (bestPair 0).1 (bestPair 0).2) =
      1 / 3 ∧
    twoPointTransportCost (inducedPlan (1 : History) (bestPair 1).1 (bestPair 1).2) =
      1 / 3 := by
  constructor
  · exact every_target_coupling_has_cost (d := 1 / 3)
      (π := inducedPlan (0 : History) (bestPair 0).1 (bestPair 0).2)
      (best_pair_induces_target_coupling 0)
  · exact every_target_coupling_has_cost (d := 1 / 3)
      (π := inducedPlan (1 : History) (bestPair 1).1 (bestPair 1).2)
      (best_pair_induces_target_coupling 1)

theorem finite_action_history_gap_and_ot_equality :
    finiteMinimumAction (0 : History) = 1 / 18 ∧
    finiteMinimumAction (1 : History) = 1 / 2 ∧
    twoPointTransportCost (inducedPlan (0 : History) (bestPair 0).1 (bestPair 0).2) =
      twoPointTransportCost (inducedPlan (1 : History) (bestPair 1).1 (bestPair 1).2) := by
  constructor
  · exact finite_minimum_action_values.1
  constructor
  · exact finite_minimum_action_values.2
  · rw [finite_transport_cost_same_across_histories.1,
      finite_transport_cost_same_across_histories.2]

end FiniteMarkov
end Elastica

#print axioms Elastica.FiniteMarkov.historyKernel_is_probability_kernel
#print axioms Elastica.FiniteMarkov.same_readout_after_different_operations
#print axioms Elastica.FiniteMarkov.controlledKernel_is_probability_kernel
#print axioms Elastica.FiniteMarkov.best_pair_reaches_target
#print axioms Elastica.FiniteMarkov.every_target_pair_has_minimum_action
#print axioms Elastica.FiniteMarkov.finite_minimum_action_values
#print axioms Elastica.FiniteMarkov.finite_markov_action_matches_curvature_gramian
#print axioms Elastica.FiniteMarkov.finite_markov_action_is_half_existing_required_action
#print axioms Elastica.FiniteMarkov.canonical_plan_is_target_coupling
#print axioms Elastica.FiniteMarkov.every_target_coupling_has_cost
#print axioms Elastica.FiniteMarkov.best_pair_induces_target_coupling
#print axioms Elastica.FiniteMarkov.finite_transport_cost_same_across_histories
#print axioms Elastica.FiniteMarkov.finite_action_history_gap_and_ot_equality
