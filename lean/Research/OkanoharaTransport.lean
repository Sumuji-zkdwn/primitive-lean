import Elastica.ExponentialWeight
import Mathlib.Tactic

/-!
# A finite transport / history-cost bridge (isolated extension)

This is a restricted mathematical bridge between Okanohara's finite-time
transport and history-conditioned adaptation viewpoints (arXiv:2601.17607
and arXiv:2602.07950v3) and the existing Elastica energy/weight operations.

It DOES NOT formalize the full Wasserstein-2 metric, entropy production,
continuous probability-measure dynamics, fluid-fiber constitutive laws,
or computational complexity. A two-segment scalar action is a finite
analogue of the speed-limit inequality, not the general ESL theorem.

The additive history penalty is an explicit model choice. The already
defined Elastica.energy and Elastica.exponentialWeight are reused directly.
-/

namespace Elastica

/-- Signed endpoint displacement of two unit-duration transport segments. -/
def twoStepTransport (u v : ℝ) : ℝ := u + v

/-- Quadratic action of the two velocity segments. -/
def twoStepAction (u v : ℝ) : ℝ := u ^ 2 + v ^ 2

/-- Discrete finite-time speed limit: displacement squared is at most
duration (two units) times quadratic action. -/
theorem two_step_speed_limit (u v : ℝ) :
    (twoStepTransport u v) ^ 2 ≤ 2 * twoStepAction u v := by
  unfold twoStepTransport twoStepAction
  nlinarith [sq_nonneg (u - v)]

/-- The constant-speed trajectory attains the scalar lower bound. -/
theorem balanced_path_attains_bound (d : ℝ) :
    (twoStepTransport (d / 2) (d / 2)) ^ 2 =
      2 * twoStepAction (d / 2) (d / 2) := by
  unfold twoStepTransport twoStepAction
  ring

/-- Unit-horizon, unit-displacement adaptation cost at memory h.
This is the constant-control toy model's action, not a generic complexity bound. -/
def historyUnitCost (h : ℝ) : ℝ := (1 + h) ^ 2

/-- The input required to produce displacement d under gain 1/(1+h). -/
def requiredInput (h d : ℝ) : ℝ := (1 + h) * d

/-- The quadratic action of this required constant input. -/
def requiredAction (h d : ℝ) : ℝ := (requiredInput h d) ^ 2

/-- Exact history-sensitive input cost for the unit-time scalar model. -/
theorem required_action_exact (h d : ℝ) :
    requiredAction h d = historyUnitCost h * d ^ 2 := by
  unfold requiredAction requiredInput historyUnitCost
  ring

/-- Under nonnegative memory, larger memory cannot reduce unit cost. -/
theorem history_unit_cost_mono {h₀ h₁ : ℝ}
    (h₀_nonneg : 0 ≤ h₀) (hle : h₀ ≤ h₁) :
    historyUnitCost h₀ ≤ historyUnitCost h₁ := by
  have hs : 0 ≤ 2 + h₀ + h₁ := by linarith
  have hp : 0 ≤ (h₁ - h₀) * (2 + h₀ + h₁) :=
    mul_nonneg (sub_nonneg.mpr hle) hs
  unfold historyUnitCost
  nlinarith

/-- An extended state (observable position, unobserved memory). -/
abbrev HistoryState := ℝ × ℝ

def readPosition (s : HistoryState) : ℝ := s.1

def adaptationCost (s : HistoryState) : ℝ := historyUnitCost s.2

/-- Equal visible position need not imply equal adaptation cost. -/
theorem same_observation_different_cost :
    readPosition ((0 : ℝ), (0 : ℝ)) =
      readPosition ((0 : ℝ), (2 : ℝ)) ∧
    adaptationCost ((0 : ℝ), (0 : ℝ)) ≠
      adaptationCost ((0 : ℝ), (2 : ℝ)) := by
  constructor
  · rfl
  · norm_num [adaptationCost, historyUnitCost]

/-- Adaptation cost does not factor through present-position observation. -/
theorem adaptation_cost_not_observation_factor :
    ¬ ∃ f : ℝ → ℝ, ∀ s : HistoryState,
        adaptationCost s = f (readPosition s) := by
  rintro ⟨f, hf⟩
  have h₀ := hf ((0 : ℝ), (0 : ℝ))
  have h₂ := hf ((0 : ℝ), (2 : ℝ))
  norm_num [adaptationCost, historyUnitCost, readPosition] at h₀ h₂
  linarith

/-- Explicitly chosen augmentation of the existing curvature integral. -/
noncomputable def historyAugmentedEnergy (ε θ : ℝ → ℝ) (ℓ h : ℝ) : ℝ :=
  energy ε θ ℓ + historyUnitCost h

/-- The history penalty cannot lower the original Elastica energy. -/
theorem energy_le_history_augmented (ε θ : ℝ → ℝ) (ℓ h : ℝ) :
    energy ε θ ℓ ≤ historyAugmentedEnergy ε θ ℓ h := by
  unfold historyAugmentedEnergy historyUnitCost
  nlinarith [sq_nonneg (1 + h)]

/-- For the same actual curve, ordered nonnegative histories order costs. -/
theorem history_augmented_energy_mono (ε θ : ℝ → ℝ) (ℓ : ℝ)
    {h₀ h₁ : ℝ} (h₀_nonneg : 0 ≤ h₀) (hle : h₀ ≤ h₁) :
    historyAugmentedEnergy ε θ ℓ h₀ ≤
      historyAugmentedEnergy ε θ ℓ h₁ := by
  have hc := history_unit_cost_mono h₀_nonneg hle
  unfold historyAugmentedEnergy
  linarith

/-- Apply the existing whole-energy exponential representation to the
history-augmented energy, not to the curvature density. -/
noncomputable def historyAugmentedWeight (β : ℝ) (ε θ : ℝ → ℝ) (ℓ h : ℝ) : ℝ :=
  Real.exp (-β * historyAugmentedEnergy ε θ ℓ h)

/-- Existing Elastica exponential-weight order remains valid after adding
the explicit nonnegative history cost. This invokes a *previous* theorem. -/
theorem history_weight_le_original {β : ℝ} (hβ : 0 < β)
    (ε θ : ℝ → ℝ) (ℓ h : ℝ) :
    historyAugmentedWeight β ε θ ℓ h ≤
      exponentialWeight β ε θ ℓ := by
  change Real.exp (-β * historyAugmentedEnergy ε θ ℓ h) ≤
    Real.exp (-β * energy ε θ ℓ)
  exact (exp_neg_mul_le_exp_neg_mul_iff hβ).2
    (energy_le_history_augmented ε θ ℓ h)

/-!
## Explicit bistable fiber / finite ensemble extension

The threshold values ±1 and the high/low resistances 3/1 are constitutive
model choices, not physical constants. For each fiber, the update holds its
previous state between the thresholds. A chosen resistance law connects
that updated state to the control-gain example above.

The serial amplification theorem is conditional on *multiplicative* fiber
resistances, not a lower bound for every inverse-learning algorithm.
-/

/-- Binary fiber with remanence in the threshold interval (-1, 1). -/
def switchFiber (q : Bool) (drive : ℝ) : Bool :=
  if (1 : ℝ) ≤ drive then true
  else if drive ≤ (-1 : ℝ) then false
  else q

theorem switch_fiber_holds_at_zero (q : Bool) :
    switchFiber q 0 = q := by
  norm_num [switchFiber]

/-- The same final external drive can retain distinct switch histories. -/
theorem switch_fiber_remanence :
    switchFiber (switchFiber false 2) 0 = true ∧
      switchFiber (switchFiber false (-2)) 0 = false := by
  constructor <;> norm_num [switchFiber]

/-- At forcing +2, two different internal states merge. -/
theorem positive_pulse_is_not_injective :
    ¬ Function.Injective (fun q : Bool => switchFiber q 2) := by
  intro h
  have heq : (false : Bool) = true := h (by norm_num [switchFiber])
  cases heq

/-- Chosen memory variable: relaxed fiber = 0, activated fiber = 2. -/
def fiberMemory (q : Bool) : ℝ := if q then 2 else 0

/-- Resistance law consistent with Okanohara's toy gain 1/(1+h). -/
def fiberResistance (q : Bool) : ℝ := 1 + fiberMemory q

theorem fiber_resistance_positive (q : Bool) :
    0 < fiberResistance q := by
  cases q <;> norm_num [fiberResistance, fiberMemory]

/-- The physical input is converted into displacement through resistance. -/
def fiberDisplacement (q : Bool) (input : ℝ) : ℝ :=
  input / fiberResistance q

/-- Reuse the *existing* requiredInput from the history-control bridge. -/
theorem fiber_required_input_realizes_target (q : Bool) (d : ℝ) :
    fiberDisplacement q (requiredInput (fiberMemory q) d) = d := by
  cases q <;>
    norm_num [fiberDisplacement, requiredInput, fiberMemory, fiberResistance]

def fiberAction (q : Bool) (d : ℝ) : ℝ :=
  requiredAction (fiberMemory q) d

/-- The pulse history changes the unit-target energy from 1 to 9. -/
theorem pulse_action_gap :
    fiberAction (switchFiber (switchFiber false 2) 0) 1 = 9 ∧
    fiberAction (switchFiber (switchFiber false (-2)) 0) 1 = 1 := by
  constructor <;>
    norm_num [fiberAction, requiredAction, requiredInput,
      fiberMemory, switchFiber]

/-- The present visible position is independent of the recorded switch. -/
abbrev FiberState := ℝ × Bool

def fiberRead (s : FiberState) : ℝ := s.1
def fiberReadCost (s : FiberState) : ℝ := fiberAction s.2 1

/-- Different pulse histories from the same initial state, with readout zero. -/
def fiberPulse (drive : ℝ) : FiberState :=
  ((0 : ℝ), switchFiber (switchFiber false drive) 0)

theorem fiber_pulse_readout_and_cost :
    fiberRead (fiberPulse 2) = fiberRead (fiberPulse (-2)) ∧
    fiberReadCost (fiberPulse 2) = 9 ∧
    fiberReadCost (fiberPulse (-2)) = 1 := by
  norm_num [fiberRead, fiberReadCost, fiberPulse, fiberAction,
    switchFiber, fiberMemory, requiredAction, requiredInput]

/-- A cost determined from only the present position cannot fit both pulses. -/
theorem pulse_cost_does_not_factor_through_readout :
    ¬ ∃ f : ℝ → ℝ, ∀ drive : ℝ,
        fiberReadCost (fiberPulse drive) = f (fiberRead (fiberPulse drive)) := by
  rintro ⟨f, hf⟩
  have hp := hf 2
  have hn := hf (-2)
  norm_num [fiberRead, fiberReadCost, fiberPulse, fiberAction,
    switchFiber, fiberMemory, requiredAction, requiredInput] at hp hn
  linarith

/-- Pushforward of a signed mass function by the deterministic switch. -/
def fiberPushforward (drive : ℝ) (p : Bool → ℝ) (target : Bool) : ℝ :=
  (if switchFiber false drive = target then p false else 0) +
    (if switchFiber true drive = target then p true else 0)

/-- A positive pulse pushes all mass to the high-resistance fiber state. -/
theorem positive_pulse_collapses_mass (p : Bool → ℝ) :
    fiberPushforward 2 p false = 0 ∧
      fiberPushforward 2 p true = p false + p true := by
  constructor <;> simp [fiberPushforward, switchFiber]

def fiberDirac (q target : Bool) : ℝ := if q = target then 1 else 0

/-- Distinct initial point distributions become identical after the pulse. -/
theorem positive_pulse_erases_distinct_diracs :
    fiberDirac false ≠ fiberDirac true ∧
      (fun b => fiberPushforward 2 (fiberDirac false) b) =
        (fun b => fiberPushforward 2 (fiberDirac true) b) := by
  constructor
  · intro h
    have heq := congrFun h false
    norm_num [fiberDirac] at heq
  · funext b
    cases b <;>
      norm_num [fiberPushforward, fiberDirac, switchFiber]

/-- Independent fibers in series: resistances multiply, by modelling choice. -/
def serialResistance {n : ℕ} (q : Fin n → Bool) : ℝ :=
  ∏ i : Fin n, fiberResistance (q i)

def serialAction {n : ℕ} (q : Fin n → Bool) (d : ℝ) : ℝ :=
  (serialResistance q) ^ 2 * d ^ 2

theorem serial_all_on_resistance (n : ℕ) :
    serialResistance (fun _ : Fin n => true) = (3 : ℝ) ^ n := by
  simp [serialResistance, fiberResistance, fiberMemory]

theorem serial_all_off_resistance (n : ℕ) :
    serialResistance (fun _ : Fin n => false) = 1 := by
  simp [serialResistance, fiberResistance, fiberMemory]

/-- Exponential action is derived under the explicit series-resistance law. -/
theorem serial_all_on_action (n : ℕ) (d : ℝ) :
    serialAction (fun _ : Fin n => true) d = (9 : ℝ) ^ n * d ^ 2 := by
  rw [serialAction, serial_all_on_resistance]
  congr 1
  calc
    ((3 : ℝ) ^ n) ^ 2 = (3 : ℝ) ^ (n * 2) := by rw [pow_mul]
    _ = (3 : ℝ) ^ (2 * n) := by rw [Nat.mul_comm n 2]
    _ = ((3 : ℝ) ^ 2) ^ n := by rw [pow_mul]
    _ = (9 : ℝ) ^ n := by norm_num

theorem serial_all_off_action (n : ℕ) (d : ℝ) :
    serialAction (fun _ : Fin n => false) d = d ^ 2 := by
  simp [serialAction, serial_all_off_resistance]

/-!
## Energy-derived relay thresholds

The switching rule can be justified as a minimizer of a two-state
linear-forcing energy with a discrete dissipation penalty, rather
than only an operational if-then-else rule. This is a *discrete*
energy choice, not a derivation from the full smooth curvature integral.
-/

/-- The two-state reduction of a signed linear external work term -u*x. -/
def fiberExternalEnergy (q : Bool) (u : ℝ) : ℝ :=
  if q then -u else u

/-- One unit of switching distance costs two units of dissipated energy. -/
def fiberSwitchPenalty (old new : Bool) : ℝ :=
  if old = new then 0 else 2

def fiberStepEnergy (old new : Bool) (u : ℝ) : ℝ :=
  fiberExternalEnergy new u + fiberSwitchPenalty old new

/-- From the relaxed state, changing to the activated state becomes
weakly preferable exactly when u >= +1. -/
theorem fiber_up_threshold_iff (u : ℝ) :
    fiberStepEnergy false true u ≤ fiberStepEnergy false false u ↔
      (1 : ℝ) ≤ u := by
  change -u + 2 ≤ u ↔ (1 : ℝ) ≤ u
  constructor <;> intro h <;> linarith

/-- From the activated state, changing to the relaxed state becomes
weakly preferable exactly when u <= -1. -/
theorem fiber_down_threshold_iff (u : ℝ) :
    fiberStepEnergy true false u ≤ fiberStepEnergy true true u ↔
      u ≤ (-1 : ℝ) := by
  change u + 2 ≤ -u ↔ u ≤ (-1 : ℝ)
  constructor <;> intro h <;> linarith

/-- In the middle of the hysteresis loop, holding is strictly cheaper
than switching, for either internal fiber state. -/
theorem fiber_hold_is_strict_minimizer (q : Bool) (u : ℝ)
    (hl : (-1 : ℝ) < u) (hr : u < (1 : ℝ)) :
    fiberStepEnergy q q u < fiberStepEnergy q (!q) u := by
  cases q
  · change u < -u + 2
    linarith
  · change -u < u + 2
    linarith

/-- The actual relay update always weakly minimizes the discrete energy
including dissipation among the two possible next fiber states. -/
theorem switchFiber_minimizes_step_energy (q : Bool) (u : ℝ) :
    fiberStepEnergy q (switchFiber q u) u ≤
      fiberStepEnergy q (!(switchFiber q u)) u := by
  cases q
  · by_cases hhi : (1 : ℝ) ≤ u
    · have hs : switchFiber false u = true := by simp [switchFiber, hhi]
      rw [hs]
      exact (fiber_up_threshold_iff u).2 hhi
    · have hs : switchFiber false u = false := by simp [switchFiber, hhi]
      rw [hs]
      change u ≤ -u + 2
      linarith [lt_of_not_ge hhi]
  · by_cases hlo : u ≤ (-1 : ℝ)
    · have hhi : ¬ ((1 : ℝ) ≤ u) := by linarith
      have hs : switchFiber true u = false := by simp [switchFiber, hhi, hlo]
      rw [hs]
      exact (fiber_down_threshold_iff u).2 hlo
    · have hs : switchFiber true u = true := by
        by_cases hhi : (1 : ℝ) ≤ u
        · simp [switchFiber, hhi]
        · simp [switchFiber, hhi, hlo]
      rw [hs]
      change -u ≤ u + 2
      linarith [lt_of_not_ge hlo]

end Elastica

/-! Explicit kernel-axiom audit for the standalone extension. -/
#print axioms Elastica.two_step_speed_limit
#print axioms Elastica.balanced_path_attains_bound
#print axioms Elastica.required_action_exact
#print axioms Elastica.history_unit_cost_mono
#print axioms Elastica.same_observation_different_cost
#print axioms Elastica.adaptation_cost_not_observation_factor
#print axioms Elastica.energy_le_history_augmented
#print axioms Elastica.history_augmented_energy_mono
#print axioms Elastica.history_weight_le_original

#print axioms Elastica.switch_fiber_holds_at_zero
#print axioms Elastica.switch_fiber_remanence
#print axioms Elastica.positive_pulse_is_not_injective
#print axioms Elastica.fiber_resistance_positive
#print axioms Elastica.fiber_required_input_realizes_target
#print axioms Elastica.pulse_action_gap
#print axioms Elastica.fiber_pulse_readout_and_cost
#print axioms Elastica.pulse_cost_does_not_factor_through_readout
#print axioms Elastica.positive_pulse_collapses_mass
#print axioms Elastica.positive_pulse_erases_distinct_diracs
#print axioms Elastica.serial_all_on_resistance
#print axioms Elastica.serial_all_off_resistance
#print axioms Elastica.serial_all_on_action
#print axioms Elastica.serial_all_off_action
#print axioms Elastica.fiber_up_threshold_iff
#print axioms Elastica.fiber_down_threshold_iff
#print axioms Elastica.fiber_hold_is_strict_minimizer
#print axioms Elastica.switchFiber_minimizes_step_energy
