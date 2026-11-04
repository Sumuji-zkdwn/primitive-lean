/-! Explicit finite operations for prayer, doubt, belief update and disappointment. -/

noncomputable section
open Real Finset

namespace LinearInputFourBayes

open LinearInputBayes

def mixture {α : Type*} (ε : ℝ) (q μ : α → ℝ) (x : α) : ℝ :=
  (1 - ε) * q x + ε * μ x

theorem mixture_distribution {α : Type*} [Fintype α] {q μ : α → ℝ}
    (hq : IsDistribution q) (hμ : IsDistribution μ) {ε : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) : IsDistribution (mixture ε q μ) := by
  constructor
  · intro x
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr hε1) (hq.1 x)) (mul_nonneg hε (hμ.1 x))
  · unfold mass mixture
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    change (1 - ε) * mass q + ε * mass μ = 1
    rw [hq.2, hμ.2]
    ring

theorem exploration_floor {α : Type*} {q μ : α → ℝ} (hq : ∀ x, 0 ≤ q x)
    {ε : ℝ} (hε1 : ε ≤ 1) (x : α) : ε * μ x ≤ mixture ε q μ x := by
  have := mul_nonneg (sub_nonneg.mpr hε1) (hq x)
  unfold mixture
  linarith

theorem exploration_can_restore_support {α : Type*} {q μ : α → ℝ}
    (hq : ∀ x, 0 ≤ q x) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {x : α}
    (hμ : 0 < μ x) : 0 < mixture ε q μ x :=
  lt_of_lt_of_le (mul_pos hε hμ) (exploration_floor hq hε1 x)

def disappointment (p y : ℝ) : ℝ := max (p - y) 0

theorem calibrated_binary_disappointment {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    p * disappointment p 1 + (1 - p) * disappointment p 0 = p * (1 - p) := by
  rw [disappointment, max_eq_right (sub_nonpos.mpr hp1)]
  simp only [disappointment, sub_zero, max_eq_left hp, mul_zero, zero_add]
  ring

theorem calibrated_disappointment_positive {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    0 < p * disappointment p 1 + (1 - p) * disappointment p 0 := by
  rw [calibrated_binary_disappointment hp.le hp1.le]
  exact mul_pos hp (sub_pos.mpr hp1)

def binaryPrior (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

def binaryScore (b : Bool) : ℝ := if b then 1 else 0

theorem binaryPrior_distribution {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    IsDistribution (binaryPrior p) := by
  constructor
  · intro b; cases b <;> simp [binaryPrior, hp, sub_nonneg.mpr hp1]
  · simp [mass, binaryPrior]

def binaryPartition (p β : ℝ) : ℝ := 1 - p + p * exp β

def binaryTilt (p β : ℝ) : ℝ := p * exp β / binaryPartition p β

theorem binary_tilt_formula (p β : ℝ) :
    tilt (binaryPrior p) β binaryScore true = binaryTilt p β := by
  simp [tilt, posterior, LinearInputBayes.normalize, mass, binaryPrior, binaryScore, binaryTilt, binaryPartition, add_comm]

theorem binary_partition_positive {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (β : ℝ) :
    0 < binaryPartition p β := add_pos (sub_pos.mpr hp1) (mul_pos hp (exp_pos β))

theorem binary_tilt_odds {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (β : ℝ) :
    binaryTilt p β / (1 - binaryTilt p β) = (p / (1 - p)) * exp β := by
  have hz := (binary_partition_positive hp hp1 β).ne'
  have hq : 1 - p ≠ 0 := (sub_pos.mpr hp1).ne'
  have hd : binaryPartition p β - p * exp β ≠ 0 := by
    simpa [binaryPartition] using hq
  unfold binaryTilt
  field_simp
  unfold binaryPartition
  ring

def binaryFreeEnergy (p β : ℝ) : ℝ := log (binaryPartition p β)

theorem hasDerivAt_binaryPartition (p β : ℝ) :
    HasDerivAt (binaryPartition p) (p * exp β) β := by
  simpa [binaryPartition] using
    (hasDerivAt_const β (1 - p)).add ((Real.hasDerivAt_exp β).const_mul p)

theorem hasDerivAt_binaryFreeEnergy {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (β : ℝ) :
    HasDerivAt (binaryFreeEnergy p) (binaryTilt p β) β := by
  simpa [binaryFreeEnergy, binaryTilt] using
    (hasDerivAt_binaryPartition p β).log (binary_partition_positive hp hp1 β).ne'

theorem binary_tilt_between {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (β : ℝ) :
    0 < binaryTilt p β ∧ binaryTilt p β < 1 := by
  have hz := binary_partition_positive hp hp1 β
  constructor
  · exact div_pos (mul_pos hp (exp_pos β)) hz
  · apply (div_lt_one hz).mpr
    unfold binaryPartition
    linarith

theorem hasDerivAt_binaryTilt {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (β : ℝ) :
    HasDerivAt (binaryTilt p) (binaryTilt p β * (1 - binaryTilt p β)) β := by
  have hz := (binary_partition_positive hp hp1 β).ne'
  have h := ((Real.hasDerivAt_exp β).const_mul p).div (hasDerivAt_binaryPartition p β) hz
  convert h using 1
  unfold binaryTilt
  field_simp

theorem binary_free_energy_derivative {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (β : ℝ) :
    deriv (binaryFreeEnergy p) β = binaryTilt p β :=
  (hasDerivAt_binaryFreeEnergy hp hp1 β).deriv

theorem binary_free_energy_second_derivative {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (β : ℝ) :
    HasDerivAt (deriv (binaryFreeEnergy p)) (binaryTilt p β * (1 - binaryTilt p β)) β := by
  have h : deriv (binaryFreeEnergy p) = binaryTilt p := funext (binary_free_energy_derivative hp hp1)
  rw [h]
  exact hasDerivAt_binaryTilt hp hp1 β

theorem binary_free_energy_second_positive {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (β : ℝ) :
    0 < deriv (deriv (binaryFreeEnergy p)) β := by
  rw [(binary_free_energy_second_derivative hp hp1 β).deriv]
  exact mul_pos (binary_tilt_between hp hp1 β).1 (sub_pos.mpr (binary_tilt_between hp hp1 β).2)

def thresholdForget {α : Type*} [Fintype α] (τ : ℝ) (w : α → ℝ) : α → ℝ :=
  LinearInputBayes.normalize (fun x => if τ ≤ w x then w x else 0)

theorem forgotten_stays_zero {α : Type*} [Fintype α] (τ : ℝ) (w L : α → ℝ)
    {x : α} (h : w x < τ) : posterior (thresholdForget τ w) L x = 0 := by
  apply posterior_zero_prior
  simp [thresholdForget, LinearInputBayes.normalize, not_le.mpr h]

theorem prayer_doubt_cancel {α : Type*} [Fintype α] {w : α → ℝ}
    (hw : IsDistribution w) (β : ℝ) (r : α → ℝ) :
    tilt (tilt w β r) (-β) r = w ∧ tilt (tilt w (-β) r) β r = w := by
  exact ⟨tilt_cancel hw β r, by simpa using tilt_cancel hw (-β) r⟩

/-- The source's exact two-state example: intermediate deletion creates order dependence. -/
theorem deletion_order_counterexample :
    tilt (thresholdForget (1 / 3) (tilt (binaryPrior (1 / 2)) (log 3) binaryScore))
        (-log 3) binaryScore = binaryPrior 1 ∧
    tilt (thresholdForget (1 / 3) (tilt (binaryPrior (1 / 2)) (-log 3) binaryScore))
        (log 3) binaryScore = binaryPrior 0 := by
  constructor <;> funext b <;> cases b <;>
    norm_num [tilt, posterior, LinearInputBayes.normalize, mass, thresholdForget, binaryPrior, binaryScore,
      exp_neg, exp_log (by norm_num : (0 : ℝ) < 3)]

def aliasPriorLeft (x : Fin 3) : ℝ := if x.val = 1 then 0 else 1 / 2

def aliasPriorRight (x : Fin 3) : ℝ := if x.val = 0 then 0 else 1 / 2

def aliasLikelihood (x : Fin 3) : ℝ := if x.val = 1 then 3 else 1

theorem alias_priors_are_distributions :
    IsDistribution aliasPriorLeft ∧ IsDistribution aliasPriorRight := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  constructor <;> constructor
  · intro x; unfold aliasPriorLeft; split_ifs <;> norm_num
  · norm_num [mass, aliasPriorLeft, Fin.sum_univ_three]
  · intro x; unfold aliasPriorRight; split_ifs <;> norm_num
  · norm_num [mass, aliasPriorRight, Fin.sum_univ_three, h20]

/-- Equal coarse priors can have different future coarse posteriors if likelihood sees a lost distinction. -/
theorem forgetting_can_lose_predictive_information :
    pushWeight LinearInputF0.exampleK aliasPriorLeft = pushWeight LinearInputF0.exampleK aliasPriorRight ∧
    pushWeight LinearInputF0.exampleK (posterior aliasPriorLeft aliasLikelihood) 0 = 1 / 2 ∧
    pushWeight LinearInputF0.exampleK (posterior aliasPriorRight aliasLikelihood) 0 = 3 / 4 := by
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  refine ⟨?_, ?_, ?_⟩
  · funext b
    fin_cases b <;> norm_num [pushWeight, aliasPriorLeft, aliasPriorRight,
      LinearInputF0.exampleK, Fin.sum_univ_three, h01, h02, h10, h12, h20, h21]
  · norm_num [pushWeight, posterior, LinearInputBayes.normalize, mass, aliasPriorLeft, aliasLikelihood,
      LinearInputF0.exampleK, Fin.sum_univ_three, h02, h12, h20]
  · norm_num [pushWeight, posterior, LinearInputBayes.normalize, mass, aliasPriorRight, aliasLikelihood,
      LinearInputF0.exampleK, Fin.sum_univ_three, h02, h12, h20]

end LinearInputFourBayes
