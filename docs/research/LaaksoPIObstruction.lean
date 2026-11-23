import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Abstract obstruction to any uniform weak Poincare constant

The specific Laakso ball tests in the A-track notebook are intended to
supply the two explicit bounds below: oscillation >= c > 0 and scaled
upper-gradient energy <= K * (1/2)^n for fixed enlargement lambda.
This module proves that no nonnegative PI constant C can satisfy both
bounds for every n. It does not formalize the quotient's ball measures
or certify that the model-specific bounds hold.
-/

namespace LaaksoPIObstruction

open Filter
open scoped Topology

theorem no_uniform_PI_from_geometric_decay
    (osc cost : ℕ → ℝ) (c K : ℝ)
    (hc : 0 < c)
    (hosc : ∀ n : ℕ, c ≤ osc n)
    (hcost : ∀ n : ℕ, cost n ≤ K * (1 / 2 : ℝ) ^ n) :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, osc n ≤ C * cost n := by
  rintro ⟨C, hC, hPI⟩
  have hpow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n)
      atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hlim : Tendsto (fun n : ℕ => (C * K) * (1 / 2 : ℝ) ^ n)
      atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hpow : Tendsto
      (fun n : ℕ => (C * K) * (1 / 2 : ℝ) ^ n)
      atTop (nhds ((C * K) * 0)))
  have hsmall : ∀ᶠ n : ℕ in atTop,
      (C * K) * (1 / 2 : ℝ) ^ n < c :=
    hlim.eventually (Iio_mem_nhds hc)
  rcases hsmall.exists with ⟨n, hn⟩
  have hbound : c ≤ (C * K) * (1 / 2 : ℝ) ^ n := by
    calc
      c ≤ osc n := hosc n
      _ ≤ C * cost n := hPI n
      _ ≤ C * (K * (1 / 2 : ℝ) ^ n) :=
        mul_le_mul_of_nonneg_left (hcost n) hC
      _ = (C * K) * (1 / 2 : ℝ) ^ n := by ring
  exact (not_lt_of_ge hbound) hn

#print axioms no_uniform_PI_from_geometric_decay

end LaaksoPIObstruction
