/-!
# Kerr finite-flow relative-energy bridge (new, additive)

This supplement isolates the skew cancellation in the relative-energy rate.
It reuses the retained scalar Kerr gap and the genuine finite matrix pairing.
The statements are finite-dimensional; no spatial limit, uniform time-step
stability, or general nonlinear PDE solution is asserted.
-/

namespace KerrKoopman.RelativeEnergyBridge

noncomputable section

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- Finite matrix action commutes with differences; no skewness is needed. -/
theorem applyQ_sub (Q : ι → ι → ℝ) (u v : ι → ℝ) (i : ι) :
    FiniteEnergy.applyQ Q (fun j => u j - v j) i =
      FiniteEnergy.applyQ Q u i - FiniteEnergy.applyQ Q v i := by
  simp only [FiniteEnergy.applyQ, mul_sub, Finset.sum_sub_distrib]

/-- The (unweighted) relative physical energy, with comparison state first
inside the old scalar `electricGap`.  A mesh factor h can be multiplied later. -/
def relativeEnergy (E H EB HB : ι → ℝ) : ℝ :=
  ∑ i, (RelativeEnergy.electricGap (EB i) (E i) + (H i - HB i) ^ 2 / 2)

/-- Spatially dimension-independent coercivity for physical E and H. -/
theorem relative_energy_controls (E H EB HB : ι → ℝ) :
    (∑ i, ((E i - EB i) ^ 2 + (H i - HB i) ^ 2) / 2) ≤
      relativeEnergy E H EB HB := by
  unfold relativeEnergy
  apply Finset.sum_le_sum
  intro i _
  have hs := RelativeEnergy.square_error_le_gap (EB i) (E i)
  linarith

/-- The material-law nonlinear remainder is controlled by the scalar gap,
without an N-dependent constant or a bound on the actual field E. -/
theorem constitutive_remainder_control (e b : ℝ) :
    |(e - b) - (Riccati.constitutive e - Riccati.constitutive b) / (1 + b ^ 2)| ≤
      3 * RelativeEnergy.electricGap b e :=
  RelativeEnergy.constitutive_remainder_le_three_gap b e

/-- The formal rate of relative energy along actual finite Maxwell rates
D'=-QH and H'=-QE, with arbitrary comparison displacement/magnetic rates. -/
def relativeRateLeft (Q : ι → ι → ℝ) (E H EB HB db dh : ι → ℝ) (i : ι) : ℝ :=
  (E i - EB i) * (-FiniteEnergy.applyQ Q H i) -
  ((Riccati.constitutive (E i) - Riccati.constitutive (EB i)) /
    (1 + (EB i) ^ 2)) * db i +
  (H i - HB i) * (-FiniteEnergy.applyQ Q E i - dh i)

/-- The same rate after transferring the spatial derivative onto the
comparison state. The last two terms are precisely its two residuals. -/
def relativeRateRight (Q : ι → ι → ℝ) (E H EB HB db dh : ι → ℝ) (i : ι) : ℝ :=
  ((E i - EB i) -
    (Riccati.constitutive (E i) - Riccati.constitutive (EB i)) /
      (1 + (EB i) ^ 2)) * db i -
  (E i - EB i) * (db i + FiniteEnergy.applyQ Q HB i) -
  (H i - HB i) * (dh i + FiniteEnergy.applyQ Q EB i)

/-- Pointwise rearrangement: two unbalanced spatial terms remain. -/
theorem relative_rate_term (Q : ι → ι → ℝ) (E H EB HB db dh : ι → ℝ) (i : ι) :
    relativeRateLeft Q E H EB HB db dh i =
      relativeRateRight Q E H EB HB db dh i -
        (E i - EB i) * FiniteEnergy.applyQ Q (fun j => H j - HB j) i -
        (H i - HB i) * FiniteEnergy.applyQ Q (fun j => E j - EB j) i := by
  unfold relativeRateLeft relativeRateRight
  rw [applyQ_sub Q H HB i, applyQ_sub Q E EB i]
  ring

/-- Discretization-independent cancellation at the finite level.
There is NO ||Q|| factor. This is an identity of algebraic rate expressions;
the chain rule for an actual time-varying relative energy is a separate step. -/
theorem relative_energy_rate_identity (Q : ι → ι → ℝ)
    (hQ : ∀ i j, Q i j = -Q j i)
    (E H EB HB db dh : ι → ℝ) :
    (∑ i, relativeRateLeft Q E H EB HB db dh i) =
      ∑ i, relativeRateRight Q E H EB HB db dh i := by
  have hskew := FiniteEnergy.skew_pairing Q hQ
    (fun i => E i - EB i) (fun i => H i - HB i)
  calc
    (∑ i, relativeRateLeft Q E H EB HB db dh i) =
        ∑ i, (relativeRateRight Q E H EB HB db dh i -
          (E i - EB i) * FiniteEnergy.applyQ Q (fun j => H j - HB j) i -
          (H i - HB i) * FiniteEnergy.applyQ Q (fun j => E j - EB j) i) := by
            apply Finset.sum_congr rfl
            intro i _
            exact relative_rate_term Q E H EB HB db dh i
    _ = (∑ i, relativeRateRight Q E H EB HB db dh i) -
        (∑ i, (E i - EB i) * FiniteEnergy.applyQ Q (fun j => H j - HB j) i) -
        (∑ i, (H i - HB i) * FiniteEnergy.applyQ Q (fun j => E j - EB j) i) := by
          simp only [Finset.sum_sub_distrib]
    _ = ∑ i, relativeRateRight Q E H EB HB db dh i := by
          rw [hskew]
          ring

/-- Connect the preceding finite identity to the already constructed
actual Kerr ODE flow, rather than postulating a separate solution. -/
theorem actual_flow_relative_rate_identity (Q : ι → ι → ℝ)
    (hQ : ∀ i j, Q i j = -Q j i) (t : ℝ) (z : FiniteFlow.State ι)
    (EB HB db dh : ι → ℝ) :
    (∑ i, relativeRateLeft Q
        (fun j => FiniteFlow.electric (FiniteFlow.flow Q t z) j)
        (fun j => (FiniteFlow.flow Q t z).snd j) EB HB db dh i) =
      ∑ i, relativeRateRight Q
        (fun j => FiniteFlow.electric (FiniteFlow.flow Q t z) j)
        (fun j => (FiniteFlow.flow Q t z).snd j) EB HB db dh i :=
  relative_energy_rate_identity Q hQ _ _ EB HB db dh

end

end KerrKoopman.RelativeEnergyBridge
