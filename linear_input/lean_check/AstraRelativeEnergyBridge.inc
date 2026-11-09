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


/-! ## Time-dependent Kerr relative energy: genuine finite-flow chain rule -/

/-- Differentiate the physical Kerr relative electric energy by applying the
existing energy and constitutive chain rules, rather than assuming a rate. -/
theorem electricGap_hasDerivAt (e b : ℝ → ℝ) (t de db : ℝ)
    (he : HasDerivAt e de t) (hb : HasDerivAt b db t) :
    HasDerivAt (fun s => RelativeEnergy.electricGap (b s) (e s))
      ((e t - b t) * (1 + (e t) ^ 2) * de -
        (Riccati.constitutive (e t) - Riccati.constitutive (b t)) * db) t := by
  have hz : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 t := hasDerivAt_const t 0
  have hWe : HasDerivAt (fun s => FiniteEnergy.density (e s) 0)
      ((e t + (e t) ^ 3) * de) t := by
    simpa using (FiniteEnergy.density_hasDerivAt e (fun _ : ℝ => 0) de 0 t he hz)
  have hWb : HasDerivAt (fun s => FiniteEnergy.density (b s) 0)
      ((b t + (b t) ^ 3) * db) t := by
    simpa using (FiniteEnergy.density_hasDerivAt b (fun _ : ℝ => 0) db 0 t hb hz)
  have hDe : HasDerivAt (fun s => Riccati.constitutive (e s))
      ((1 + (e t) ^ 2) * de) t := by
    simpa only [Riccati.constitutive] using
      (FiniteEnergy.constitutive_hasDerivAt e de t he)
  have hDb : HasDerivAt (fun s => Riccati.constitutive (b s))
      ((1 + (b t) ^ 2) * db) t := by
    simpa only [Riccati.constitutive] using
      (FiniteEnergy.constitutive_hasDerivAt b db t hb)
  have h := (hWe.sub hWb).sub (hb.mul (hDe.sub hDb))
  convert h using 1
  dsimp [RelativeEnergy.electricGap, Riccati.constitutive]
  ring

/-- Genuine physical Maxwell component rates, paired with a differentiable
comparison profile, satisfy the relative-energy chain rule. -/
theorem relativeEnergy_hasDerivAt_physical (Q : ι → ι → ℝ)
    (hQ : ∀ i j, Q i j = -Q j i)
    (E H EB HB : ℝ → ι → ℝ) (dEB dHB : ι → ℝ) (t : ℝ)
    (hE : ∀ i, HasDerivAt (fun s => E s i)
      (FiniteEnergy.electricRate Q (E t) (H t) i) t)
    (hH : ∀ i, HasDerivAt (fun s => H s i)
      (FiniteEnergy.magneticRate Q (E t) i) t)
    (hEB : ∀ i, HasDerivAt (fun s => EB s i) (dEB i) t)
    (hHB : ∀ i, HasDerivAt (fun s => HB s i) (dHB i) t) :
    HasDerivAt (fun s => relativeEnergy (E s) (H s) (EB s) (HB s))
      (∑ i, relativeRateRight Q (E t) (H t) (EB t) (HB t)
        (fun j => (1 + (EB t j) ^ 2) * dEB j) dHB i) t := by
  have hpoint (i : ι) : HasDerivAt
      (fun s => RelativeEnergy.electricGap (EB s i) (E s i) +
        (H s i - HB s i) ^ 2 / 2)
      (relativeRateLeft Q (E t) (H t) (EB t) (HB t)
        (fun j => (1 + (EB t j) ^ 2) * dEB j) dHB i) t := by
    have hg := electricGap_hasDerivAt (fun s => E s i) (fun s => EB s i)
      t (FiniteEnergy.electricRate Q (E t) (H t) i) (dEB i) (hE i) (hEB i)
    have hm : HasDerivAt (fun s => (H s i - HB s i) ^ 2 / 2)
        ((H t i - HB t i) *
          (FiniteEnergy.magneticRate Q (E t) i - dHB i)) t := by
      convert (((hH i).sub (hHB i)).pow 2).div_const 2 using 1
      simp only [Pi.sub_apply]
      ring
    have he0 : (1 + (E t i) ^ 2) ≠ 0 :=
      ne_of_gt (FiniteEnergy.constitutive_denominator_pos (E t i))
    have hb0 : (1 + (EB t i) ^ 2) ≠ 0 :=
      ne_of_gt (FiniteEnergy.constitutive_denominator_pos (EB t i))
    convert hg.add hm using 1
    dsimp only [relativeRateLeft, FiniteEnergy.electricRate,
      FiniteEnergy.magneticRate]
    field_simp [he0, hb0]
  have hsum : HasDerivAt
      (fun s => relativeEnergy (E s) (H s) (EB s) (HB s))
      (∑ i, relativeRateLeft Q (E t) (H t) (EB t) (HB t)
        (fun j => (1 + (EB t j) ^ 2) * dEB j) dHB i) t := by
    unfold relativeEnergy
    exact HasDerivAt.fun_sum (fun i _ => hpoint i)
  rw [relative_energy_rate_identity Q hQ (E t) (H t) (EB t) (HB t)
    (fun j => (1 + (EB t j) ^ 2) * dEB j) dHB] at hsum
  exact hsum

/-- The constructed finite Kerr ODE flow satisfies the exact
relative-energy time-derivative identity against any C1 comparison field.
The comparison displacement rate is (1+barE²)*barE'. -/
theorem relativeEnergy_hasDerivAt_flow (Q : ι → ι → ℝ)
    (hQ : ∀ i j, Q i j = -Q j i) (z : FiniteFlow.State ι)
    (EB HB : ℝ → ι → ℝ) (dEB dHB : ι → ℝ) (t : ℝ)
    (hEB : ∀ i, HasDerivAt (fun s => EB s i) (dEB i) t)
    (hHB : ∀ i, HasDerivAt (fun s => HB s i) (dHB i) t) :
    HasDerivAt
      (fun s => relativeEnergy
        (fun i => FiniteFlow.electric (FiniteFlow.flow Q s z) i)
        (fun i => (FiniteFlow.flow Q s z).snd i) (EB s) (HB s))
      (∑ i, relativeRateRight Q
        (fun j => FiniteFlow.electric (FiniteFlow.flow Q t z) j)
        (fun j => (FiniteFlow.flow Q t z).snd j) (EB t) (HB t)
        (fun j => (1 + (EB t j) ^ 2) * dEB j) dHB i) t := by
  exact relativeEnergy_hasDerivAt_physical Q hQ
    (fun s i => FiniteFlow.electric (FiniteFlow.flow Q s z) i)
    (fun s i => (FiniteFlow.flow Q s z).snd i) EB HB dEB dHB t
    (fun i => FiniteFlow.hasDerivAt_electric Q t z i)
    (fun i => FiniteFlow.hasDerivAt_magnetic Q t z i)
    hEB hHB



/-! ## Mesh-independent residual growth bounds -/

/-- Exact Kerr remainder and a pointwise bound on the comparison displacement
rate control the formal relative-energy production. No \`‖Q‖\` assumption. -/
theorem relativeRateRight_le (Q : ι → ι → ℝ)
    (E H EB HB db dh : ι → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hdb : ∀ i, |db i| ≤ A) :
    (∑ i, relativeRateRight Q E H EB HB db dh i) ≤
      3 * A * relativeEnergy E H EB HB +
        ∑ i, (|E i - EB i| * |db i + FiniteEnergy.applyQ Q HB i| +
          |H i - HB i| * |dh i + FiniteEnergy.applyQ Q EB i|) := by
  have hgR : (∑ i, RelativeEnergy.electricGap (EB i) (E i)) ≤
      relativeEnergy E H EB HB := by
    unfold relativeEnergy
    apply Finset.sum_le_sum
    intro i _
    have hs : 0 ≤ (H i - HB i) ^ 2 / 2 := by positivity
    linarith
  have hterm (i : ι) :
      relativeRateRight Q E H EB HB db dh i ≤
        3 * A * RelativeEnergy.electricGap (EB i) (E i) +
          (|E i - EB i| * |db i + FiniteEnergy.applyQ Q HB i| +
            |H i - HB i| * |dh i + FiniteEnergy.applyQ Q EB i|) := by
    have hg : 0 ≤ RelativeEnergy.electricGap (EB i) (E i) :=
      RelativeEnergy.electricGap_nonneg _ _
    have hr := constitutive_remainder_control (E i) (EB i)
    have hmain :
        ((E i - EB i) -
          (Riccati.constitutive (E i) - Riccati.constitutive (EB i)) /
            (1 + (EB i) ^ 2)) * db i ≤
        3 * A * RelativeEnergy.electricGap (EB i) (E i) := by
      calc
        _ ≤ |((E i - EB i) -
          (Riccati.constitutive (E i) - Riccati.constitutive (EB i)) /
            (1 + (EB i) ^ 2)) * db i| := le_abs_self _
        _ = |(E i - EB i) -
          (Riccati.constitutive (E i) - Riccati.constitutive (EB i)) /
            (1 + (EB i) ^ 2)| * |db i| := abs_mul _ _
        _ ≤ (3 * RelativeEnergy.electricGap (EB i) (E i)) * |db i| :=
          mul_le_mul_of_nonneg_right hr (abs_nonneg _)
        _ ≤ (3 * RelativeEnergy.electricGap (EB i) (E i)) * A :=
          mul_le_mul_of_nonneg_left (hdb i) (by positivity)
        _ = 3 * A * RelativeEnergy.electricGap (EB i) (E i) := by ring
    have he : -(E i - EB i) * (db i + FiniteEnergy.applyQ Q HB i) ≤
        |E i - EB i| * |db i + FiniteEnergy.applyQ Q HB i| := by
      calc
        _ ≤ |-(E i - EB i) * (db i + FiniteEnergy.applyQ Q HB i)| := le_abs_self _
        _ = _ := by rw [abs_mul, abs_neg]
    have hh : -(H i - HB i) * (dh i + FiniteEnergy.applyQ Q EB i) ≤
        |H i - HB i| * |dh i + FiniteEnergy.applyQ Q EB i| := by
      calc
        _ ≤ |-(H i - HB i) * (dh i + FiniteEnergy.applyQ Q EB i)| := le_abs_self _
        _ = _ := by rw [abs_mul, abs_neg]
    dsimp only [relativeRateRight]
    linarith
  calc
    (∑ i, relativeRateRight Q E H EB HB db dh i) ≤
        ∑ i, (3 * A * RelativeEnergy.electricGap (EB i) (E i) +
          (|E i - EB i| * |db i + FiniteEnergy.applyQ Q HB i| +
            |H i - HB i| * |dh i + FiniteEnergy.applyQ Q EB i|)) := by
              apply Finset.sum_le_sum
              intro i _
              exact hterm i
    _ = 3 * A * (∑ i, RelativeEnergy.electricGap (EB i) (E i)) +
          ∑ i, (|E i - EB i| * |db i + FiniteEnergy.applyQ Q HB i| +
            |H i - HB i| * |dh i + FiniteEnergy.applyQ Q EB i|) := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ 3 * A * relativeEnergy E H EB HB +
          ∑ i, (|E i - EB i| * |db i + FiniteEnergy.applyQ Q HB i| +
            |H i - HB i| * |dh i + FiniteEnergy.applyQ Q EB i|) := by
              exact add_le_add_right
                (mul_le_mul_of_nonneg_left hgR (by positivity)) _



/-- Strong dimension-independent residual estimate. The elementary inequality
\`|a|*|r| ≤ (a^2+r^2)/2\` absorbs the physical field errors into the Kerr gap.
Only the prescribed comparison rate A enters; no matrix operator norm. -/
theorem relativeRateRight_quadratic_le (Q : ι → ι → ℝ)
    (E H EB HB db dh : ι → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hdb : ∀ i, |db i| ≤ A) :
    (∑ i, relativeRateRight Q E H EB HB db dh i) ≤
      (3 * A + 1) * relativeEnergy E H EB HB +
        ∑ i, ((db i + FiniteEnergy.applyQ Q HB i) ^ 2 +
          (dh i + FiniteEnergy.applyQ Q EB i) ^ 2) / 2 := by
  have hcross :
      (∑ i, (|E i - EB i| * |db i + FiniteEnergy.applyQ Q HB i| +
        |H i - HB i| * |dh i + FiniteEnergy.applyQ Q EB i|)) ≤
      ∑ i, (((E i - EB i) ^ 2 + (H i - HB i) ^ 2) / 2 +
        ((db i + FiniteEnergy.applyQ Q HB i) ^ 2 +
          (dh i + FiniteEnergy.applyQ Q EB i) ^ 2) / 2) := by
    apply Finset.sum_le_sum
    intro i _
    have he : |E i - EB i| * |db i + FiniteEnergy.applyQ Q HB i| ≤
        ((E i - EB i) ^ 2 +
          (db i + FiniteEnergy.applyQ Q HB i) ^ 2) / 2 := by
      nlinarith [sq_nonneg (|E i - EB i| -
        |db i + FiniteEnergy.applyQ Q HB i|),
        sq_abs (E i - EB i),
        sq_abs (db i + FiniteEnergy.applyQ Q HB i)]
    have hh : |H i - HB i| * |dh i + FiniteEnergy.applyQ Q EB i| ≤
        ((H i - HB i) ^ 2 +
          (dh i + FiniteEnergy.applyQ Q EB i) ^ 2) / 2 := by
      nlinarith [sq_nonneg (|H i - HB i| -
        |dh i + FiniteEnergy.applyQ Q EB i|),
        sq_abs (H i - HB i),
        sq_abs (dh i + FiniteEnergy.applyQ Q EB i)]
    linarith
  have hphysical := relative_energy_controls E H EB HB
  calc
    (∑ i, relativeRateRight Q E H EB HB db dh i) ≤
        3 * A * relativeEnergy E H EB HB +
        ∑ i, (|E i - EB i| * |db i + FiniteEnergy.applyQ Q HB i| +
          |H i - HB i| * |dh i + FiniteEnergy.applyQ Q EB i|) :=
          relativeRateRight_le Q E H EB HB db dh A hA hdb
    _ ≤ 3 * A * relativeEnergy E H EB HB +
        ∑ i, (((E i - EB i) ^ 2 + (H i - HB i) ^ 2) / 2 +
          ((db i + FiniteEnergy.applyQ Q HB i) ^ 2 +
            (dh i + FiniteEnergy.applyQ Q EB i) ^ 2) / 2) :=
          add_le_add_left hcross _
    _ = 3 * A * relativeEnergy E H EB HB +
        (∑ i, ((E i - EB i) ^ 2 + (H i - HB i) ^ 2) / 2) +
        ∑ i, ((db i + FiniteEnergy.applyQ Q HB i) ^ 2 +
          (dh i + FiniteEnergy.applyQ Q EB i) ^ 2) / 2 := by
          rw [Finset.sum_add_distrib]
          ring
    _ ≤ (3 * A + 1) * relativeEnergy E H EB HB +
        ∑ i, ((db i + FiniteEnergy.applyQ Q HB i) ^ 2 +
          (dh i + FiniteEnergy.applyQ Q EB i) ^ 2) / 2 := by
          nlinarith

/-- Bound on the actual derivative of the genuine finite Kerr flow's relative
energy against a differentiable comparison field. In particular, its growth
coefficient is independent of the matrix norm or the number of grid cells. -/
theorem relativeEnergy_deriv_le_flow (Q : ι → ι → ℝ)
    (hQ : ∀ i j, Q i j = -Q j i) (z : FiniteFlow.State ι)
    (EB HB : ℝ → ι → ℝ) (dEB dHB : ι → ℝ) (t A : ℝ)
    (hA : 0 ≤ A)
    (hdb : ∀ i, |(1 + (EB t i) ^ 2) * dEB i| ≤ A)
    (hEB : ∀ i, HasDerivAt (fun s => EB s i) (dEB i) t)
    (hHB : ∀ i, HasDerivAt (fun s => HB s i) (dHB i) t) :
    deriv (fun s => relativeEnergy
      (fun i => FiniteFlow.electric (FiniteFlow.flow Q s z) i)
      (fun i => (FiniteFlow.flow Q s z).snd i) (EB s) (HB s)) t ≤
      (3 * A + 1) * relativeEnergy
        (fun i => FiniteFlow.electric (FiniteFlow.flow Q t z) i)
        (fun i => (FiniteFlow.flow Q t z).snd i) (EB t) (HB t) +
      ∑ i, (((1 + (EB t i) ^ 2) * dEB i +
          FiniteEnergy.applyQ Q (HB t) i) ^ 2 +
        (dHB i + FiniteEnergy.applyQ Q (EB t) i) ^ 2) / 2 := by
  have hd := relativeEnergy_hasDerivAt_flow Q hQ z EB HB dEB dHB t hEB hHB
  rw [hd.deriv]
  exact relativeRateRight_quadratic_le Q
    (fun i => FiniteFlow.electric (FiniteFlow.flow Q t z) i)
    (fun i => (FiniteFlow.flow Q t z).snd i)
    (EB t) (HB t) (fun i => (1 + (EB t i) ^ 2) * dEB i) dHB A hA hdb


end

end KerrKoopman.RelativeEnergyBridge
