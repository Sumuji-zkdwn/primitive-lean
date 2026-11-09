import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# Physical finite Kerr energy conservation

The index type is an arbitrary finite type. The differentiation matrix is
an actual real skew matrix, not a hypothesized energy-conserving vector
field. We define the physical E,H right-hand sides and prove that every
differentiable curve satisfying those equations conserves the physical
energy. Existence, completeness, Fourier-grid consistency and RKHA or
Sobolev-space constructions are not asserted by this module.
-/

open scoped BigOperators

namespace KerrKoopman.FiniteEnergy

noncomputable section

variable {ι : Type*} [Fintype ι]

def applyQ (Q : ι → ι → ℝ) (u : ι → ℝ) (i : ι) : ℝ :=
  ∑ j, Q i j * u j

def density (e h : ℝ) : ℝ := h ^ 2 / 2 + e ^ 2 / 2 + e ^ 4 / 4

def energy (E H : ι → ℝ) : ℝ := ∑ i, density (E i) (H i)

def electricRate (Q : ι → ι → ℝ) (E H : ι → ℝ) (i : ι) : ℝ :=
  -(applyQ Q H i) / (1 + (E i) ^ 2)

def magneticRate (Q : ι → ι → ℝ) (E : ι → ℝ) (i : ι) : ℝ :=
  -(applyQ Q E i)

def energyRate (Q : ι → ι → ℝ) (E H : ι → ℝ) : ℝ :=
  ∑ i, (H i * magneticRate Q E i +
    (E i + (E i) ^ 3) * electricRate Q E H i)

/-- The constitutive denominator cannot vanish for real physical states. -/
theorem constitutive_denominator_pos (e : ℝ) : 0 < 1 + e ^ 2 := by
  nlinarith [sq_nonneg e]

/-- Exact cancellation of the nonlinear electric energy derivative. -/
theorem electric_density_rate (e q : ℝ) :
    (e + e ^ 3) * (-q / (1 + e ^ 2)) = -e * q := by
  have hne : 1 + e ^ 2 ≠ 0 := ne_of_gt (constitutive_denominator_pos e)
  field_simp

/-- Skewness of the actual finite differentiation matrix exchanges the
two physical fields with a minus sign in their finite pairing. -/
theorem skew_pairing (Q : ι → ι → ℝ)
    (hQ : ∀ i j, Q i j = -Q j i) (u v : ι → ℝ) :
    (∑ i, u i * applyQ Q v i) = -(∑ i, v i * applyQ Q u i) := by
  unfold applyQ
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ j, ∑ i, u i * (Q i j * v j)) =
        ∑ j, ∑ i, -(v j * (Q j i * u i)) := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro i hi
      rw [hQ i j]
      ring
    _ = -(∑ j, ∑ i, v j * (Q j i * u i)) := by
      simp only [Finset.sum_neg_distrib]

/-- The physical finite-dimensional vector field has zero energy rate. -/
theorem energyRate_eq_zero (Q : ι → ι → ℝ)
    (hQ : ∀ i j, Q i j = -Q j i) (E H : ι → ℝ) :
    energyRate Q E H = 0 := by
  unfold energyRate electricRate magneticRate
  simp_rw [electric_density_rate]
  simp only [mul_neg, neg_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  have h := skew_pairing Q hQ E H
  linarith

/-- Chain rule for the actual quartic physical energy density. -/
theorem density_hasDerivAt (e h : ℝ → ℝ) (e' h' t : ℝ)
    (he : HasDerivAt e e' t) (hh : HasDerivAt h h' t) :
    HasDerivAt (fun z => density (e z) (h z))
      (h t * h' + (e t + (e t) ^ 3) * e') t := by
  convert (((hh.pow 2).div_const 2).add ((he.pow 2).div_const 2)).add
    ((he.pow 4).div_const 4) using 1
  dsimp [density]
  ring

/-- Any actual differentiable physical solution has zero energy derivative.
Only the physical component ODE and matrix skewness are hypotheses. -/
theorem energy_hasDerivAt_zero (Q : ι → ι → ℝ)
    (hQ : ∀ i j, Q i j = -Q j i) (E H : ℝ → ι → ℝ) (t : ℝ)
    (hE : ∀ i, HasDerivAt (fun z => E z i) (electricRate Q (E t) (H t) i) t)
    (hH : ∀ i, HasDerivAt (fun z => H z i) (magneticRate Q (E t) i) t) :
    HasDerivAt (fun z => energy (E z) (H z)) 0 t := by
  have h : HasDerivAt (fun z => energy (E z) (H z))
      (energyRate Q (E t) (H t)) t := by
    unfold energy energyRate
    exact HasDerivAt.fun_sum (fun i _ => density_hasDerivAt
      (fun z => E z i) (fun z => H z i) _ _ t (hE i) (hH i))
  simpa only [energyRate_eq_zero Q hQ] using h

/-- Conservation along a globally defined differentiable physical solution;
the existence of such a solution is not assumed as a hidden theorem. -/
theorem energy_conserved (Q : ι → ι → ℝ)
    (hQ : ∀ i j, Q i j = -Q j i) (E H : ℝ → ι → ℝ)
    (hE : ∀ t i, HasDerivAt (fun z => E z i) (electricRate Q (E t) (H t) i) t)
    (hH : ∀ t i, HasDerivAt (fun z => H z i) (magneticRate Q (E t) i) t)
    (t t₀ : ℝ) : energy (E t) (H t) = energy (E t₀) (H t₀) := by
  have hd : ∀ z, HasDerivAt (fun z => energy (E z) (H z)) 0 z :=
    fun z => energy_hasDerivAt_zero Q hQ E H z (hE z) (hH z)
  exact is_const_of_deriv_eq_zero (fun z => (hd z).differentiableAt)
    (fun z => (hd z).deriv) t t₀

/-- Local interval version: no global-in-time solution is required. -/
theorem energy_conserved_on_Icc (Q : ι → ι → ℝ)
    (hQ : ∀ i j, Q i j = -Q j i) (E H : ℝ → ι → ℝ)
    (a b : ℝ) (hab : a ≤ b)
    (hE : ∀ t ∈ Set.Icc a b, ∀ i,
      HasDerivAt (fun z => E z i) (electricRate Q (E t) (H t) i) t)
    (hH : ∀ t ∈ Set.Icc a b, ∀ i,
      HasDerivAt (fun z => H z i) (magneticRate Q (E t) i) t) :
    energy (E b) (H b) = energy (E a) (H a) := by
  have hd : ∀ t ∈ Set.Icc a b,
      HasDerivAt (fun z => energy (E z) (H z)) 0 t :=
    fun t ht => energy_hasDerivAt_zero Q hQ E H t (hE t ht) (hH t ht)
  have hc : ContinuousOn (fun z => energy (E z) (H z)) (Set.Icc a b) := by
    intro t ht
    exact (hd t ht).continuousAt.continuousWithinAt
  have hm : MonotoneOn (fun z => energy (E z) (H z)) (Set.Icc a b) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b) hc
    · intro t ht
      exact (hd t (interior_subset ht)).hasDerivWithinAt
    · intro t ht
      exact le_rfl
  have ha : AntitoneOn (fun z => energy (E z) (H z)) (Set.Icc a b) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b) hc
    · intro t ht
      exact (hd t (interior_subset ht)).hasDerivWithinAt
    · intro t ht
      exact le_rfl
  exact le_antisymm (ha ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab)
    (hm ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab)

/-- Derivative of D=E+E^3/3, before imposing the electric ODE. -/
theorem constitutive_hasDerivAt (e : ℝ → ℝ) (e' t : ℝ)
    (he : HasDerivAt e e' t) :
    HasDerivAt (fun z => e z + (e z) ^ 3 / 3)
      ((1 + (e t) ^ 2) * e') t := by
  convert he.add ((he.pow 3).div_const 3) using 1
  ring

/-- The physical E equation really gives Ddot=-QH under the Kerr law. -/
theorem displacement_hasDerivAt (Q : ι → ι → ℝ)
    (E H : ℝ → ι → ℝ) (t : ℝ) (i : ι)
    (hE : HasDerivAt (fun z => E z i) (electricRate Q (E t) (H t) i) t) :
    HasDerivAt (fun z => E z i + (E z i) ^ 3 / 3)
      (-applyQ Q (H t) i) t := by
  convert constitutive_hasDerivAt (fun z => E z i) _ t hE using 1
  unfold electricRate
  field_simp

/-- A real skew differentiation matrix that annihilates constants also
annihilates the sum of every differentiated field. -/
theorem sum_applyQ_eq_zero (Q : ι → ι → ℝ)
    (hQ : ∀ i j, Q i j = -Q j i) (hconst : ∀ i, ∑ j, Q i j = 0)
    (u : ι → ℝ) : (∑ i, applyQ Q u i) = 0 := by
  have hcol : ∀ j, (∑ i, Q i j) = 0 := by
    intro j
    calc
      (∑ i, Q i j) = ∑ i, -Q j i := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hQ i j
      _ = -(∑ i, Q j i) := by rw [Finset.sum_neg_distrib]
      _ = 0 := by rw [hconst j, neg_zero]
  unfold applyQ
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, hcol, zero_mul]
  exact Finset.sum_const_zero

/-- The magnetic sum (and hence the mean for a nonempty finite grid)
has zero derivative along the physical magnetic equation. -/
theorem magnetic_sum_hasDerivAt_zero (Q : ι → ι → ℝ)
    (hQ : ∀ i j, Q i j = -Q j i) (hconst : ∀ i, ∑ j, Q i j = 0)
    (E H : ℝ → ι → ℝ) (t : ℝ)
    (hH : ∀ i, HasDerivAt (fun z => H z i) (magneticRate Q (E t) i) t) :
    HasDerivAt (fun z => ∑ i, H z i) 0 t := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hH i)
  simpa only [magneticRate, Finset.sum_neg_distrib,
    sum_applyQ_eq_zero Q hQ hconst, neg_zero] using hd

/-- The displacement sum has zero derivative under the actual E equation
and Kerr constitutive law, not under an assumed D equation. -/
theorem displacement_sum_hasDerivAt_zero (Q : ι → ι → ℝ)
    (hQ : ∀ i j, Q i j = -Q j i) (hconst : ∀ i, ∑ j, Q i j = 0)
    (E H : ℝ → ι → ℝ) (t : ℝ)
    (hE : ∀ i, HasDerivAt (fun z => E z i) (electricRate Q (E t) (H t) i) t) :
    HasDerivAt (fun z => ∑ i, (E z i + (E z i) ^ 3 / 3)) 0 t := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => displacement_hasDerivAt Q E H t i (hE i))
  simpa only [Finset.sum_neg_distrib, sum_applyQ_eq_zero Q hQ hconst,
    neg_zero] using hd

end

end KerrKoopman.FiniteEnergy
