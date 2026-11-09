/-!
# Kerr finite-flow relative-energy derivative, conditional on reference rates

This module differentiates the *actual* finite Kerr relative energy, without
postulating a derivative of an abstract error function.  The comparison field
has explicit displacement and magnetic residual rates.  The pre-existing
ContinuumRelativeEnergy.finite_skew_rate_budget supplies the skew cancellation
and the operator-norm-free algebraic inequality.

No PDE existence, N-uniform spatial consistency, or Gronwall assertion is made.
The source files and proofs imported from KerrKoopman are unchanged.
-/

namespace KerrKoopman.ContinuumRelativeDynamics

noncomputable section

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- Physical relative energy: the comparison electric field is the base. -/
def relativeEnergy (e a b : ι → ℝ) : ℝ :=
  ∑ i, (RelativeEnergy.electricGap (e i) (a i) + (b i) ^ 2 / 2)

/-- Exact chain rule for the nonlinear scalar Kerr relative-energy gap. -/
theorem electricGap_hasDerivAt (e a : ℝ → ℝ) (e' a' t : ℝ)
    (he : HasDerivAt e e' t) (ha : HasDerivAt a a' t) :
    HasDerivAt (fun s => RelativeEnergy.electricGap (e s) (a s))
      ((a t - e t) * (1 + (a t) ^ 2) * a' -
       (Riccati.constitutive (a t) - Riccati.constitutive (e t)) * e') t := by
  have hz : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 t :=
    hasDerivAt_const t (0 : ℝ)
  have hWa := FiniteEnergy.density_hasDerivAt a (fun _ => (0 : ℝ)) a' 0 t ha hz
  have hWe := FiniteEnergy.density_hasDerivAt e (fun _ => (0 : ℝ)) e' 0 t he hz
  have hDa : HasDerivAt (fun s => Riccati.constitutive (a s))
      ((1 + (a t) ^ 2) * a') t := by
    simpa only [Riccati.constitutive] using
      (FiniteEnergy.constitutive_hasDerivAt a a' t ha)
  have hDe : HasDerivAt (fun s => Riccati.constitutive (e s))
      ((1 + (e t) ^ 2) * e') t := by
    simpa only [Riccati.constitutive] using
      (FiniteEnergy.constitutive_hasDerivAt e e' t he)
  have h := (hWa.sub hWe).sub (he.mul (hDa.sub hDe))
  convert h using 1
  dsimp [FiniteEnergy.density, Riccati.constitutive]
  ring

/-- Differentiating the sum of the exact electric gap and magnetic L2 gap. -/
theorem relativeEnergy_hasDerivAt (A H E V : ℝ → ι → ℝ)
    (ad hd ed vd : ι → ℝ) (t : ℝ)
    (hA : ∀ i, HasDerivAt (fun s => A s i) (ad i) t)
    (hH : ∀ i, HasDerivAt (fun s => H s i) (hd i) t)
    (hE : ∀ i, HasDerivAt (fun s => E s i) (ed i) t)
    (hV : ∀ i, HasDerivAt (fun s => V s i) (vd i) t) :
    HasDerivAt
      (fun s => relativeEnergy (E s) (A s) (fun i => H s i - V s i))
      (∑ i, ((A t i - E t i) * (1 + (A t i) ^ 2) * ad i -
        (Riccati.constitutive (A t i) - Riccati.constitutive (E t i)) * ed i +
        (H t i - V t i) * (hd i - vd i))) t := by
  unfold relativeEnergy
  apply HasDerivAt.fun_sum
  intro i _
  have hg := electricGap_hasDerivAt (fun s => E s i) (fun s => A s i)
    (ed i) (ad i) t (hE i) (hA i)
  have hb := ((hH i).sub (hV i)).pow 2
  have h := hg.add (hb.div_const 2)
  convert h using 1
  dsimp
  ring

/-- The finite matrix derivative respects subtraction by linearity. -/
theorem applyQ_sub (Q : ι → ι → ℝ) (a e : ι → ℝ) (i : ι) :
    FiniteEnergy.applyQ Q (fun j => a j - e j) i =
      FiniteEnergy.applyQ Q a i - FiniteEnergy.applyQ Q e i := by
  simp only [FiniteEnergy.applyQ, mul_sub, Finset.sum_sub_distrib]

/-- Time-derivative rate with explicit residuals in the reference Maxwell law. -/
def physicalRate (Q : ι → ι → ℝ) (a h e v rD rH : ι → ℝ) : ℝ :=
  ∑ i, ((a i - e i) *
      (-FiniteEnergy.applyQ Q (fun j => h j - v j) i -
        FiniteEnergy.applyQ Q v i) -
    ((Riccati.constitutive (a i) - Riccati.constitutive (e i)) /
      (1 + (e i) ^ 2)) * (-FiniteEnergy.applyQ Q v i + rD i) +
    (h i - v i) *
      (-FiniteEnergy.applyQ Q (fun j => a j - e j) i - rH i))

/-- A differentiated physical Kerr trajectory has the actual modulated rate.
    The reference E and V satisfy Maxwell equations up to rD and rH. -/
theorem physicalRelative_hasDerivAt (Q : ι → ι → ℝ)
    (A H E V : ℝ → ι → ℝ) (rD rH : ι → ℝ) (t : ℝ)
    (hA : ∀ i, HasDerivAt (fun s => A s i)
      (FiniteEnergy.electricRate Q (A t) (H t) i) t)
    (hH : ∀ i, HasDerivAt (fun s => H s i)
      (FiniteEnergy.magneticRate Q (A t) i) t)
    (hE : ∀ i, HasDerivAt (fun s => E s i)
      ((-FiniteEnergy.applyQ Q (V t) i + rD i) / (1 + (E t i) ^ 2)) t)
    (hV : ∀ i, HasDerivAt (fun s => V s i)
      (-FiniteEnergy.applyQ Q (E t) i + rH i) t) :
    HasDerivAt
      (fun s => relativeEnergy (E s) (A s) (fun i => H s i - V s i))
      (physicalRate Q (A t) (H t) (E t) (V t) rD rH) t := by
  have hd := relativeEnergy_hasDerivAt A H E V
    (fun i => FiniteEnergy.electricRate Q (A t) (H t) i)
    (fun i => FiniteEnergy.magneticRate Q (A t) i)
    (fun i => (-FiniteEnergy.applyQ Q (V t) i + rD i) / (1 + (E t i) ^ 2))
    (fun i => -FiniteEnergy.applyQ Q (E t) i + rH i)
    t hA hH hE hV
  convert hd using 1
  unfold physicalRate
  apply Finset.sum_congr rfl
  intro i _
  have ha0 : 1 + (A t i) ^ 2 ≠ 0 :=
    ne_of_gt (FiniteEnergy.constitutive_denominator_pos (A t i))
  have he0 : 1 + (E t i) ^ 2 ≠ 0 :=
    ne_of_gt (FiniteEnergy.constitutive_denominator_pos (E t i))
  rw [applyQ_sub Q (A t) (E t) i]
  rw [applyQ_sub Q (H t) (V t) i]
  dsimp [FiniteEnergy.electricRate, FiniteEnergy.magneticRate]
  field_simp [ha0, he0]
  ring

/-- The actual relative-energy derivative rate obeys the already proven
    matrix-norm-free bound; this uses only skewness and a reference rate cap. -/
theorem physicalRate_le (Q : ι → ι → ℝ)
    (hQ : ∀ i j, Q i j = -Q j i)
    (a h e v rD rH : ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hdt : ∀ i, |-FiniteEnergy.applyQ Q v i + rD i| ≤ M) :
    physicalRate Q a h e v rD rH ≤
      ∑ i, ((3 * M + 1) *
        (RelativeEnergy.electricGap (e i) (a i) +
         (h i - v i) ^ 2 / 2) +
        ((rD i) ^ 2 + (rH i) ^ 2) / 2) := by
  exact ContinuumRelativeEnergy.finite_skew_rate_budget Q hQ e a
    (fun i => h i - v i) v rD rH M hM hdt

end

end KerrKoopman.ContinuumRelativeDynamics
