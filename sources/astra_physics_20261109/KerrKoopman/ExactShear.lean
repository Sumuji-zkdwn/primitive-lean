import KerrKoopman.PrimitiveConstitutive
import KerrKoopman.ExplicitMaterial

/-!
# Two exact subflows in physical displacement and magnetic coordinates

For every finite real matrix Q, the two parts of Ddot=-QH,
Hdot=-Q E(D) are explicit shears. Their formulas and derivatives are exact
for each subproblem. Their finite composition is only a splitting step,
not an asserted exact solution of the coupled nonlinear evolution.
-/

namespace KerrKoopman.ExactShear

noncomputable section

open FiniteEnergy PrimitiveConstitutive

abbrev State (ι : Type*) := (ι → ℝ) × (ι → ℝ)

variable {ι : Type*} [Fintype ι]

def fieldE (D : ι → ℝ) : ι → ℝ := fun i => materialInverse (D i)

def shearA (Q : ι → ι → ℝ) (t : ℝ) (z : State ι) : State ι :=
  (fun i => z.1 i - t * applyQ Q z.2 i, z.2)

def shearB (Q : ι → ι → ℝ) (t : ℝ) (z : State ι) : State ι :=
  (z.1, fun i => z.2 i - t * applyQ Q (fieldE z.1) i)

def lieStep (Q : ι → ι → ℝ) (t : ℝ) (z : State ι) : State ι :=
  shearB Q t (shearA Q t z)

theorem shearA_zero (Q : ι → ι → ℝ) (z : State ι) : shearA Q 0 z = z := by
  apply Prod.ext <;> funext i <;> simp [shearA]

theorem shearB_zero (Q : ι → ι → ℝ) (z : State ι) : shearB Q 0 z = z := by
  apply Prod.ext <;> funext i <;> simp [shearB]

theorem shearA_add (Q : ι → ι → ℝ) (s t : ℝ) (z : State ι) :
    shearA Q s (shearA Q t z) = shearA Q (s + t) z := by
  apply Prod.ext <;> funext i
  · dsimp [shearA]; ring
  · rfl

theorem shearB_add (Q : ι → ι → ℝ) (s t : ℝ) (z : State ι) :
    shearB Q s (shearB Q t z) = shearB Q (s + t) z := by
  apply Prod.ext <;> funext i
  · rfl
  · dsimp [shearB]; ring

theorem shearA_inverse (Q : ι → ι → ℝ) (t : ℝ) (z : State ι) :
    shearA Q (-t) (shearA Q t z) = z := by
  rw [shearA_add, neg_add_cancel, shearA_zero]

theorem shearB_inverse (Q : ι → ι → ℝ) (t : ℝ) (z : State ι) :
    shearB Q (-t) (shearB Q t z) = z := by
  rw [shearB_add, neg_add_cancel, shearB_zero]

theorem shearA_displacement_derivative (Q : ι → ι → ℝ) (z : State ι)
    (t : ℝ) (i : ι) :
    HasDerivAt (fun s => (shearA Q s z).1 i) (-applyQ Q z.2 i) t := by
  simpa [shearA] using (hasDerivAt_const t (z.1 i)).sub
    ((hasDerivAt_id t).mul_const (applyQ Q z.2 i))

theorem shearA_magnetic_derivative (Q : ι → ι → ℝ) (z : State ι)
    (t : ℝ) (i : ι) :
    HasDerivAt (fun s => (shearA Q s z).2 i) 0 t :=
  hasDerivAt_const t (z.2 i)

theorem shearB_displacement_derivative (Q : ι → ι → ℝ) (z : State ι)
    (t : ℝ) (i : ι) :
    HasDerivAt (fun s => (shearB Q s z).1 i) 0 t :=
  hasDerivAt_const t (z.1 i)

theorem shearB_magnetic_derivative (Q : ι → ι → ℝ) (z : State ι)
    (t : ℝ) (i : ι) :
    HasDerivAt (fun s => (shearB Q s z).2 i)
      (-applyQ Q (fieldE z.1) i) t := by
  simpa [shearB] using (hasDerivAt_const t (z.2 i)).sub
    ((hasDerivAt_id t).mul_const (applyQ Q (fieldE z.1) i))

/-- Both updates use the same matrix and material inverse for all input states. -/
theorem lieStep_formula (Q : ι → ι → ℝ) (t : ℝ) (z : State ι) :
    lieStep Q t z =
      (fun i => z.1 i - t * applyQ Q z.2 i,
       fun i => z.2 i - t * applyQ Q
         (fun j => materialInverse (z.1 j - t * applyQ Q z.2 j)) i) := rfl

/-- The update can use the closed sinh/asinh material formula directly,
without solving a minimization problem or cubic root problem at each stage. -/
theorem lieStep_explicit_formula (Q : ι → ι → ℝ) (t : ℝ) (z : State ι) :
    lieStep Q t z =
      (fun i => z.1 i - t * applyQ Q z.2 i,
       fun i => z.2 i - t * applyQ Q
         (fun j => ExplicitMaterial.electricOfDisplacement
           (z.1 j - t * applyQ Q z.2 j)) i) := by
  rw [lieStep_formula]
  simp only [ExplicitMaterial.electricOfDisplacement_eq_materialInverse]

theorem lieStep_zero (Q : ι → ι → ℝ) (z : State ι) : lieStep Q 0 z = z := by
  rw [lieStep, shearA_zero, shearB_zero]

/-- The inverse reverses the order of the two subflows. -/
theorem lieStep_inverse (Q : ι → ι → ℝ) (t : ℝ) (z : State ι) :
    shearA Q (-t) (shearB Q (-t) (lieStep Q t z)) = z := by
  rw [lieStep, shearB_inverse, shearA_inverse]

/-- Its displacement derivative at zero is already the full physical rate. -/
theorem lieStep_displacement_derivative_zero
    (Q : ι → ι → ℝ) (z : State ι) (i : ι) :
    HasDerivAt (fun t => (lieStep Q t z).1 i) (-applyQ Q z.2 i) 0 :=
  shearA_displacement_derivative Q z 0 i

/-- The magnetic derivative at zero also agrees with the full coupled system.
This is first-order consistency, not equality with a finite-time flow. -/
theorem lieStep_magnetic_derivative_zero
    (Q : ι → ι → ℝ) (z : State ι) (i : ι) :
    HasDerivAt (fun t => (lieStep Q t z).2 i)
      (-applyQ Q (fieldE z.1) i) 0 := by
  let v : ℝ → ℝ := fun t => applyQ Q
    (fun j => materialInverse (z.1 j - t * applyQ Q z.2 j)) i
  let v' : ℝ := ∑ j, Q i j *
    ((1 / (1 + materialInverse (z.1 j) ^ 2)) * (-applyQ Q z.2 j))
  have hd : ∀ j, HasDerivAt
      (fun t : ℝ => materialInverse (z.1 j - t * applyQ Q z.2 j))
      ((1 / (1 + materialInverse (z.1 j) ^ 2)) * (-applyQ Q z.2 j)) 0 := by
    intro j
    have h := (ExplicitMaterial.hasDerivAt_materialInverse
      (z.1 j - 0 * applyQ Q z.2 j)).comp 0
      ((hasDerivAt_const 0 (z.1 j)).sub
        ((hasDerivAt_id 0).mul_const (applyQ Q z.2 j)))
    simpa using h
  have hv : HasDerivAt v v' 0 := by
    exact HasDerivAt.fun_sum (fun j _ => (hd j).const_mul (Q i j))
  have h := (hasDerivAt_const 0 (z.2 i)).sub ((hasDerivAt_id 0).mul hv)
  simpa [v, lieStep, shearA, shearB, fieldE] using h

/-- The discrepancy between the two orders is already visible in D. -/
theorem displacement_commutator (Q : ι → ι → ℝ)
    (s t : ℝ) (z : State ι) (i : ι) :
    (shearA Q s (shearB Q t z)).1 i -
        (shearB Q t (shearA Q s z)).1 i =
      s * t * applyQ Q (applyQ Q (fieldE z.1)) i := by
  have hq : applyQ Q (fun j => z.2 j - t * applyQ Q (fieldE z.1) j) i =
      applyQ Q z.2 i - t * applyQ Q (applyQ Q (fieldE z.1)) i := by
    simp only [applyQ, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    ring_nf
  dsimp [shearA, shearB]
  rw [hq]
  ring_nf

/-- A nonzero commutator coefficient forbids exchanging the two subflows. -/
theorem shears_do_not_commute (Q : ι → ι → ℝ)
    (s t : ℝ) (z : State ι) (i : ι)
    (hs : s ≠ 0) (ht : t ≠ 0)
    (hQ : applyQ Q (applyQ Q (fieldE z.1)) i ≠ 0) :
    shearA Q s (shearB Q t z) ≠ shearB Q t (shearA Q s z) := by
  intro heq
  have h := displacement_commutator Q s t z i
  rw [heq, sub_self] at h
  exact (mul_ne_zero (mul_ne_zero hs ht) hQ) h.symm

/-- Exact residual of the coupled displacement equation along the one-step
Lie curve. Its leading factor is the physical time t, not a hidden clock. -/
theorem lieStep_displacement_residual (Q : ι → ι → ℝ)
    (t : ℝ) (z : State ι) (i : ι) :
    (-applyQ Q z.2 i) - (-applyQ Q (lieStep Q t z).2 i) =
      -t * applyQ Q (applyQ Q (fieldE (lieStep Q t z).1)) i := by
  have hq : applyQ Q
      (fun j => z.2 j - t * applyQ Q (fieldE (shearA Q t z).1) j) i =
      applyQ Q z.2 i - t * applyQ Q
        (applyQ Q (fieldE (shearA Q t z).1)) i := by
    simp only [applyQ, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    ring_nf
  change (-applyQ Q z.2 i) - (-applyQ Q
      (fun j => z.2 j - t * applyQ Q (fieldE (shearA Q t z).1) j) i) = _
  rw [hq]
  change (-applyQ Q z.2 i) - (-(applyQ Q z.2 i - t *
      applyQ Q (applyQ Q (fieldE (shearA Q t z).1)) i)) =
    -t * applyQ Q (applyQ Q (fieldE (shearA Q t z).1)) i
  ring

/-- At a nonzero residual, this finite-time curve is not an exact Maxwell
solution. A convergent product limit requires a separate argument. -/
theorem lieStep_not_exact_at_nonzero_residual (Q : ι → ι → ℝ)
    (t : ℝ) (z : State ι) (i : ι) (ht : t ≠ 0)
    (hQ : applyQ Q (applyQ Q (fieldE (lieStep Q t z).1)) i ≠ 0) :
    ¬ HasDerivAt (fun s => (lieStep Q s z).1 i)
      (-applyQ Q (lieStep Q t z).2 i) t := by
  intro h
  have hd := shearA_displacement_derivative Q z t i
  change HasDerivAt (fun s => (lieStep Q s z).1 i) (-applyQ Q z.2 i) t at hd
  have heq := hd.unique h
  have hr := lieStep_displacement_residual Q t z i
  rw [heq, sub_self] at hr
  exact (mul_ne_zero (neg_ne_zero.mpr ht) hQ) hr.symm

end

end KerrKoopman.ExactShear
