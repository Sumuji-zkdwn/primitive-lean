import ElasticaOperatorTheory

/-!
An additive fixed-endpoint/tangent realization of observational refinement.
The operation is a finite transition on three explicitly constructed smooth
angle functions. No continuous deformation, local middle replacement,
stationarity, or physical dynamics is asserted.
-/
noncomputable section
open scoped Interval

namespace FixedBoundaryWitness

open LinearInputOperatorWords
open LinearInputOperatorRefinement

def f (s : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.sin (2 * Real.pi * s) -
    (1 / 4 : ℝ) * Real.sin (4 * Real.pi * s)

def angle (i : Fin 3) : ℝ → ℝ :=
  if i = 0 then f else if i = 1 then (fun s => -f s)
  else (fun s => f (s + 1 / 2))

theorem f_contDiff : ContDiff ℝ ⊤ f := by
  unfold f
  fun_prop

theorem f_odd (s : ℝ) : f (-s) = -f s := by
  simp [f, mul_neg, Real.sin_neg]
  ring

theorem f_periodic : Function.Periodic f 1 := by
  intro s
  have h₁ : 2 * Real.pi * (s + 1) = 2 * Real.pi * s + 2 * Real.pi := by ring
  have h₂ : 4 * Real.pi * (s + 1) =
      (4 * Real.pi * s + 2 * Real.pi) + 2 * Real.pi := by ring
  simp only [f, h₁, h₂, Real.sin_add_two_pi]

theorem f_reflect (s : ℝ) : f (1 - s) = -f s := by
  have h := f_periodic (-s)
  have e : -s + 1 = 1 - s := by ring
  rw [e, f_odd] at h
  exact h

theorem f_zero : f 0 = 0 := by simp [f]

theorem f_one : f 1 = 0 := by
  have h := f_periodic 0
  simpa [f_zero] using h

theorem f_half : f (1 / 2) = 0 := by
  have h₁ : 2 * Real.pi * (1 / 2 : ℝ) = Real.pi := by ring
  have h₂ : 4 * Real.pi * (1 / 2 : ℝ) = 2 * Real.pi := by ring
  unfold f
  rw [h₁, h₂]
  simp

theorem f_quarter : f (1 / 4) = 1 / 2 := by
  have h₁ : 2 * Real.pi * (1 / 4 : ℝ) = Real.pi / 2 := by ring
  have h₂ : 4 * Real.pi * (1 / 4 : ℝ) = Real.pi := by ring
  unfold f
  rw [h₁, h₂]
  norm_num

theorem angle_initial (i : Fin 3) : angle i 0 = 0 := by
  fin_cases i
  · simpa [angle] using f_zero
  · simp [angle, f_zero]
  · change f ((0 : ℝ) + 1 / 2) = 0
    simpa only [zero_add] using f_half

theorem angle_final (i : Fin 3) : angle i 1 = 0 := by
  fin_cases i
  · simpa [angle] using f_one
  · simp [angle, f_one]
  · change f ((1 : ℝ) + 1 / 2) = 0
    rw [add_comm, f_periodic, f_half]

theorem hasDeriv_f (s : ℝ) :
    HasDerivAt f (Real.pi * Real.cos (2 * Real.pi * s) -
      Real.pi * Real.cos (4 * Real.pi * s)) s := by
  unfold f
  convert (((((hasDerivAt_id s).const_mul (2 * Real.pi)).sin).const_mul
      (1 / 2 : ℝ)).sub
    (((((hasDerivAt_id s).const_mul (4 * Real.pi)).sin).const_mul
      (1 / 4 : ℝ)))) using 1
  · rfl
  · simp only [id_eq]
    ring

theorem curvature_zero :
    Elastica.curvature (angle (0 : Fin 3)) 0 = 0 := by
  change deriv f 0 = 0
  simpa using (hasDeriv_f 0).deriv

theorem curvature_one :
    Elastica.curvature (angle (1 : Fin 3)) 0 = 0 := by
  change deriv (fun s => -f s) 0 = 0
  simpa using! (hasDeriv_f 0).neg.deriv

theorem curvature_two :
    Elastica.curvature (angle (2 : Fin 3)) 0 = -2 * Real.pi := by
  change deriv (fun s => f (s + 1 / 2)) 0 = -2 * Real.pi
  have h₁ : 2 * Real.pi * (1 / 2 : ℝ) = Real.pi := by ring
  have h₂ : 4 * Real.pi * (1 / 2 : ℝ) = 2 * Real.pi := by ring
  have hi : HasDerivAt (fun s : ℝ => s + 1 / 2) 1 0 := by
    simpa using! ((hasDerivAt_id (0 : ℝ)).add_const (1 / 2 : ℝ))
  have ho : HasDerivAt f
      (Real.pi * Real.cos (2 * Real.pi * (1 / 2)) -
        Real.pi * Real.cos (4 * Real.pi * (1 / 2)))
      ((fun s : ℝ => s + 1 / 2) 0) := by
    simpa only [zero_add] using (hasDeriv_f (1 / 2))
  have h := ho.comp (0 : ℝ) (h := fun s : ℝ => s + 1 / 2) (h' := 1) hi
  rw [h₁, h₂] at h
  simp only [Real.cos_pi, Real.cos_two_pi, mul_one] at h
  calc
    deriv (fun s => f (s + 1 / 2)) 0 = Real.pi * -1 - Real.pi := h.deriv
    _ = -2 * Real.pi := by ring

theorem angle_zero_ne_one : angle (0 : Fin 3) ≠ angle 1 := by
  intro h
  have hp := congrFun h (1 / 4)
  change f (1 / 4) = -f (1 / 4) at hp
  rw [f_quarter] at hp
  norm_num at hp

theorem angle_zero_ne_two : angle (0 : Fin 3) ≠ angle 2 := by
  intro h
  have hp := congrArg (fun θ => Elastica.curvature θ 0) h
  change Elastica.curvature (angle 0) 0 =
    Elastica.curvature (angle 2) 0 at hp
  rw [curvature_zero, curvature_two] at hp
  linarith [Real.pi_pos]

theorem angle_one_ne_two : angle (1 : Fin 3) ≠ angle 2 := by
  intro h
  have hp := congrArg (fun θ => Elastica.curvature θ 0) h
  change Elastica.curvature (angle 1) 0 =
    Elastica.curvature (angle 2) 0 at hp
  rw [curvature_one, curvature_two] at hp
  linarith [Real.pi_pos]

theorem angle_injective : Function.Injective angle := by
  intro i j h
  fin_cases i <;> fin_cases j
  · rfl
  · exact (angle_zero_ne_one h).elim
  · exact (angle_zero_ne_two h).elim
  · exact (angle_zero_ne_one h.symm).elim
  · rfl
  · exact (angle_one_ne_two h).elim
  · exact (angle_zero_ne_two h.symm).elim
  · exact (angle_one_ne_two h.symm).elim
  · rfl

theorem angle_smooth (i : Fin 3) : ContDiff ℝ ⊤ (angle i) := by
  fin_cases i
  · exact f_contDiff
  · exact f_contDiff.neg
  · exact f_contDiff.comp (contDiff_id.add contDiff_const)

theorem sin_f_integral_zero :
    (∫ s in (0 : ℝ)..1, Real.sin (f s)) = 0 := by
  have hreflect :
      (∫ s in (0 : ℝ)..1, Real.sin (f (1 - s))) =
        ∫ s in (0 : ℝ)..1, Real.sin (f s) := by
    simpa using intervalIntegral.integral_comp_sub_left
      (a := (0 : ℝ)) (b := (1 : ℝ)) (fun s => Real.sin (f s)) 1
  have hneg :
      (∫ s in (0 : ℝ)..1, Real.sin (f (1 - s))) =
        -(∫ s in (0 : ℝ)..1, Real.sin (f s)) := by
    simp only [f_reflect, Real.sin_neg, intervalIntegral.integral_neg]
  linarith

theorem shifted_integral (g : ℝ → ℝ) :
    (∫ s in (0 : ℝ)..1, g (f (s + 1 / 2))) =
      ∫ s in (0 : ℝ)..1, g (f s) := by
  have hp : Function.Periodic (fun s => g (f s)) 1 := by
    intro s
    exact congrArg g (f_periodic s)
  calc
    (∫ s in (0 : ℝ)..1, g (f (s + 1 / 2))) =
        ∫ s in (1 / 2 : ℝ)..1 / 2 + 1, g (f s) := by
          simpa [add_comm] using intervalIntegral.integral_comp_add_right
            (a := (0 : ℝ)) (b := (1 : ℝ)) (fun s => g (f s)) (1 / 2)
    _ = ∫ s in (0 : ℝ)..1, g (f s) := by
          simpa using hp.intervalIntegral_add_eq (1 / 2) 0

theorem common_x_endpoint (i : Fin 3) :
    Elastica.xCoord (angle i) 0 1 = Elastica.xCoord f 0 1 := by
  fin_cases i
  · rfl
  · change Elastica.xCoord (fun s => -f s) 0 1 = Elastica.xCoord f 0 1
    simp [Elastica.xCoord, Real.cos_neg]
  · change Elastica.xCoord (fun s => f (s + 1 / 2)) 0 1 = Elastica.xCoord f 0 1
    simp only [Elastica.xCoord, zero_add]
    exact shifted_integral Real.cos

theorem common_y_endpoint (i : Fin 3) :
    Elastica.yCoord (angle i) 0 1 = 0 := by
  fin_cases i
  · simpa [Elastica.yCoord] using! sin_f_integral_zero
  · change Elastica.yCoord (fun s => -f s) 0 1 = 0
    simp [Elastica.yCoord, Real.sin_neg, sin_f_integral_zero]
  · change Elastica.yCoord (fun s => f (s + 1 / 2)) 0 1 = 0
    simp only [Elastica.yCoord, zero_add]
    rw [shifted_integral Real.sin, sin_f_integral_zero]

theorem unit_speed (i : Fin 3) (s : ℝ) :
    (deriv (Elastica.xCoord (angle i) 0) s)^2 +
      (deriv (Elastica.yCoord (angle i) 0) s)^2 = 1 :=
  Elastica.unit_speed_squared (angle_smooth i).continuous 0 0 s

/-- All three states have the same initial/final tangent angle and endpoints. -/
theorem shared_boundary (i j : Fin 3) :
    angle i 0 = angle j 0 ∧ angle i 1 = angle j 1 ∧
      Elastica.xCoord (angle i) 0 1 = Elastica.xCoord (angle j) 0 1 ∧
      Elastica.yCoord (angle i) 0 1 = Elastica.yCoord (angle j) 0 1 := by
  exact ⟨(angle_initial i).trans (angle_initial j).symm,
    (angle_final i).trans (angle_final j).symm,
    (common_x_endpoint i).trans (common_x_endpoint j).symm,
    (common_y_endpoint i).trans (common_y_endpoint j).symm⟩

/-- The quadratic bending integral is an optional specialization. -/
def quadraticBending (i : Fin 3) : ℝ :=
  ∫ s in (0 : ℝ)..1, (Elastica.curvature (angle i) s)^2

theorem f_deriv_periodic : Function.Periodic (deriv f) 1 := by
  intro s
  have hf : (fun t : ℝ => f (t + 1)) = f := funext f_periodic
  have hd := congrFun (congrArg deriv hf) s
  rw [deriv_comp_add_const] at hd
  exact hd

theorem periodic_halfshift_integral (g : ℝ → ℝ)
    (hg : Function.Periodic g 1) :
    (∫ s in (0 : ℝ)..1, g (s + 1 / 2)) =
      ∫ s in (0 : ℝ)..1, g s := by
  calc
    (∫ s in (0 : ℝ)..1, g (s + 1 / 2)) =
        ∫ s in (1 / 2 : ℝ)..1 / 2 + 1, g s := by
          simp [intervalIntegral.integral_comp_add_right, add_comm]
    _ = ∫ s in (0 : ℝ)..1, g s := by
          simpa using hg.intervalIntegral_add_eq (1 / 2) 0

theorem quadratic_bending_equal (i : Fin 3) :
    quadraticBending i = quadraticBending 0 := by
  fin_cases i
  · rfl
  · change (∫ s in (0 : ℝ)..1, (deriv (fun t => -f t) s)^2) =
      ∫ s in (0 : ℝ)..1, (deriv f s)^2
    have hneg (s : ℝ) : deriv (fun t => -f t) s = -(deriv f s) := by
      change deriv (-f) s = -(deriv f s)
      exact deriv.neg
    simp only [hneg, neg_sq]
  · change (∫ s in (0 : ℝ)..1, (deriv (fun t => f (t + 1 / 2)) s)^2) =
      ∫ s in (0 : ℝ)..1, (deriv f s)^2
    simp only [deriv_comp_add_const]
    exact periodic_halfshift_integral (fun s => (deriv f s)^2) (by
      intro s
      change (deriv f (s + 1))^2 = (deriv f s)^2
      rw [f_deriv_periodic s])

/-- Observe initial signed curvature, as in #100. -/
def observer (i : Fin 3) : ℝ := Elastica.curvature (angle i) 0

/-- These are the old and fresh transitions already present in operator theory. -/
def oldStep : Unit → Fin 3 → Fin 3 := baseStep
def freshStep : Unit → Fin 3 → Fin 3 := witnessFresh

theorem old_preserves_boundary (a : Unit) (i : Fin 3) :
    angle (oldStep a i) 0 = angle i 0 ∧
    angle (oldStep a i) 1 = angle i 1 ∧
    Elastica.xCoord (angle (oldStep a i)) 0 1 = Elastica.xCoord (angle i) 0 1 ∧
    Elastica.yCoord (angle (oldStep a i)) 0 1 = Elastica.yCoord (angle i) 0 1 :=
  shared_boundary (oldStep a i) i

theorem fresh_preserves_boundary (a : Unit) (i : Fin 3) :
    angle (freshStep a i) 0 = angle i 0 ∧
    angle (freshStep a i) 1 = angle i 1 ∧
    Elastica.xCoord (angle (freshStep a i)) 0 1 = Elastica.xCoord (angle i) 0 1 ∧
    Elastica.yCoord (angle (freshStep a i)) 0 1 = Elastica.yCoord (angle i) 0 1 :=
  shared_boundary (freshStep a i) i

theorem run_old (word : List Unit) (i : Fin 3) :
    run oldStep word i = i := by
  induction word generalizing i with
  | nil => rfl
  | cons a tail ih =>
      change run oldStep tail i = i
      exact ih i

theorem old_indistinguishable :
    WordEq observer oldStep (0 : Fin 3) (1 : Fin 3) := by
  intro word
  rw [run_old, run_old]
  exact curvature_zero.trans curvature_one.symm

theorem fresh_distinguishes :
    ¬ WordEq observer (sumStep oldStep freshStep)
      (0 : Fin 3) (1 : Fin 3) := by
  intro h
  have heq : (0 : ℝ) = -2 * Real.pi := by
    simpa [run, sumStep, freshStep, witnessFresh, observer,
      curvature_zero, curvature_two] using h [Sum.inr ()]
  linarith [Real.pi_pos]

/-- A fixed-boundary curve family instantiates the existing quotient theorem. -/
theorem fixed_boundary_quotient_splits :
    ∃ q r : State observer (sumStep oldStep freshStep),
      q ≠ r ∧ forget observer oldStep freshStep q =
        forget observer oldStep freshStep r :=
  strict_refinement_splits_quotient observer oldStep freshStep 0 1
    old_indistinguishable fresh_distinguishes

/-- Geometry, equal bending energy, and the actual quotient split together. -/
theorem fixed_boundary_realization :
    (∀ i : Fin 3, ContDiff ℝ ⊤ (angle i)) ∧
    Function.Injective angle ∧
    (∀ (i : Fin 3) (s : ℝ),
      (deriv (Elastica.xCoord (angle i) 0) s)^2 +
        (deriv (Elastica.yCoord (angle i) 0) s)^2 = 1) ∧
    (∀ i j : Fin 3,
      angle i 0 = angle j 0 ∧ angle i 1 = angle j 1 ∧
      Elastica.xCoord (angle i) 0 1 = Elastica.xCoord (angle j) 0 1 ∧
      Elastica.yCoord (angle i) 0 1 = Elastica.yCoord (angle j) 0 1) ∧
    (∀ i : Fin 3, quadraticBending i = quadraticBending 0) ∧
    (∃ q r : State observer (sumStep oldStep freshStep),
      q ≠ r ∧ forget observer oldStep freshStep q =
        forget observer oldStep freshStep r) :=
  ⟨angle_smooth, angle_injective, unit_speed, shared_boundary, quadratic_bending_equal,
    fixed_boundary_quotient_splits⟩

/-- Work directly with the three distinct actual angle functions. -/
abbrev RepresentedCurve := Set.range angle

def curveEquiv : Fin 3 ≃ RepresentedCurve := Equiv.ofInjective angle angle_injective

def curveObserver (θ : RepresentedCurve) : ℝ := Elastica.curvature θ.val 0

def curveOld (a : Unit) (θ : RepresentedCurve) : RepresentedCurve :=
  curveEquiv (oldStep a (curveEquiv.symm θ))

def curveFresh (a : Unit) (θ : RepresentedCurve) : RepresentedCurve :=
  curveEquiv (freshStep a (curveEquiv.symm θ))

theorem curve_readout (i : Fin 3) : curveObserver (curveEquiv i) = observer i := rfl

theorem curve_old_step (a : Unit) (i : Fin 3) :
    curveEquiv (oldStep a i) = curveOld a (curveEquiv i) := by
  simp [curveOld]

theorem curve_extended_step (a : Sum Unit Unit) (i : Fin 3) :
    curveEquiv (sumStep oldStep freshStep a i) =
      sumStep curveOld curveFresh a (curveEquiv i) := by
  cases a <;> simp [sumStep, curveOld, curveFresh]

theorem curve_old_indistinguishable :
    WordEq curveObserver curveOld (curveEquiv 0) (curveEquiv 1) :=
  (representation_word_eq observer oldStep curveEquiv curveOld curveObserver
    curve_readout curve_old_step 0 1).mp old_indistinguishable

theorem curve_fresh_distinguishes :
    ¬ WordEq curveObserver (sumStep curveOld curveFresh)
      (curveEquiv 0) (curveEquiv 1) := by
  intro h
  apply fresh_distinguishes
  exact (representation_word_eq observer (sumStep oldStep freshStep)
    curveEquiv (sumStep curveOld curveFresh) curveObserver
    curve_readout curve_extended_step 0 1).mpr h

theorem represented_curve_split :
    ∃ q r : State curveObserver (sumStep curveOld curveFresh),
      q ≠ r ∧ forget curveObserver curveOld curveFresh q =
        forget curveObserver curveOld curveFresh r :=
  strict_refinement_splits_quotient curveObserver curveOld curveFresh
    (curveEquiv 0) (curveEquiv 1)
    curve_old_indistinguishable curve_fresh_distinguishes

theorem represented_curve_smooth (θ : RepresentedCurve) : ContDiff ℝ ⊤ θ.val := by
  obtain ⟨i, hi⟩ := θ.property
  rw [← hi]
  exact angle_smooth i

theorem represented_unit_speed (θ : RepresentedCurve) (s : ℝ) :
    (deriv (Elastica.xCoord θ.val 0) s)^2 +
      (deriv (Elastica.yCoord θ.val 0) s)^2 = 1 := by
  obtain ⟨i, hi⟩ := θ.property
  rw [← hi]
  exact unit_speed i s

theorem represented_curve_boundary (θ φ : RepresentedCurve) :
    θ.val 0 = φ.val 0 ∧ θ.val 1 = φ.val 1 ∧
    Elastica.xCoord θ.val 0 1 = Elastica.xCoord φ.val 0 1 ∧
    Elastica.yCoord θ.val 0 1 = Elastica.yCoord φ.val 0 1 := by
  obtain ⟨i, hi⟩ := θ.property
  obtain ⟨j, hj⟩ := φ.property
  rw [← hi, ← hj]
  exact shared_boundary i j

/-- The refinement is also proved on the type of actual angle functions. -/
theorem represented_curve_realization :
    (∀ θ : RepresentedCurve, ContDiff ℝ ⊤ θ.val) ∧
    (∀ (θ : RepresentedCurve) (s : ℝ),
      (deriv (Elastica.xCoord θ.val 0) s)^2 +
        (deriv (Elastica.yCoord θ.val 0) s)^2 = 1) ∧
    (∀ θ φ : RepresentedCurve,
      θ.val 0 = φ.val 0 ∧ θ.val 1 = φ.val 1 ∧
      Elastica.xCoord θ.val 0 1 = Elastica.xCoord φ.val 0 1 ∧
      Elastica.yCoord θ.val 0 1 = Elastica.yCoord φ.val 0 1) ∧
    (∃ q r : State curveObserver (sumStep curveOld curveFresh),
      q ≠ r ∧ forget curveObserver curveOld curveFresh q =
        forget curveObserver curveOld curveFresh r) :=
  ⟨represented_curve_smooth, represented_unit_speed, represented_curve_boundary,
    represented_curve_split⟩

#print axioms shared_boundary
#print axioms curvature_two
#print axioms fixed_boundary_quotient_splits
#print axioms fixed_boundary_realization
#print axioms represented_curve_realization

end FixedBoundaryWitness
