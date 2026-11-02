/-!
# Two shear generators from one verified polynomial-energy gradient

This is an additive supplement to VariablePairObservations.inc.
The potential E_k(x,u)=k*x^2/2+u*x is the k,lam=a=c=0,
signed-input s=+1 slice of the existing real energy family.

The SAME actual gradient G_k(x,u)=(k*x+u,x), combined with
coordinate swap P(x,u)=(u,x), gives
A_k=G_k ∘ P and B_k=P ∘ G_k.

We prove inverse-order cancellation, the nontrivial commutator,
unit determinant, trace 2+(ab)^2, and an exact exponential lower
bound for the unit commutator. This is discrete algebra, not a
physical energy or no-work amplifier.

The choice of sign s=+1, the swap, and the alternating word are
explicit model choices, not consequences forced by variational
minimality. The existing derivation of the gradient IS reused.
-/

noncomputable section

namespace LinearInputShearCommutator

open LinearInputVariablePairs

/-- The chosen signed-input potential is already in the polynomial family. -/
theorem source_energy (k x u : ℝ) :
    energy k 0 0 0 x 0 (-u) = k * x ^ 2 / 2 + u * x := by
  unfold energy
  ring

/-- An exact slice of the ORIGINAL primitive Design.E, not just its extension. -/
theorem source_is_original_energy (k x u : ℝ) :
    LinearInputDesign.E 0 (k - 2) (-u) x 0 =
      energy k 0 0 0 x 0 (-u) := by
  calc
    LinearInputDesign.E 0 (k - 2) (-u) x 0 =
        energy ((k - 2) + 2) 0 1 (Real.sqrt 2) x 0 (-u) :=
      (energy_eq_primitive 0 (k - 2) (-u) x 0).symm
    _ = energy k 0 0 0 x 0 (-u) := by
      unfold energy
      ring

theorem original_potential_formula (k x u : ℝ) :
    LinearInputDesign.E 0 (k - 2) (-u) x 0 =
      k * x ^ 2 / 2 + u * x := by
  rw [source_is_original_energy, source_energy]

def pairSwap (z : ℝ × ℝ) : ℝ × ℝ := (z.2, z.1)

/-- A specialization of the actual derivative pair, not a postulated map. -/
def gradient (k : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  gradXu k 0 0 0 1 0 z

theorem gradient_formula (k : ℝ) (z : ℝ × ℝ) :
    gradient k z = (k * z.1 + z.2, z.1) := by
  change gradXu k 0 0 0 1 0 z = _
  rw [gradXu_formula]
  apply Prod.ext <;> dsimp <;> ring

/-- The same derivative pair computed directly from the original Design.E. -/
theorem original_gradient_formula (k : ℝ) (z : ℝ × ℝ) :
    (deriv (fun t : ℝ => LinearInputDesign.E 0 (k - 2) (-z.2) t 0) z.1,
     deriv (fun t : ℝ => LinearInputDesign.E 0 (k - 2) (-t) z.1 0) z.2) =
      (k * z.1 + z.2, z.1) := by
  have hx :
      (fun t : ℝ => LinearInputDesign.E 0 (k - 2) (-z.2) t 0) =
        (fun t : ℝ => energy k 0 0 0 t 0 (-z.2)) := by
    funext t
    exact source_is_original_energy k t z.2
  have hu :
      (fun t : ℝ => LinearInputDesign.E 0 (k - 2) (-t) z.1 0) =
        (fun t : ℝ => energy k 0 0 0 z.1 0 (-t)) := by
    funext t
    exact source_is_original_energy k z.1 t
  rw [hx, hu]
  simpa only [gradient, gradXu, neg_one_mul] using gradient_formula k z

def shearA (a : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  gradient a (pairSwap z)

def shearB (b : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  pairSwap (gradient b z)

/-- Swapping the inputs BEFORE the source gradient produces the x-shear. -/
theorem shearA_formula (a : ℝ) (z : ℝ × ℝ) :
    shearA a z = (z.1 + a * z.2, z.2) := by
  change gradient a (pairSwap z) = _
  rw [gradient_formula]
  apply Prod.ext <;> (dsimp [pairSwap]; ring)

/-- Swapping the outputs AFTER the same source gradient produces the y-shear. -/
theorem shearB_formula (b : ℝ) (z : ℝ × ℝ) :
    shearB b z = (z.1, z.2 + b * z.1) := by
  change pairSwap (gradient b z) = _
  rw [gradient_formula]
  apply Prod.ext <;> (dsimp [pairSwap]; ring)

def undoA (a : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.1 - a * z.2, z.2)

def undoB (b : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.1, z.2 - b * z.1)

theorem undoA_left (a : ℝ) (z : ℝ × ℝ) :
    undoA a (shearA a z) = z := by
  rw [shearA_formula]
  apply Prod.ext <;> (dsimp [undoA]; ring)

theorem undoA_right (a : ℝ) (z : ℝ × ℝ) :
    shearA a (undoA a z) = z := by
  rw [shearA_formula]
  apply Prod.ext <;> (dsimp [undoA]; ring)

theorem undoB_left (b : ℝ) (z : ℝ × ℝ) :
    undoB b (shearB b z) = z := by
  rw [shearB_formula]
  apply Prod.ext <;> (dsimp [undoB]; ring)

theorem undoB_right (b : ℝ) (z : ℝ × ℝ) :
    shearB b (undoB b z) = z := by
  rw [shearB_formula]
  apply Prod.ext <;> (dsimp [undoB]; ring)

/-- The genuine inverse order B^-1 then A^-1 cancels A then B. -/
theorem correct_reverse_order (a b : ℝ) (z : ℝ × ℝ) :
    undoA a (undoB b (shearB b (shearA a z))) = z := by
  rw [undoB_left, undoA_left]

/-- Execute A, B, inverse A, inverse B, deliberately in wrong reverse order. -/
def loop (a b : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  undoB b (undoA a (shearB b (shearA a z)))

/-- Exact real polynomial commutator matrix, with no matrix assumptions. -/
theorem loop_formula (a b : ℝ) (z : ℝ × ℝ) :
    loop a b z =
      ((1 - a*b) * z.1 - a^2*b*z.2,
       a*b^2*z.1 + (1 + a*b + a^2*b^2)*z.2) := by
  unfold loop
  rw [shearA_formula, shearB_formula]
  apply Prod.ext <;> dsimp [undoB, undoA] <;> ring

/-- The product of the two diagonal terms minus the off-diagonal product. -/
theorem loop_determinant (a b : ℝ) :
    (1-a*b) * (1+a*b+a^2*b^2) - (-a^2*b) * (a*b^2) = 1 := by
  ring

theorem loop_trace (a b : ℝ) :
    (1-a*b) + (1+a*b+a^2*b^2) = 2 + (a*b)^2 := by
  ring

/-- Both nonzero shear parameters make the determinant-one map hyperbolic. -/
theorem loop_trace_gt_two (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    2 < (1-a*b) + (1+a*b+a^2*b^2) := by
  rw [loop_trace]
  have hab : a*b ≠ 0 := mul_ne_zero ha hb
  nlinarith [sq_pos_of_ne_zero hab]

theorem shears_do_not_commute :
    shearB 1 (shearA 1 ((1 : ℝ), 0)) ≠
      shearA 1 (shearB 1 ((1 : ℝ), 0)) := by
  norm_num [shearA_formula, shearB_formula]

theorem loop_one_formula (z : ℝ × ℝ) :
    loop 1 1 z = (-z.2, z.1 + 3*z.2) := by
  rw [loop_formula]
  apply Prod.ext <;> dsimp <;> ring

/-- The explicitly reported first four full cycles. -/
theorem reported_trajectory :
    loop 1 1 ((1 : ℝ), 0) = ((0 : ℝ), 1) ∧
    loop 1 1 ((0 : ℝ), 1) = ((-1 : ℝ), 3) ∧
    loop 1 1 ((-1 : ℝ), 3) = ((-3 : ℝ), 8) ∧
    loop 1 1 ((-3 : ℝ), 8) = ((-8 : ℝ), 21) := by
  norm_num [loop_one_formula]

/-- Cayley-Hamilton in the concrete unit-coefficient 2D representation. -/
theorem loop_cayley_hamilton (z : ℝ × ℝ) :
    loop 1 1 (loop 1 1 z) =
      (3 * (loop 1 1 z).1 - z.1, 3 * (loop 1 1 z).2 - z.2) := by
  apply Prod.ext <;> simp [loop_one_formula] <;> ring

/-- The forward cone, including a quantitative lower slope bound. -/
def growthCone (z : ℝ × ℝ) : Prop :=
  0 < z.2 ∧ -z.2/2 ≤ z.1 ∧ z.1 ≤ 0

theorem growthCone_initial : growthCone ((0 : ℝ), 1) := by
  norm_num [growthCone]

theorem growthCone_preserved (z : ℝ × ℝ) (hz : growthCone z) :
    growthCone (loop 1 1 z) := by
  rcases hz with ⟨hy, hxlo, hxhi⟩
  rw [loop_one_formula]
  change 0 < z.1 + 3*z.2 ∧
    -(z.1 + 3*z.2)/2 ≤ -z.2 ∧ -z.2 ≤ 0
  constructor
  · linarith
  constructor
  · linarith
  · linarith

/-- Within this invariant cone the vertical displacement grows by >=5/2. -/
theorem growthCone_one_step (z : ℝ × ℝ) (hz : growthCone z) :
    (5 : ℝ)/2 * z.2 ≤ (loop 1 1 z).2 := by
  rw [loop_one_formula]
  change (5 : ℝ)/2 * z.2 ≤ z.1 + 3*z.2
  linarith [hz.2.1]

theorem growthCone_iterate (n : ℕ) :
    growthCone ((loop 1 1)^[n] ((0 : ℝ), 1)) := by
  induction n with
  | zero =>
      simpa only [Function.iterate_zero, id_eq] using growthCone_initial
  | succ n ih =>
      simpa only [Function.iterate_succ_apply'] using
        growthCone_preserved _ ih

/-- Exact exponential lower bound, beginning after the first A-B-A^-1-B^-1
cycle from (1,0). This establishes unbounded growth without diagonalization. -/
theorem exponential_lower_bound (n : ℕ) :
    ((5 : ℝ)/2)^n ≤ (((loop 1 1)^[n] ((0 : ℝ), 1)).2) := by
  induction n with
  | zero =>
      norm_num [Function.iterate_zero]
  | succ n ih =>
      have hstep :
          (5 : ℝ)/2 * (((loop 1 1)^[n] ((0 : ℝ), 1)).2) ≤
            (((loop 1 1)^[n+1] ((0 : ℝ), 1)).2) := by
        simpa only [Function.iterate_succ_apply'] using
          growthCone_one_step _ (growthCone_iterate n)
      calc
        ((5 : ℝ)/2)^(n+1) = ((5 : ℝ)/2) * ((5 : ℝ)/2)^n := by
          rw [pow_succ]
          ring
        _ ≤ ((5 : ℝ)/2) *
            (((loop 1 1)^[n] ((0 : ℝ), 1)).2) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ ≤ (((loop 1 1)^[n+1] ((0 : ℝ), 1)).2) := hstep

/-- The exact expanding characteristic root of the one-cycle matrix. -/
def expandingRoot : ℝ := (3 + Real.sqrt 5)/2

theorem expandingRoot_characteristic :
    expandingRoot^2 - 3*expandingRoot + 1 = 0 := by
  have hs : (Real.sqrt (5 : ℝ))^2 = 5 :=
    Real.sq_sqrt (by norm_num)
  dsimp [expandingRoot]
  nlinarith [hs]

theorem expandingRoot_gt_one : 1 < expandingRoot := by
  have hs := Real.sqrt_nonneg (5 : ℝ)
  dsimp [expandingRoot]
  linarith

theorem expandingRoot_golden_square :
    expandingRoot = ((1 + Real.sqrt (5 : ℝ))/2)^2 := by
  have hs : (Real.sqrt (5 : ℝ))^2 = 5 :=
    Real.sq_sqrt (by norm_num)
  dsimp [expandingRoot]
  nlinarith [hs]

end LinearInputShearCommutator
