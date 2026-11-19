import Mathlib

/-!
# Lebesgue measure preservation by Boole-type maps (orbit-trace section 3, (C))

Section 3 of `docs/research/2026-11-04-orbit-trace-integrals.md` states, as a hand
proof, that a rational map whose real inverse branches `r_j` are increasing with
`Σ_j r_j'(s) = 1` preserves Lebesgue measure: `∫ Φ(S x) dx = ∫ Φ(s) ds`. The note
records the analytic change of variables as not formalized in Lean.

* `integral_comp_eq_of_branches` proves the abstract statement: if finitely many
  differentiable branches `r i : ℝ → ℝ` satisfy `S ∘ r i = id`, have nonnegative
  derivatives summing to `1`, have pairwise disjoint ranges, and their ranges cover
  `ℝ` up to a null set, then `∫ g (S x) dx = ∫ g t dt` for every integrable `g`.
  The proof uses mathlib's one-dimensional change of variables
  (`integral_image_eq_integral_abs_deriv_smul`) on each branch and the Lusin–Souslin
  theorem for the measurability of the branch ranges.
* `boole_integral` instantiates it for Boole's map `S(x) = x - 1/x`
  (the case `m = 2`, `c = 0`, `a_1 = 0`, `b_1 = 1` of the note), with the explicit
  branches `(t ± √(t² + 4))/2`.

The three-branch map of the note (`m = 3`) needs its cubic inverse branches, which
are not constructed here.
-/

namespace OrbitTrace

open MeasureTheory Set

/-- **Abstract measure preservation through inverse branches.** -/
theorem integral_comp_eq_of_branches {ι : Type*} [Fintype ι] (S : ℝ → ℝ) (r r' : ι → ℝ → ℝ)
    (hderiv : ∀ i t, HasDerivAt (r i) (r' i t) t) (hnonneg : ∀ i t, 0 ≤ r' i t)
    (hinv : ∀ i t, S (r i t) = t)
    (hdisj : Pairwise (Function.onFun Disjoint fun i => range (r i)))
    (hnull : volume (⋃ i, range (r i))ᶜ = 0)
    (hsum : ∀ t, ∑ i, r' i t = 1) (g : ℝ → ℝ) (hg : Integrable g) :
    ∫ x, g (S x) = ∫ t, g t := by
  have hinj : ∀ i, Function.Injective (r i) := fun i a b h => by
    rw [← hinv i a, h, hinv i b]
  have hcont : ∀ i, Continuous (r i) := fun i =>
    continuous_iff_continuousAt.mpr fun t => (hderiv i t).continuousAt
  have hmeas : ∀ i, MeasurableSet (range (r i)) := fun i => by
    rw [← image_univ]
    exact MeasurableSet.univ.image_of_continuousOn_injOn (hcont i).continuousOn
      (hinj i).injOn
  have hderiv' : ∀ i, ∀ x ∈ (univ : Set ℝ), HasDerivWithinAt (r i) (r' i x) univ x :=
    fun i x _ => (hderiv i x).hasDerivWithinAt
  -- each derivative is at most 1, hence a bounded measurable weight
  have hle : ∀ i t, r' i t ≤ 1 := fun i t => by
    rw [← hsum t]
    exact Finset.single_le_sum (fun j _ => hnonneg j t) (Finset.mem_univ i)
  have hr'meas : ∀ i, Measurable (r' i) := fun i => by
    have : r' i = deriv (r i) := funext fun t => (hderiv i t).deriv.symm
    rw [this]
    exact measurable_deriv _
  have hweighted : ∀ i, Integrable (fun t => r' i t * g t) := fun i => by
    refine hg.bdd_mul (c := 1) (hr'meas i).aestronglyMeasurable ?_
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg i t)]
    exact hle i t
  -- change of variables on each branch
  have hbranch : ∀ i, ∫ x in range (r i), g (S x) = ∫ t, r' i t * g t := fun i => by
    rw [← image_univ, integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ (hderiv' i)
      (hinj i).injOn, setIntegral_univ]
    congr 1
    funext t
    rw [abs_of_nonneg (hnonneg i t), hinv, smul_eq_mul]
  have hint : ∀ i, IntegrableOn (fun x => g (S x)) (range (r i)) := fun i => by
    rw [← image_univ, integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
      (hderiv' i) (hinj i).injOn, integrableOn_univ]
    refine (hweighted i).congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [abs_of_nonneg (hnonneg i t), hinv, smul_eq_mul]
  -- the union of the ranges carries all the mass
  have hae : ∀ᵐ x ∂volume, x ∉ ⋃ i, range (r i) → g (S x) = 0 := by
    have := measure_eq_zero_iff_ae_notMem.mp hnull
    filter_upwards [this] with x hx hnot
    exact absurd (by simpa using hx) hnot
  rw [← setIntegral_eq_integral_of_ae_compl_eq_zero hae,
    integral_iUnion_fintype hmeas hdisj hint]
  simp only [hbranch]
  rw [← integral_finsetSum _ fun i _ => hweighted i]
  congr 1
  funext t
  rw [← Finset.sum_mul, hsum, one_mul]

/-! ## Boole's map `x - 1/x` -/

/-- The two inverse branches `(t ± √(t² + 4))/2` of `x ↦ x - 1/x`. -/
noncomputable def booleBranch (b : Bool) (t : ℝ) : ℝ :=
  (t + (if b then 1 else -1) * Real.sqrt (t ^ 2 + 4)) / 2

/-- Their derivatives `(1 ± t/√(t² + 4))/2`. -/
noncomputable def booleBranchDeriv (b : Bool) (t : ℝ) : ℝ :=
  (1 + (if b then 1 else -1) * (t / Real.sqrt (t ^ 2 + 4))) / 2

theorem sqrt_pos_aux (t : ℝ) : 0 < Real.sqrt (t ^ 2 + 4) :=
  Real.sqrt_pos.mpr (by positivity)

theorem sqrt_sq_aux (t : ℝ) : Real.sqrt (t ^ 2 + 4) ^ 2 = t ^ 2 + 4 :=
  Real.sq_sqrt (by positivity)

theorem abs_lt_sqrt_aux (t : ℝ) : |t| < Real.sqrt (t ^ 2 + 4) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_lt_sqrt (sq_nonneg t) (by linarith)

theorem booleBranch_hasDerivAt (b : Bool) (t : ℝ) :
    HasDerivAt (booleBranch b) (booleBranchDeriv b t) t := by
  have hs : HasDerivAt (fun t => Real.sqrt (t ^ 2 + 4)) (t / Real.sqrt (t ^ 2 + 4)) t := by
    have h1 : HasDerivAt (fun t : ℝ => t ^ 2 + 4) (2 * t) t := by
      simpa using (hasDerivAt_pow 2 t).add_const 4
    have := h1.sqrt (by positivity)
    convert this using 1
    field_simp
  unfold booleBranch booleBranchDeriv
  convert ((hasDerivAt_id t).add (hs.const_mul (if b then (1 : ℝ) else -1))).div_const 2 using 1
  simp

theorem booleBranchDeriv_nonneg (b : Bool) (t : ℝ) : 0 ≤ booleBranchDeriv b t := by
  unfold booleBranchDeriv
  have hpos := sqrt_pos_aux t
  have habs := abs_lt_sqrt_aux t
  have hq : |t / Real.sqrt (t ^ 2 + 4)| ≤ 1 := by
    rw [abs_div, abs_of_pos hpos, div_le_one hpos]
    exact habs.le
  cases b <;> simp <;> linarith [abs_le.mp hq]

theorem booleBranchDeriv_sum (t : ℝ) : ∑ b, booleBranchDeriv b t = 1 := by
  rw [Fintype.sum_bool]
  simp only [booleBranchDeriv, ↓reduceIte, Bool.false_eq_true]
  ring

theorem booleBranch_ne_zero (b : Bool) (t : ℝ) : booleBranch b t ≠ 0 := by
  unfold booleBranch
  have hpos := sqrt_pos_aux t
  have habs := abs_lt_sqrt_aux t
  cases b <;> simp <;> intro h <;> cases abs_lt.mp habs <;> linarith

theorem booleBranch_inv (b : Bool) (t : ℝ) :
    booleBranch b t - 1 / booleBranch b t = t := by
  have hne := booleBranch_ne_zero b t
  have hsq := sqrt_sq_aux t
  -- the branch is a root of r² - t r - 1 = 0
  have hroot : booleBranch b t ^ 2 - t * booleBranch b t - 1 = 0 := by
    unfold booleBranch
    cases b <;> simp <;> nlinarith [hsq]
  field_simp
  linarith

theorem booleBranch_true_pos (t : ℝ) : 0 < booleBranch true t := by
  unfold booleBranch
  have := abs_lt_sqrt_aux t
  simp
  cases abs_lt.mp this
  linarith

theorem booleBranch_false_neg (t : ℝ) : booleBranch false t < 0 := by
  unfold booleBranch
  have := abs_lt_sqrt_aux t
  simp
  cases abs_lt.mp this
  linarith

/-- Every nonzero real number is reached by the branch of its sign. -/
theorem booleBranch_surj {x : ℝ} (hx : x ≠ 0) :
    booleBranch (decide (0 < x)) (x - 1 / x) = x := by
  have hsqrt : Real.sqrt ((x - 1 / x) ^ 2 + 4) = |x + 1 / x| := by
    rw [← Real.sqrt_sq_eq_abs]
    congr 1
    field_simp
    ring
  unfold booleBranch
  rw [hsqrt]
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · have hs : x + 1 / x < 0 := by
      have : 1 / x < 0 := by rw [one_div]; exact inv_lt_zero.mpr hneg
      linarith
    rw [abs_of_neg hs]
    have hd : decide (0 < x) = false := decide_eq_false (not_lt.mpr hneg.le)
    rw [hd]
    simp only [Bool.false_eq_true, ↓reduceIte]
    ring
  · have hs : 0 < x + 1 / x := by positivity
    rw [abs_of_pos hs]
    have hd : decide (0 < x) = true := decide_eq_true hpos
    rw [hd]
    simp only [↓reduceIte]
    ring

/-- **Boole's theorem**: `∫ g (x - 1/x) dx = ∫ g x dx` for every integrable `g`. -/
theorem boole_integral (g : ℝ → ℝ) (hg : Integrable g) :
    ∫ x, g (x - 1 / x) = ∫ x, g x := by
  apply integral_comp_eq_of_branches (fun x => x - 1 / x) booleBranch booleBranchDeriv
    booleBranch_hasDerivAt booleBranchDeriv_nonneg booleBranch_inv
  · intro b c hbc
    rw [Function.onFun, Set.disjoint_left]
    rintro _ ⟨s, rfl⟩ ⟨t, ht⟩
    cases b <;> cases c
    · exact hbc rfl
    · have := booleBranch_false_neg s; have := booleBranch_true_pos t; linarith
    · have := booleBranch_true_pos s; have := booleBranch_false_neg t; linarith
    · exact hbc rfl
  · apply measure_mono_null (t := {0})
    · intro x hx
      by_contra h0
      apply hx
      exact mem_iUnion.mpr ⟨decide (0 < x), x - 1 / x, booleBranch_surj h0⟩
    · exact measure_singleton 0
  · exact booleBranchDeriv_sum
  · exact hg

end OrbitTrace

#print axioms OrbitTrace.integral_comp_eq_of_branches
#print axioms OrbitTrace.boole_integral
