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

* `exists_inverse_branch` constructs the inverse of a map with positive derivative
  from an open interval onto `ℝ` (through `StrictMono.orderIsoOfSurjective`) and
  differentiates it (`HasDerivAt.of_local_left_inverse`).
* `S3_integral` treats the three-branch map `S(x) = x + 1 - 1/x - 1/(x-1)` of
  section 1 (`m = 3`). Its branches on `(-∞,0)`, `(0,1)`, `(1,∞)` are obtained from
  the intermediate value theorem and `exists_inverse_branch`, without solving the
  cubic. They are three distinct roots of `X³ - tX² + (t-3)X + 1`, so they sum to
  `t` (`root_sum`); differentiating that identity gives `Σ r_i' = 1`.
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

/-! ## Inverse branches of an increasing map onto `ℝ` -/

/-- An increasing differentiable function from an open interval onto `ℝ` has a
differentiable inverse branch. -/
theorem exists_inverse_branch {I : Set ℝ} [OrdConnected I] (hI : IsOpen I)
    (f f' : ℝ → ℝ) (hf : ∀ x ∈ I, HasDerivAt f (f' x) x) (hpos : ∀ x ∈ I, 0 < f' x)
    (hsurj : ∀ t, ∃ x ∈ I, f x = t) :
    ∃ r : ℝ → ℝ, (∀ t, r t ∈ I) ∧ (∀ t, f (r t) = t) ∧ (∀ x ∈ I, r (f x) = x) ∧
      ∀ t, HasDerivAt r (f' (r t))⁻¹ t := by
  have hcont : ContinuousOn f I := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hmono : StrictMonoOn f I := by
    apply strictMonoOn_of_deriv_pos (Set.OrdConnected.convex ‹_›) hcont
    intro x hx
    rw [hI.interior_eq] at hx
    rw [(hf x hx).deriv]
    exact hpos x hx
  let g : I → ℝ := fun x => f x
  have gmono : StrictMono g := fun a b hab => hmono a.2 b.2 hab
  have gsurj : Function.Surjective g := fun t => by
    obtain ⟨x, hx, rfl⟩ := hsurj t
    exact ⟨⟨x, hx⟩, rfl⟩
  let e : I ≃o ℝ := StrictMono.orderIsoOfSurjective g gmono gsurj
  have he : ∀ x : I, e x = f x := fun x => rfl
  refine ⟨fun t => (e.symm t).1, fun t => (e.symm t).2, fun t => ?_, fun x hx => ?_, fun t => ?_⟩
  · have := e.apply_symm_apply t
    rw [he] at this
    exact this
  · have : e.symm (e ⟨x, hx⟩) = ⟨x, hx⟩ := e.symm_apply_apply _
    rw [he] at this
    exact congrArg Subtype.val this
  · have hrc : Continuous fun t => (e.symm t).1 := continuous_subtype_val.comp e.symm.continuous
    apply HasDerivAt.of_local_left_inverse hrc.continuousAt (hf _ (e.symm t).2)
      (hpos _ (e.symm t).2).ne'
    filter_upwards with y
    have := e.apply_symm_apply y
    rw [he] at this
    exact this

/-! ## The three-branch map of section 1 -/

/-- The map of section 1: `S(x) = x + 1 - 1/x - 1/(x-1) = (x³ - 3x + 1)/(x² - x)`. -/
noncomputable def S3 (x : ℝ) : ℝ := x + 1 - 1 / x - 1 / (x - 1)

/-- Its derivative `1 + 1/x² + 1/(x-1)²`. -/
noncomputable def S3deriv (x : ℝ) : ℝ := 1 + 1 / x ^ 2 + 1 / (x - 1) ^ 2

theorem S3deriv_pos (x : ℝ) : 0 < S3deriv x := by unfold S3deriv; positivity

theorem S3_hasDerivAt {x : ℝ} (h0 : x ≠ 0) (h1 : x ≠ 1) : HasDerivAt S3 (S3deriv x) x := by
  have h1' : x - 1 ≠ 0 := sub_ne_zero.mpr h1
  have ha : HasDerivAt (fun x : ℝ => 1 / x) (-(1 / x ^ 2)) x := by
    simpa [one_div] using hasDerivAt_inv h0
  have hb : HasDerivAt (fun x : ℝ => 1 / (x - 1)) (-(1 / (x - 1) ^ 2)) x := by
    have := (hasDerivAt_inv h1').comp x ((hasDerivAt_id x).sub_const 1)
    simpa [one_div, Function.comp_def] using this
  have := (((hasDerivAt_id x).add_const 1).sub ha).sub hb
  have hfun : S3 = ((fun x => id x + 1) - fun x => 1 / x) - fun x => 1 / (x - 1) := by
    funext y; simp [S3]
  have key : HasDerivAt S3 (1 - -(1 / x ^ 2) - -(1 / (x - 1) ^ 2)) x := by
    rw [hfun]; exact this
  unfold S3deriv
  convert key using 1
  ring

theorem S3_cubic {x t : ℝ} (h0 : x ≠ 0) (h1 : x ≠ 1) (h : S3 x = t) :
    x ^ 3 - t * x ^ 2 + (t - 3) * x + 1 = 0 := by
  have h1' : x - 1 ≠ 0 := sub_ne_zero.mpr h1
  unfold S3 at h
  rw [← h]
  field_simp
  ring

/-- Three distinct roots of `X³ - tX² + (t-3)X + 1` sum to `t`. -/
theorem root_sum {a b c t : ℝ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : a ^ 3 - t * a ^ 2 + (t - 3) * a + 1 = 0) (hb : b ^ 3 - t * b ^ 2 + (t - 3) * b + 1 = 0)
    (hc : c ^ 3 - t * c ^ 2 + (t - 3) * c + 1 = 0) : a + b + c = t := by
  have qab : a ^ 2 + a * b + b ^ 2 - t * (a + b) + (t - 3) = 0 := by
    have : (a - b) * (a ^ 2 + a * b + b ^ 2 - t * (a + b) + (t - 3)) = 0 := by
      linear_combination ha - hb
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hab)
  have qac : a ^ 2 + a * c + c ^ 2 - t * (a + c) + (t - 3) = 0 := by
    have : (a - c) * (a ^ 2 + a * c + c ^ 2 - t * (a + c) + (t - 3)) = 0 := by
      linear_combination ha - hc
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hac)
  have : (b - c) * (a + b + c - t) = 0 := by linear_combination qab - qac
  have := (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hbc)
  linarith

/-- Values of `S3` at the bounding points used for the intermediate value theorem. -/
theorem S3_bounds (M : ℝ) (hM : 4 ≤ M) :
    S3 (1 + 1 / M) < -M + 3 ∧ M - 1 < S3 M ∧ S3 (-M) < -M + 2 ∧ M < S3 (-1 / M) ∧
      S3 (1 / M) < -M + 3 ∧ M - 1 < S3 (1 - 1 / M) := by
  have hM0 : 0 < M := by linarith
  have i1 : 0 < 1 / M := by positivity
  have i2 : 1 / M ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hM
  unfold S3
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e : 1 / (1 + 1 / M - 1) = M := by field_simp; ring
    have : 0 < 1 / (1 + 1 / M) := by positivity
    rw [e]; linarith
  · have : 1 / (M - 1) ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  · have e1 : 1 / -M = -(1 / M) := by rw [div_neg]
    have e2 : 1 / (-M - 1) = -(1 / (M + 1)) := by rw [← div_neg]; ring_nf
    have : 1 / (M + 1) ≤ 1 / 5 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    rw [e1, e2]; linarith
  · have e1 : 1 / (-1 / M) = -M := by field_simp
    have e2 : 1 / (-1 / M - 1) = -(M / (M + 1)) := by
      have : -1 / M - 1 = -((M + 1) / M) := by field_simp; ring
      rw [this, one_div, inv_neg, inv_div]
    have : 0 ≤ M / (M + 1) := by positivity
    have e3 : -1 / M = -(1 / M) := by ring
    rw [e1, e2, e3]; linarith
  · have e1 : 1 / (1 / M) = M := by field_simp
    have e2 : 1 / (1 / M - 1) = -(M / (M - 1)) := by
      have : 1 / M - 1 = -((M - 1) / M) := by field_simp; ring
      rw [this, one_div, inv_neg, inv_div]
    have : M / (M - 1) ≤ 4 / 3 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    rw [e1, e2]; linarith
  · have e1 : 1 / (1 - 1 / M - 1) = -M := by field_simp; ring
    have e2 : 1 / (1 - 1 / M) = M / (M - 1) := by
      have : M - 1 ≠ 0 := by linarith
      field_simp
    have : M / (M - 1) ≤ 4 / 3 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    rw [e1, e2]; linarith

theorem S3_continuousOn_Icc {a b : ℝ} (h : ∀ x ∈ Icc a b, x ≠ 0 ∧ x ≠ 1) :
    ContinuousOn S3 (Icc a b) := fun x hx =>
  (S3_hasDerivAt (h x hx).1 (h x hx).2).continuousAt.continuousWithinAt

theorem S3_surj_Ioi (t : ℝ) : ∃ x ∈ Ioi (1 : ℝ), S3 x = t := by
  set M := |t| + 4 with hM
  have hM4 : 4 ≤ M := by have := abs_nonneg t; linarith
  obtain ⟨b1, b2, -, -, -, -⟩ := S3_bounds M hM4
  have hi : 1 / M ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hM4
  have hpos : 0 < 1 / M := by positivity
  obtain ⟨x, hx, hxt⟩ := intermediate_value_Icc (show 1 + 1 / M ≤ M by linarith)
    (S3_continuousOn_Icc fun x hx => ⟨by linarith [hx.1], by linarith [hx.1]⟩)
    (show t ∈ Icc (S3 (1 + 1 / M)) (S3 M) from
      ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩)
  exact ⟨x, by show 1 < x; linarith [hx.1], hxt⟩

theorem S3_surj_Iio (t : ℝ) : ∃ x ∈ Iio (0 : ℝ), S3 x = t := by
  set M := |t| + 4 with hM
  have hM4 : 4 ≤ M := by have := abs_nonneg t; linarith
  obtain ⟨-, -, b3, b4, -, -⟩ := S3_bounds M hM4
  have hpos : 0 < 1 / M := by positivity
  have e : -1 / M = -(1 / M) := by ring
  obtain ⟨x, hx, hxt⟩ := intermediate_value_Icc (show -M ≤ -1 / M by
      rw [e]; have : 1 / M ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hM4; linarith)
    (S3_continuousOn_Icc fun x hx => ⟨by have := hx.2; rw [e] at this; linarith,
      by have := hx.2; rw [e] at this; linarith⟩)
    (show t ∈ Icc (S3 (-M)) (S3 (-1 / M)) from
      ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩)
  exact ⟨x, by show x < 0; have := hx.2; rw [e] at this; linarith, hxt⟩

theorem S3_surj_Ioo (t : ℝ) : ∃ x ∈ Ioo (0 : ℝ) 1, S3 x = t := by
  set M := |t| + 4 with hM
  have hM4 : 4 ≤ M := by have := abs_nonneg t; linarith
  obtain ⟨-, -, -, -, b5, b6⟩ := S3_bounds M hM4
  have hi : 1 / M ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hM4
  have hpos : 0 < 1 / M := by positivity
  obtain ⟨x, hx, hxt⟩ := intermediate_value_Icc (show 1 / M ≤ 1 - 1 / M by linarith)
    (S3_continuousOn_Icc fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    (show t ∈ Icc (S3 (1 / M)) (S3 (1 - 1 / M)) from
      ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩)
  exact ⟨x, ⟨by linarith [hx.1], by linarith [hx.2]⟩, hxt⟩

/-- **Measure preservation for the map of section 1**:
`∫ g (x + 1 - 1/x - 1/(x - 1)) dx = ∫ g x dx` for every integrable `g`. -/
theorem S3_integral (g : ℝ → ℝ) (hg : Integrable g) : ∫ x, g (S3 x) = ∫ x, g x := by
  have hd : ∀ (I : Set ℝ), (∀ x ∈ I, x ≠ 0 ∧ x ≠ 1) → ∀ x ∈ I, HasDerivAt S3 (S3deriv x) x :=
    fun I hI x hx => S3_hasDerivAt (hI x hx).1 (hI x hx).2
  obtain ⟨r1, m1, i1, l1, d1⟩ := exists_inverse_branch (I := Iio (0 : ℝ)) isOpen_Iio S3 S3deriv
    (hd _ fun x hx => ⟨ne_of_lt hx, by have : x < 0 := hx; linarith⟩)
    (fun x _ => S3deriv_pos x) S3_surj_Iio
  obtain ⟨r2, m2, i2, l2, d2⟩ := exists_inverse_branch (I := Ioo (0 : ℝ) 1) isOpen_Ioo S3 S3deriv
    (hd _ fun x hx => ⟨ne_of_gt hx.1, ne_of_lt hx.2⟩)
    (fun x _ => S3deriv_pos x) S3_surj_Ioo
  obtain ⟨r3, m3, i3, l3, d3⟩ := exists_inverse_branch (I := Ioi (1 : ℝ)) isOpen_Ioi S3 S3deriv
    (hd _ fun x hx => ⟨by have : 1 < x := hx; linarith, ne_of_gt hx⟩)
    (fun x _ => S3deriv_pos x) S3_surj_Ioi
  -- the three branches sum to the identity (roots of the cubic)
  have hsum_eq : ∀ t, r1 t + r2 t + r3 t = t := by
    intro t
    have a1 : r1 t < 0 := m1 t
    have a2 := m2 t
    have a3 : 1 < r3 t := m3 t
    exact root_sum (by have := a2.1; linarith) (by linarith) (by have := a2.2; linarith)
      (S3_cubic (by linarith) (by linarith) (i1 t))
      (S3_cubic (by have := a2.1; linarith) (by have := a2.2; linarith) (i2 t))
      (S3_cubic (by linarith) (by linarith) (i3 t))
  have hsum : ∀ t, (S3deriv (r1 t))⁻¹ + (S3deriv (r2 t))⁻¹ + (S3deriv (r3 t))⁻¹ = 1 := by
    intro t
    have h := ((d1 t).add (d2 t)).add (d3 t)
    have hid : (fun t => r1 t + r2 t + r3 t) = id := funext hsum_eq
    have h' : HasDerivAt (fun t => r1 t + r2 t + r3 t)
        ((S3deriv (r1 t))⁻¹ + (S3deriv (r2 t))⁻¹ + (S3deriv (r3 t))⁻¹) t := h
    rw [hid] at h'
    exact h'.unique (hasDerivAt_id t)
  let r : Fin 3 → ℝ → ℝ := ![r1, r2, r3]
  have hmem : ∀ x, x ≠ 0 → x ≠ 1 → ∃ i, x ∈ range (r i) := by
    intro x h0 h1
    rcases lt_or_gt_of_ne h0 with hx | hx
    · exact ⟨0, S3 x, l1 x hx⟩
    · rcases lt_or_gt_of_ne h1 with hx' | hx'
      · exact ⟨1, S3 x, l2 x ⟨hx, hx'⟩⟩
      · exact ⟨2, S3 x, l3 x hx'⟩
  apply integral_comp_eq_of_branches S3 r (fun i t => (S3deriv (r i t))⁻¹)
  · intro i t; fin_cases i
    · exact d1 t
    · exact d2 t
    · exact d3 t
  · intro i t; exact (inv_pos.mpr (S3deriv_pos _)).le
  · intro i t; fin_cases i
    · exact i1 t
    · exact i2 t
    · exact i3 t
  · intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    rintro _ ⟨s, rfl⟩ ⟨u, hu⟩
    have b1 := m1 s; have b2 := m2 s; have b3 := m3 s
    have c1 := m1 u; have c2 := m2 u; have c3 := m3 u
    simp only [mem_Iio, mem_Ioo, mem_Ioi] at b1 b2 b3 c1 c2 c3
    fin_cases i <;> fin_cases j <;> simp [r] at hij hu <;> linarith [b2.1, b2.2, c2.1, c2.2]
  · apply measure_mono_null (t := {0, 1})
    · intro x hx
      by_contra hx01
      simp only [mem_insert_iff, mem_singleton_iff, not_or] at hx01
      obtain ⟨i, hi⟩ := hmem x hx01.1 hx01.2
      exact hx (mem_iUnion.mpr ⟨i, hi⟩)
    · exact (Set.toFinite _).measure_zero _
  · intro t
    rw [Fin.sum_univ_three]
    exact hsum t
  · exact hg

end OrbitTrace

#print axioms OrbitTrace.integral_comp_eq_of_branches
#print axioms OrbitTrace.boole_integral
#print axioms OrbitTrace.exists_inverse_branch
#print axioms OrbitTrace.S3_integral
