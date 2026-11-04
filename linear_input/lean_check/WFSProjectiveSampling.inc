/-!
PR #21 adapter for the established supplemental joint checker.
Original sources are preserved in sources/wfs_projective_pr21_20261101/.
Imports are supplied by All.lean, and the two repeated namespace blocks are
assembled as one.  The gcd proof retains m by substituting d explicitly.
-/

namespace LinearInputWFSObservation

/-!
# WFS projective lift and sampled cyclic observations

This file is a standalone, additive model; it does not infer a WFS
response law from the primitive elastica energy.  The lift is on
homogeneous coordinate pairs, not a constructed projective quotient.
Its invertibility ensures that it descends to the projective line.

For the sampling theorem, x is an unknown *rotation increment* in the
fully observed cyclic group ZMod m (m > 0); it is not the current phase of
a trajectory. Additional non-injective sensors need separate hypotheses.
-/


/-- Lift of z ↦ -z / (1 + 2*z) to homogeneous coordinate pairs [X:Y]. -/
def wfsLift (p : ℝ × ℝ) : ℝ × ℝ :=
  (-p.1, 2 * p.1 + p.2)

/-- Gauge C: [X:Y] ↦ [X:X+Y], corresponding to w = z/(1+z). -/
def gauge (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1, p.1 + p.2)

def gaugeInv (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1, p.2 - p.1)

/-- The normal form is a reflection, not a general nonlinear map. -/
def reflection (p : ℝ × ℝ) : ℝ × ℝ :=
  (-p.1, p.2)

theorem gaugeInv_gauge (p : ℝ × ℝ) :
    gaugeInv (gauge p) = p := by
  rcases p with ⟨x, y⟩
  apply Prod.ext
  · rfl
  · change x + y - x = y
    ring

theorem gauge_gaugeInv (p : ℝ × ℝ) :
    gauge (gaugeInv p) = p := by
  rcases p with ⟨x, y⟩
  apply Prod.ext
  · rfl
  · change x + (y - x) = y
    ring

/-- Exact conjugacy of the homogeneous linear maps: C ∘ T = R ∘ C. -/
theorem gauge_wfsLift (p : ℝ × ℝ) :
    gauge (wfsLift p) = reflection (gauge p) := by
  rcases p with ⟨x, y⟩
  apply Prod.ext
  · rfl
  · change -x + (2 * x + y) = x + y
    ring

theorem wfsLift_involutive : Function.Involutive wfsLift := by
  intro p
  rcases p with ⟨x, y⟩
  apply Prod.ext
  · change -(-x) = x
    ring
  · change 2 * (-x) + (2 * x + y) = y
    ring

theorem reflection_involutive : Function.Involutive reflection := by
  intro p
  rcases p with ⟨x, y⟩
  apply Prod.ext
  · change -(-x) = x
    ring
  · rfl

/-- Sampling a cyclic rotation d steps at a time: x ↦ d*x (mod m). -/
def sample (m d : ℕ) (x : ZMod m) : ZMod m :=
  (d : ZMod m) * x

/--
For a positive period m, d-step sampling is injective precisely when
d and m are coprime.  The positivity hypothesis matters: ZMod 0 is
the infinite cyclic group, where x ↦ 2*x is injective.
-/
theorem sample_injective_iff_coprime (m d : ℕ) (hm : 0 < m) :
    Function.Injective (sample m d) ↔ Nat.Coprime d m := by
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  constructor
  · intro hinj
    have hsurj : Function.Surjective (sample m d) :=
      Finite.surjective_of_injective hinj
    obtain ⟨x, hx⟩ := hsurj 1
    have hu : IsUnit (d : ZMod m) := by
      apply IsUnit.of_mul_eq_one x
      simpa [sample] using hx
    exact (ZMod.isUnit_iff_coprime d m).mp hu
  · intro hcop x y hxy
    have hleft : (d : ZMod m)⁻¹ * (d : ZMod m) = 1 := by
      calc
        _ = (d : ZMod m) * (d : ZMod m)⁻¹ := mul_comm _ _
        _ = 1 := ZMod.coe_mul_inv_eq_one d hcop
    have h := congrArg (fun z : ZMod m => (d : ZMod m)⁻¹ * z) hxy
    simpa only [sample, ← mul_assoc, hleft, one_mul] using h

/-- A four-state clockwise/counterclockwise ambiguity at two-step sampling. -/
theorem four_state_two_step_alias :
    sample 4 2 (1 : ZMod 4) = sample 4 2 (3 : ZMod 4) := by
  decide

theorem four_state_one_step_separates :
    sample 4 1 (1 : ZMod 4) ≠ sample 4 1 (3 : ZMod 4) := by
  decide

def samplePair (m d e : ℕ) (x : ZMod m) : ZMod m × ZMod m :=
  (sample m d x, sample m e x)

/-- Two individually lossy samplers jointly identify every six-state rotation increment. -/
theorem six_state_two_three_joint_injective :
    Function.Injective (samplePair 6 2 3) := by
  decide



/-!
# Sampling kernels and observation pseudodistances

These statements concern an unknown rotation increment in ZMod m.
A finite set of observation times is assumed, with full access to each
sampled residue.  They are not claims about the physical WFS law,
about an arbitrary non-injective sensor, or about spatial distance.

The exact general cardinality formula for the kernel is proved in the
companion mathematical note; below we formalize the general gcd-based
*kernel characterization*, the distance axioms, and two finite counts.
The general cardinality formula is not claimed as Lean-verified.
-/


/-- A sampling kernel: all rotation increments killed at every observation time. -/
def sampleKernel (m : ℕ) (ds : Finset ℕ) (x : ZMod m) : Prop :=
  ∀ d ∈ ds, sample m d x = 0

/-- Include the period m in the gcd to take the quotient modulus into account. -/
def observationGCD (m : ℕ) (ds : Finset ℕ) : ℕ :=
  (insert m ds).gcd id

theorem sample_zero_iff_order_dvd (m d : ℕ) (x : ZMod m) :
    sample m d x = 0 ↔ addOrderOf x ∣ d := by
  unfold sample
  rw [← nsmul_eq_mul]
  exact (addOrderOf_dvd_iff_nsmul_eq_zero).symm

/-- All samples vanish precisely when the single gcd sample vanishes. -/
theorem sampleKernel_iff_gcd_zero (m : ℕ) (ds : Finset ℕ) (x : ZMod m) :
    sampleKernel m ds x ↔ sample m (observationGCD m ds) x = 0 := by
  have he (d : ℕ) : sample m d x = 0 ↔ addOrderOf x ∣ d :=
    sample_zero_iff_order_dvd m d x
  constructor
  · intro h
    apply (he (observationGCD m ds)).2
    change addOrderOf x ∣ (insert m ds).gcd id
    apply (Finset.dvd_gcd_iff).2
    intro d hd
    rcases Finset.mem_insert.mp hd with hdm | hd
    · subst d
      apply (he m).1
      simp [sample]
    · exact (he d).1 (h d hd)
  · intro h d hd
    apply (he d).2
    have hg : addOrderOf x ∣ (insert m ds).gcd id :=
      (he (observationGCD m ds)).1 h
    have hall : ∀ k ∈ insert m ds, addOrderOf x ∣ k :=
      (Finset.dvd_gcd_iff).1 hg
    exact hall d (Finset.mem_insert_of_mem hd)

/-- Number of elements in the finite cyclic sampling kernel. -/
def sampleKernelCard (m : ℕ) [NeZero m] (ds : Finset ℕ) : ℕ :=
  (Finset.univ.filter (fun x : ZMod m =>
    (ds.filter (fun d => sample m d x ≠ 0)).card = 0)).card

/-- Two samples together eliminate the kernel in the six-state example. -/
theorem sampleKernelCard_six_two_three :
    sampleKernelCard 6 ({2, 3} : Finset ℕ) = 1 := by
  decide

/-- The pair of samples 2 and 4 has a two-element kernel modulo 8. -/
theorem sampleKernelCard_eight_two_four :
    sampleKernelCard 8 ({2, 4} : Finset ℕ) = 2 := by
  decide

/-- The discrete 0/1 distance between two symbols. -/
def mismatch {α : Type*} [DecidableEq α] (a b : α) : ℕ :=
  if a = b then 0 else 1

theorem mismatch_self {α : Type*} [DecidableEq α] (a : α) :
    mismatch a a = 0 := by simp [mismatch]

theorem mismatch_symm {α : Type*} [DecidableEq α] (a b : α) :
    mismatch a b = mismatch b a := by
  by_cases h : a = b
  · subst b
    rfl
  · have h' : b ≠ a := Ne.symm h
    simp [mismatch, h, h']

theorem mismatch_triangle {α : Type*} [DecidableEq α] (a b c : α) :
    mismatch a c ≤ mismatch a b + mismatch b c := by
  by_cases hab : a = b
  · subst b
    simp [mismatch]
  · by_cases hbc : b = c
    · subst c
      simp [mismatch]
    · by_cases hac : a = c
      · subst c
        simp [mismatch]
      · simp [mismatch, hab, hbc, hac]

/-- Count the observation times at which two candidate increments differ. -/
def observationDistance (m : ℕ) (ds : Finset ℕ)
    (x y : ZMod m) : ℕ :=
  ds.sum (fun d => mismatch (sample m d x) (sample m d y))

theorem observationDistance_self (m : ℕ) (ds : Finset ℕ) (x : ZMod m) :
    observationDistance m ds x x = 0 := by
  simp [observationDistance, mismatch]

theorem observationDistance_symm (m : ℕ) (ds : Finset ℕ) (x y : ZMod m) :
    observationDistance m ds x y = observationDistance m ds y x := by
  unfold observationDistance
  apply Finset.sum_congr rfl
  intro d _
  exact mismatch_symm _ _

theorem observationDistance_triangle (m : ℕ) (ds : Finset ℕ)
    (x y z : ZMod m) :
    observationDistance m ds x z ≤
      observationDistance m ds x y + observationDistance m ds y z := by
  unfold observationDistance
  calc
    ds.sum (fun d => mismatch (sample m d x) (sample m d z))
        ≤ ds.sum (fun d => mismatch (sample m d x) (sample m d y) +
             mismatch (sample m d y) (sample m d z)) := by
          apply Finset.sum_le_sum
          intro d _
          exact mismatch_triangle _ _ _
    _ = ds.sum (fun d => mismatch (sample m d x) (sample m d y)) +
          ds.sum (fun d => mismatch (sample m d y) (sample m d z)) := by
          rw [Finset.sum_add_distrib]

theorem mismatch_eq_zero_iff {α : Type*} [DecidableEq α] (a b : α) :
    mismatch a b = 0 ↔ a = b := by
  by_cases h : a = b <;> simp [mismatch, h]

theorem observationDistance_zero_iff (m : ℕ) (ds : Finset ℕ)
    (x y : ZMod m) :
    observationDistance m ds x y = 0 ↔
      ∀ d ∈ ds, sample m d x = sample m d y := by
  unfold observationDistance
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun d hd => Nat.zero_le _)]
  simp only [mismatch_eq_zero_iff]

/-- The zero-distance equivalence classes are precisely kernel cosets. -/
theorem observationDistance_zero_iff_kernel (m : ℕ) (ds : Finset ℕ)
    (x y : ZMod m) :
    observationDistance m ds x y = 0 ↔ sampleKernel m ds (x - y) := by
  rw [observationDistance_zero_iff]
  constructor
  · intro h d hd
    change (d : ZMod m) * (x - y) = 0
    rw [mul_sub, sub_eq_zero]
    exact h d hd
  · intro h d hd
    have hz : (d : ZMod m) * (x - y) = 0 := h d hd
    rw [mul_sub, sub_eq_zero] at hz
    exact hz


end LinearInputWFSObservation
