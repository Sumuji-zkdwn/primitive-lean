import Elastica.WFSObservation

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

namespace LinearInputWFSObservation

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
    rcases Finset.mem_insert.mp hd with rfl | hd
    · apply (he m).1
      simp [sample, ZMod.natCast_self]
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
  (Finset.univ.filter (fun x : ZMod m => sampleKernel m ds x)).card

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
