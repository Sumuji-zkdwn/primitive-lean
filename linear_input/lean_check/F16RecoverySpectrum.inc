/-!
# F16: one-probe recovery and the signed two-dimensional blocks

A follow-up to LinearInputF16Holonomy. The 256-entry integer epsilon matrix
is inherited from the user-provided sedenion Cayley-Dickson convention.

The first group establishes that a single obstructed probe recovers exactly
the high bit discarded by the F0 observation. The second group extracts the
eight 2-by-2 blocks of L_(e3+t e10) and explicit null vectors at t = +1,-1.

The signed block determinant formula is NOT presented as a proof of the
determinant or the full spectrum of the 16-by-16 operator: that additionally
needs a proof of the row/column permutation decomposition.
-/

noncomputable section

namespace LinearInputF16Recovery

open LinearInputF16Holonomy

abbrev SignedBasis := Bool × Fin 16

/-- Two observations: current F0 state and that after one right probe. -/
def pairedObservation (b : Fin 16) (s : SignedBasis) : SignedBasis × SignedBasis :=
  (forgetSigned s, observedRight b s)

/-- Restore the discarded high bit as needed. -/
def highIndex (a : Fin 16) : Fin 16 :=
  ⟨a.val % 8 + 8, by
    have hm : a.val % 8 < 8 := Nat.mod_lt _ (by decide)
    omega⟩

/-- A constructive inverse of the two-observation code for obstructed probes.
The test compares the second observation against the canonical low-bit lift. -/
def decodeProbe (b : Fin 16) (p : SignedBasis × SignedBasis) : SignedBasis :=
  if observedRight b p.1 = p.2 then p.1
  else (p.1.1, highIndex p.1.2)

/-- The eight non-descending probes restore *every* one of the 32 signed states. -/
theorem decodeProbe_exact (b : Fin 16) :
    (1 ≤ b.val ∧ b.val ≤ 8) →
      ∀ s : SignedBasis, decodeProbe b (pairedObservation b s) = s := by
  fin_cases b <;> decide

theorem pairedObservation_injective_bad (b : Fin 16)
    (hb : 1 ≤ b.val ∧ b.val ≤ 8) :
    Function.Injective (pairedObservation b) := by
  intro s t h
  have he := congrArg (decodeProbe b) h
  rw [decodeProbe_exact b hb s, decodeProbe_exact b hb t] at he
  exact he

/-- The other eight probes fail to distinguish e0 from e8. -/
theorem pairedObservation_good_collision (b : Fin 16) :
    (b.val = 0 ∨ 9 ≤ b.val) →
      pairedObservation b (true, (0 : Fin 16)) =
        pairedObservation b (true, (8 : Fin 16)) := by
  fin_cases b <;> decide

theorem pairedObservation_injective_iff (b : Fin 16) :
    Function.Injective (pairedObservation b) ↔
      1 ≤ b.val ∧ b.val ≤ 8 := by
  constructor
  · intro h
    by_contra hb
    have hgood : b.val = 0 ∨ 9 ≤ b.val := by
      have hlt := b.isLt
      omega
    have he := h (pairedObservation_good_collision b hgood)
    have hne : (true, (0 : Fin 16)) ≠ (true, (8 : Fin 16)) := by decide
    exact hne he
  · exact pairedObservation_injective_bad b

/-- Concrete F0 forgetting counterexample with a single probe e1. -/
theorem forgotten_bit_reappears :
    forgetSigned (true, (0 : Fin 16)) =
      forgetSigned (true, (8 : Fin 16)) ∧
    observedRight (1 : Fin 16) (true, (0 : Fin 16)) ≠
      observedRight (1 : Fin 16) (true, (8 : Fin 16)) := by
  decide

/-- The partner of a low basis index within a signed 2x2 block. -/
def partnerIndex (a : Fin 8) : Fin 16 :=
  ⟨(Nat.xor a.val 9) % 16, Nat.mod_lt _ (by decide)⟩

/-- Column indices under e3 and e10 are swapped within each block. -/
theorem block_index_swap (a : Fin 8) :
    rightIndex (3 : Fin 16) (low a) =
      rightIndex (10 : Fin 16) (partnerIndex a) ∧
    rightIndex (10 : Fin 16) (low a) =
      rightIndex (3 : Fin 16) (partnerIndex a) := by
  fin_cases a <;> decide

/-- The two coefficient products in each signed 2x2 block. -/
theorem block_coefficients (a : Fin 8) :
    eps (3 : Fin 16) (low a) * eps (3 : Fin 16) (partnerIndex a) =
      (if a.val = 0 ∨ a.val = 3 then -1 else 1) ∧
    eps (10 : Fin 16) (low a) * eps (10 : Fin 16) (partnerIndex a) =
      (if a.val < 4 then
         (if a.val = 0 ∨ a.val = 3 then 1 else -1)
       else 1) := by
  fin_cases a <;> decide

/-- Signed determinant in the actual 2x2 block, before reordering rows. -/
def blockDet (a : Fin 8) (t : ℤ) : ℤ :=
  eps (3 : Fin 16) (low a) * eps (3 : Fin 16) (partnerIndex a) -
    (eps (10 : Fin 16) (low a) * eps (10 : Fin 16) (partnerIndex a)) * t ^ 2

/-- Four blocks are +/- (1+t²); four are (1-t²). -/
theorem blockDet_formula (a : Fin 8) (t : ℤ) :
    blockDet a t =
      (if a.val < 4 then
        (if a.val = 0 ∨ a.val = 3 then -(1 + t ^ 2) else (1 + t ^ 2))
       else 1 - t ^ 2) := by
  obtain ⟨ha, hb⟩ := block_coefficients a
  unfold blockDet
  rw [ha, hb]
  by_cases hlow : a.val < 4
  · by_cases h03 : a.val = 0 ∨ a.val = 3
    · simp [hlow, h03]
      ring
    · simp [hlow, h03]
      ring
  · have h03 : ¬(a.val = 0 ∨ a.val = 3) := by omega
    simp [hlow, h03]
    ring

/-- The four blocks with indices 4..7 become singular exactly at t = +/-1
when t is an integer. -/
theorem blockDet_at_plus_one (a : Fin 8) :
    blockDet a 1 = 0 ↔ 4 ≤ a.val := by
  fin_cases a <;> decide

theorem blockDet_at_minus_one (a : Fin 8) :
    blockDet a (-1) = 0 ↔ 4 ≤ a.val := by
  fin_cases a <;> decide

/-- Left multiplication on integer coefficient vectors by a single basis unit. -/
def leftBasis (i : Fin 16) (v : Fin 16 → ℤ) (k : Fin 16) : ℤ :=
  ∑ j : Fin 16,
    if rightIndex i j = k then eps i j * v j else 0

/-- The integer pencil L_(e3 + t e10), acting on a 16-dimensional vector. -/
def leftPencil (t : ℤ) (v : Fin 16 → ℤ) : Fin 16 → ℤ :=
  fun k => leftBasis (3 : Fin 16) v k + t * leftBasis (10 : Fin 16) v k

/-- Each of the four source supports uses the low index 4..7. -/
def pivotIndex (a : Fin 4) : Fin 16 :=
  ⟨a.val + 4, by have h := a.isLt; omega⟩

def kernelSign (plus : Bool) (a : Fin 4) : ℤ :=
  if a.val = 0 ∨ a.val = 3 then (if plus then 1 else -1)
  else (if plus then -1 else 1)

/-- Four disjointly supported candidate kernel vectors at either t = 1 or -1. -/
def kernelVector (plus : Bool) (a : Fin 4) (j : Fin 16) : ℤ :=
  if j = pivotIndex a then 1
  else if j.val = Nat.xor (a.val + 4) 9 then kernelSign plus a
  else 0

/-- Recover each coefficient from its own pivot coordinate. -/
theorem kernelVector_coordinates (plus : Bool) (a b : Fin 4) :
    kernelVector plus a (pivotIndex b) = if a = b then 1 else 0 := by
  cases plus <;> fin_cases a <;> fin_cases b <;> decide

/-- Four explicit kernel vectors for t = +1. The third is e6 - e15. -/
theorem kernel_plus (a : Fin 4) (k : Fin 16) :
    leftPencil 1 (kernelVector true a) k = 0 := by
  fin_cases a <;> fin_cases k <;> decide

/-- Four explicit kernel vectors for t = -1. -/
theorem kernel_minus (a : Fin 4) (k : Fin 16) :
    leftPencil (-1) (kernelVector false a) k = 0 := by
  fin_cases a <;> fin_cases k <;> decide

/-- A concrete signed-basis zero divisor from the user's source file. -/
theorem e3_plus_e10_zero_divisor :
    leftPencil 1 (fun j : Fin 16 =>
      if j = 6 then 1 else if j = 15 then -1 else 0) =
        (fun _ => 0) := by
  funext k
  fin_cases k <;> decide

end LinearInputF16Recovery
