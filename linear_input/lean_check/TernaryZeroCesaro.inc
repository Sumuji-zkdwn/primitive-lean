/-!
Ternary placement and zero-insertion time averages.

Each length-three block contains one nonzero entry. Its residue r : Fin 3
specifies the position 3*k+r. Alternating +1,-1 gives a six-step cycle.
Zero deletion preserves a finite additive total, but need not preserve the
Cesaro average of partial sums. The general dwell-time identity is stated
for finite lists of (state value, number of time steps).

No infinite Cesaro convergence theorem, arbitrary sparse n_k decomposition,
or identification with F0 is claimed in this module.
-/

namespace LinearInputTernaryZero

/-- Put the event of block k in one of its three places. -/
def ternaryPosition (k : ℕ) (r : Fin 3) : ℕ := 3 * k + r.val

theorem ternary_position_mod (k : ℕ) (r : Fin 3) :
    ternaryPosition k r % 3 = r.val := by
  unfold ternaryPosition
  have hr := r.isLt
  omega

theorem ternary_position_increases (k : ℕ) (r s : Fin 3) :
    ternaryPosition k r < ternaryPosition (k + 1) s := by
  unfold ternaryPosition
  have hr := r.isLt
  have hs := s.isLt
  omega

theorem ternary_word_count (m : ℕ) :
    Fintype.card (Fin m → Fin 3) = 3 ^ m := by
  simp

/-- The three possibilities (a,0,0), (0,a,0), (0,0,a). -/
def ternaryBlock (r : Fin 3) (a : ℤ) : List ℤ :=
  (List.range 3).map (fun i => if i = r.val then a else 0)

theorem ternary_block_sum (r : Fin 3) (a : ℤ) :
    (ternaryBlock r a).sum = a := by
  fin_cases r <;> norm_num [ternaryBlock, List.range]

/-- Two blocks: +1 followed by -1; p and q independently choose phases. -/
def twoBlocks (p q : Fin 3) : List ℤ :=
  ternaryBlock p 1 ++ ternaryBlock q (-1)

/-- The six partial sums, accumulated without a preceding time-zero sample. -/
def sixNumerator (p q : Fin 3) : ℤ :=
  ((List.range 6).map (fun i => ((twoBlocks p q).take (i + 1)).sum)).sum

/-- Finite numerator of the six-step Cesaro average. -/
theorem six_numerator_formula (p q : Fin 3) :
    sixNumerator p q = (3 : ℤ) + (q.val : ℤ) - (p.val : ℤ) := by
  fin_cases p <;> fin_cases q <;> decide

/-- The arithmetic mean of the six successive partial sums. -/
def sixCesaro (p q : Fin 3) : ℚ :=
  (sixNumerator p q : ℚ) / 6

theorem six_cesaro_formula (p q : Fin 3) :
    sixCesaro p q = ((3 : ℚ) + (q.val : ℚ) - (p.val : ℚ)) / 6 := by
  rw [sixCesaro, six_numerator_formula]
  push_cast
  ring

/-- Exhaustive classification of the 3 by 3 phase table. -/
theorem six_cesaro_values (p q : Fin 3) :
    sixCesaro p q = (1 / 6 : ℚ) ∨
    sixCesaro p q = (1 / 3 : ℚ) ∨
    sixCesaro p q = (1 / 2 : ℚ) ∨
    sixCesaro p q = (2 / 3 : ℚ) ∨
    sixCesaro p q = (5 / 6 : ℚ) := by
  rw [six_cesaro_formula]
  fin_cases p <;> fin_cases q <;> norm_num

/-- All nine zero-padded blocks have the same ordered nonzero terms. -/
theorem two_blocks_nonzero (p q : Fin 3) :
    (twoBlocks p q).filter (fun x => x ≠ 0) = [1, -1] := by
  fin_cases p <;> fin_cases q <;> decide

/-- Same nonzero terms but different time averages. -/
theorem zero_placement_counterexample :
    (twoBlocks 0 2).filter (fun x => x ≠ 0) =
      (twoBlocks 2 0).filter (fun x => x ≠ 0) ∧
    sixCesaro 0 2 = (5 / 6 : ℚ) ∧
    sixCesaro 2 0 = (1 / 6 : ℚ) := by
  constructor
  · rw [two_blocks_nonzero, two_blocks_nonzero]
  constructor <;> rw [six_cesaro_formula] <;> norm_num

/-- Removing literal zero entries never changes the finite additive sum. -/
theorem filter_nonzero_preserves_sum (xs : List ℤ) :
    (xs.filter (fun x => x ≠ 0)).sum = xs.sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.filter_cons]
      split_ifs with hx
      · simpa only [List.sum_cons, ih]
      · have hzero : x = 0 := by simpa using hx
        subst x
        simpa only [List.sum_cons, zero_add] using ih

/-- Repeat a partial-sum state for its actual number of time slots. -/
def dwellExpand (blocks : List (ℤ × ℕ)) : List ℤ :=
  blocks.flatMap (fun b => List.replicate b.2 b.1)

theorem repeat_sum (v : ℤ) (d : ℕ) :
    (List.replicate d v).sum = (d : ℤ) * v := by
  induction d with
  | zero => simp
  | succ d ih =>
      simp [List.replicate, ih, Nat.cast_succ, add_mul, add_comm]

/-- General exact identity: time-integrated sums are occupancy-weighted. -/
theorem dwell_occupation_identity (blocks : List (ℤ × ℕ)) :
    (dwellExpand blocks).sum =
      (blocks.map (fun b => (b.2 : ℤ) * b.1)).sum := by
  induction blocks with
  | nil => rfl
  | cons b bs ih =>
      rcases b with ⟨v, d⟩
      change (List.replicate d v ++ dwellExpand bs).sum =
        (d : ℤ) * v + (bs.map (fun b => (b.2 : ℤ) * b.1)).sum
      rw [List.sum_append, repeat_sum, ih]

end LinearInputTernaryZero
