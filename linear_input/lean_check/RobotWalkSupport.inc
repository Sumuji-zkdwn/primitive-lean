/-!
A nonempty nearest-neighbour heading walk cannot omit a whole periodic class
of edges while traversing all the translates of another edge. Two consecutive
missing lifted edges confine the walk to an interval shorter than the period.
-/

namespace LinearInputRobotWalkSupport

open LinearInputRobotWalkArc
open scoped BigOperators

/-- A walk starting between two missing edges never leaves those edges' interior. -/
theorem trapped_between_missing (w : List Bool) (j lo hi : ℤ)
    (hj : lo < j ∧ j ≤ hi) (hl : lo ∉ edges j w) (hh : hi ∉ edges j w) :
    ∀ e ∈ edges j w, lo < e ∧ e < hi := by
  induction w generalizing j with
  | nil => simp [edges]
  | cons b w ih =>
    cases b <;> simp only [edges, List.mem_cons, not_or] at hl hh ⊢
    · intro e he
      rcases he with rfl | he
      · omega
      · exact ih (j-1) (by omega) hl.2 hh.2 _ he
    · intro e he
      rcases he with rfl | he
      · omega
      · exact ih (j+1) (by omega) hl.2 hh.2 _ he

private def residue (N : ℕ) (e : ℤ) := (e % (N : ℤ)).toNat

private theorem cast_residue {N : ℕ} (hN : 0 < N) (e : ℤ) :
    (residue N e : ℤ) = e % (N : ℤ) :=
  Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hN.ne'))

private theorem residue_lt {N : ℕ} (hN : 0 < N) (e : ℤ) : residue N e < N := by
  have hb := Int.emod_lt_of_pos e (show 0 < (N : ℤ) by exact_mod_cast hN)
  rw [← cast_residue hN] at hb
  exact_mod_cast hb

private theorem reduce_residue (q d : ℕ) (hq : 0 < q) (hd : 0 < d) (e : ℤ) :
    residue (q*d) e % d = residue d e := by
  have hdvd : (d : ℤ) ∣ ((q*d : ℕ) : ℤ) := by
    exact_mod_cast (dvd_mul_left d q)
  have he : (((residue (q*d) e % d : ℕ) : ℤ)) = (residue d e : ℤ) := by
    rw [Int.natCast_emod, cast_residue (Nat.mul_pos hq hd), cast_residue hd,
      Int.emod_emod_of_dvd _ hdvd]
  exact_mod_cast he

private theorem lift_mem {q d a : ℕ} {w : List Bool}
    (h : 0 < (edgeResidues (q*d) 0 w).count a) :
    ∃ e ∈ edges 0 w, residue (q*d) e = a :=
  List.mem_map.mp (List.count_pos_iff.mp h)

/-- Periodic counts on a cycle of at least two periods have full support as soon
as the counts come from one nonempty walk. -/
theorem positive_counts {q d : ℕ} (hq : 2 ≤ q) (hd : 0 < d) {w : List Bool}
    (hw : w ≠ []) (hper : ∀ i < q*d, (edgeResidues (q*d) 0 w).count i =
      (edgeResidues (q*d) 0 w).count (i%d)) :
    ∀ i < q*d, 0 < (edgeResidues (q*d) 0 w).count i := by
  let c := fun i => (edgeResidues (q*d) 0 w).count i
  have hq0 : 0 < q := by omega
  have hN := Nat.mul_pos hq0 hd
  have hsize : d+d ≤ q*d := by
    simpa [two_mul] using Nat.mul_le_mul_right d hq
  have project (e : ℤ) (he : e ∈ edges 0 w) : 0 < c (residue (q*d) e) :=
    List.count_pos_iff.mpr (List.mem_map.mpr ⟨e, he, rfl⟩)
  intro i hi
  change 0 < c i
  by_contra hzero
  let r := i % d
  have hr : r < d := Nat.mod_lt _ hd
  have hmissing : c r = 0 := by
    have h := hper i hi
    change c i = c r at h
    omega
  have absent (e : ℤ) (he : e ∈ edges 0 w) : residue d e ≠ r := by
    intro her
    have hpos := project e he
    have hp := hper (residue (q*d) e) (residue_lt hN e)
    change c _ = c _ at hp
    rw [reduce_residue q d hq0 hd, her] at hp
    omega
  have hrr : residue d (r : ℤ) = r := by
    simp [residue, Int.emod_eq_of_lt (show 0 ≤ (r : ℤ) by positivity)
      (show (r : ℤ) < d by exact_mod_cast hr)]
  have hrr' : residue d ((r:ℤ)-d) = r := by
    simpa [residue, Int.sub_emod] using hrr
  have trapped := trapped_between_missing w 0 ((r:ℤ)-d) r (by omega)
    (fun he => absent _ he hrr') (fun he => absent _ he hrr)
  obtain ⟨e, he⟩ : ∃ e, e ∈ edges 0 w := by
    cases w with
    | nil => contradiction
    | cons b u => cases b <;> simp [edges]
  let s := residue (q*d) e % d
  have hs : s < d := Nat.mod_lt _ hd
  have hspos := project e he
  have hp := hper (residue (q*d) e) (residue_lt hN e)
  change c _ = c s at hp
  have hs2 : (s+d)%d = s := by simp [Nat.mod_eq_of_lt hs]
  have hp2 := hper (s+d) (by omega)
  change c (s+d) = c ((s+d)%d) at hp2
  rw [hs2] at hp2
  obtain ⟨x, hx, hxs⟩ := lift_mem (q := q) (d := d) (w := w) (a := s)
    (show 0 < c s by omega)
  obtain ⟨y, hy, hys⟩ := lift_mem (q := q) (d := d) (w := w) (a := s+d)
    (show 0 < c (s+d) by omega)
  have hxy : residue d x = residue d y := by
    rw [← reduce_residue q d hq0 hd, ← reduce_residue q d hq0 hd y, hxs, hys,
      hs2, Nat.mod_eq_of_lt hs]
  have hmod : x ≡ y [ZMOD (d : ℤ)] := by
    change x % (d : ℤ) = y % (d : ℤ)
    rw [← cast_residue hd, ← cast_residue hd y, hxy]
  have hh := (hmod.add_right ((d:ℤ)-r)).eq
  have bx := trapped x hx
  have by' := trapped y hy
  rw [Int.emod_eq_of_lt (by omega) (by omega),
    Int.emod_eq_of_lt (by omega) (by omega)] at hh
  have heq : x = y := by omega
  rw [heq, hys] at hxs
  omega

private theorem edges_length (j : ℤ) (w : List Bool) : (edges j w).length = w.length := by
  induction w generalizing j with
  | nil => rfl
  | cons b w ih => cases b <;> simp [edges, ih]

private theorem sum_periods (f : ℕ → ℕ) (q d : ℕ) :
    ∑ i ∈ Finset.range (q*d), f (i%d) = q * ∑ i ∈ Finset.range d, f i := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Nat.succ_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt (Finset.mem_range.mp hi)]

/-- A positive count of fixed parity is one or two plus an even surplus.
Sum one period of these counts and then repeat it `q` times. -/
theorem length_of_periodic_of_parity {q d : ℕ} (hq : 2 ≤ q) (hd : 0 < d) {w : List Bool}
    (hw : w ≠ []) (hper : ∀ i < q*d, (edgeResidues (q*d) 0 w).count i =
      (edgeResidues (q*d) 0 w).count (i%d))
    (hpar : ∀ i < q*d, (edgeResidues (q*d) 0 w).count i % 2 =
      (edgeResidues (q*d) 0 w).count 0 % 2) :
    ∃ t : ℕ, w.length = q*d + 2*q*t ∨ w.length = 2*(q*d) + 2*q*t := by
  let L := edgeResidues (q*d) 0 w
  let c := fun i => L.count i
  have hpos := positive_counts hq hd hw hper
  have hN : 0 < q*d := Nat.mul_pos (by omega) hd
  have hsize : d ≤ q*d := by simpa using Nat.mul_le_mul_right d (show 1 ≤ q by omega)
  have hset : L.toFinset = Finset.range (q*d) := by
    ext i
    simp only [List.mem_toFinset, Finset.mem_range]
    constructor
    · intro hi
      obtain ⟨e, _, rfl⟩ := List.mem_map.mp (show i ∈ edgeResidues (q*d) 0 w from hi)
      exact residue_lt hN e
    · intro hi
      exact List.count_pos_iff.mp (hpos i hi)
  have blockLength : w.length = q * ∑ i ∈ Finset.range d, c i := by
    calc
      w.length = L.length := by simp [L, edgeResidues, edges_length]
      _ = ∑ i ∈ L.toFinset, c i := (List.sum_toFinset_count_eq_length _).symm
      _ = ∑ i ∈ Finset.range (q*d), c (i%d) := by
        rw [hset]
        exact Finset.sum_congr rfl (fun i hi => hper i (Finset.mem_range.mp hi))
      _ = _ := sum_periods c q d
  let base := if c 0 % 2 = 0 then 2 else 1
  let t := ∑ i ∈ Finset.range d, (c i - base) / 2
  have localCount (i : ℕ) (hi : i ∈ Finset.range d) :
      c i = base + 2*((c i - base)/2) := by
    have hlt := lt_of_lt_of_le (Finset.mem_range.mp hi) hsize
    have h := hpar i hlt
    change c i % 2 = c 0 % 2 at h
    have hp : 0 < c i := hpos i hlt
    dsimp only [base]
    split <;> omega
  have periodLength : (∑ i ∈ Finset.range d, c i) = d*base + 2*t := by
    calc
      _ = ∑ i ∈ Finset.range d, (base + 2*((c i-base)/2)) := Finset.sum_congr rfl localCount
      _ = _ := by simp [Finset.sum_add_distrib, ← Finset.mul_sum, t]
  rw [periodLength] at blockLength
  refine ⟨t, ?_⟩
  by_cases h : c 0 % 2 = 0
  · right
    simpa [base, h, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using blockLength
  · left
    simpa [base, h, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using blockLength

end LinearInputRobotWalkSupport
