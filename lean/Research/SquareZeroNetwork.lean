import Mathlib.Tactic

/-!
# Square-zero local rules and growing global reachability

Each nonloop edge is a square-zero endomorphism of integer-valued vertex
states. Composition follows matching endpoints. A two-edge cycle can amplify
one trajectory, whereas the *sum* of unit-weight edge maps on the complete
three-vertex digraph doubles the number of weighted histories at every step.

These are algebraic identities, not physical energy amplification. The
exponential in the second model counts distinct paths; it does not represent
exponential growth along any individual unit-weight path.
-/

namespace SquareZeroNetwork

abbrev Vec (n : ℕ) := Fin n → ℤ

/-- Rank-one weighted transfer along the directed edge src -> dst. -/
def edge {n : ℕ} (src dst : Fin n) (w : ℤ) (v : Vec n) : Vec n :=
  fun j => if j = dst then w * v src else 0

/-- Any nonloop edge destroys its own image on a second application. -/
theorem edge_square_zero {n : ℕ} (src dst : Fin n)
    (h : src ≠ dst) (w : ℤ) (v : Vec n) :
    edge src dst w (edge src dst w v) = (fun _ => 0) := by
  funext j
  by_cases hj : j = dst <;> simp [edge, hj, h]

/-- Matched transfers concatenate as a single weighted edge. -/
theorem edge_comp_match {n : ℕ} (a b c : Fin n) (p q : ℤ) (v : Vec n) :
    edge b c q (edge a b p v) = edge a c (q * p) v := by
  funext j
  by_cases hj : j = c <;> simp [edge, hj, mul_assoc]

/-- Mismatched endpoints make the composition identically zero. -/
theorem edge_comp_mismatch {n : ℕ} (a b c d : Fin n)
    (h : b ≠ c) (p q : ℤ) (v : Vec n) :
    edge c d q (edge a b p v) = (fun _ => 0) := by
  funext j
  by_cases hj : j = d <;> simp [edge, hj, h.symm]

/-- One two-edge round trip, performed k times. -/
def cycle2 (a b : ℤ) : ℕ → Vec 2 → Vec 2
  | 0, v => v
  | k + 1, v =>
      edge (1 : Fin 2) 0 b (edge (0 : Fin 2) 1 a (cycle2 a b k v))

/-- The initially occupied first vertex. -/
def source2 : Vec 2 := fun j => if j = 0 then 1 else 0

/-- Exact gain of a two-edge cycle, without imposing any sign assumption. -/
theorem cycle2_closed (a b : ℤ) (k : ℕ) :
    cycle2 a b k source2 =
      (fun j => if j = 0 then (a * b) ^ k else 0) := by
  induction k with
  | zero =>
      funext j
      simp [cycle2, source2]
  | succ k ih =>
      funext j
      fin_cases j
      · simp [cycle2, edge, ih, pow_succ]
        ring
      · simp [cycle2, edge]

/-- The example with gain 2 on each edge grows by a factor 4 per round. -/
theorem alternating_two_step_gain (k : ℕ) :
    cycle2 2 2 k source2 =
      (fun j => if j = 0 then (4 : ℤ) ^ k else 0) := by
  simpa using (cycle2_closed 2 2 k)

/-- Unit-weight aggregate of all six nonloop edges of the 3-vertex graph. -/
def edgeSum3 (v : Vec 3) : Vec 3 :=
  fun j =>
    edge 0 1 1 v j + edge 0 2 1 v j +
    edge 1 0 1 v j + edge 1 2 1 v j +
    edge 2 0 1 v j + edge 2 1 1 v j

/-- A vertex receives the sum of the other two vertex values. -/
def scatter3 (v : Vec 3) : Vec 3 :=
  fun j => if j = 0 then v 1 + v 2
    else if j = 1 then v 0 + v 2 else v 0 + v 1

/-- The aggregate map is literally the sum of square-zero edge maps. -/
theorem scatter3_eq_edges (v : Vec 3) : scatter3 v = edgeSum3 v := by
  funext j
  fin_cases j <;> simp [scatter3, edgeSum3, edge]

/-- Total coefficient, interpreted as a count only for nonnegative inputs. -/
def mass3 (v : Vec 3) : ℤ := v 0 + v 1 + v 2

/-- Aggregate transport doubles total weight, including signed inputs. -/
theorem scatter3_mass (v : Vec 3) :
    mass3 (scatter3 v) = 2 * mass3 v := by
  simp [mass3, scatter3]
  ring

/-- Repeated simultaneous aggregate transfer. -/
def iterateScatter3 : ℕ → Vec 3 → Vec 3
  | 0, v => v
  | k + 1, v => scatter3 (iterateScatter3 k v)

/-- A global exponential from adding unit-weight square-zero rules. -/
theorem iterate_mass (k : ℕ) (v : Vec 3) :
    mass3 (iterateScatter3 k v) = (2 : ℤ) ^ k * mass3 v := by
  induction k with
  | zero => simp [iterateScatter3]
  | succ k ih =>
      calc
        mass3 (iterateScatter3 (k + 1) v)
            = 2 * mass3 (iterateScatter3 k v) := by
                simpa [iterateScatter3] using
                  (scatter3_mass (iterateScatter3 k v))
        _ = 2 * ((2 : ℤ) ^ k * mass3 v) := by rw [ih]
        _ = (2 : ℤ) ^ (k + 1) * mass3 v := by rw [pow_succ]; ring

/-- One occupied vertex yields all length-k walks from that vertex. -/
def source3 : Vec 3 := fun j => if j = 0 then 1 else 0

/-- Symmetry of the two other endpoints is preserved at every step. -/
theorem iterate_symmetry (k : ℕ) :
    iterateScatter3 k source3 1 = iterateScatter3 k source3 2 := by
  induction k with
  | zero => simp [iterateScatter3, source3]
  | succ k ih =>
      change scatter3 (iterateScatter3 k source3) 1 =
        scatter3 (iterateScatter3 k source3) 2
      simp [scatter3, ih]

/-- The distinction between source and another vertex changes sign. -/
theorem scatter3_difference (v : Vec 3) :
    scatter3 v 0 - scatter3 v 1 = -(v 0 - v 1) := by
  simp [scatter3]

/-- A hidden parity trace survives inside exponentially many histories. -/
theorem iterate_difference (k : ℕ) :
    iterateScatter3 k source3 0 - iterateScatter3 k source3 1 =
      (-1 : ℤ) ^ k := by
  induction k with
  | zero => norm_num [iterateScatter3, source3]
  | succ k ih =>
      change scatter3 (iterateScatter3 k source3) 0 -
        scatter3 (iterateScatter3 k source3) 1 = _
      rw [scatter3_difference, ih, pow_succ]
      ring

/-- Exact endpoint-history profile, stated without integer division. -/
theorem endpoint_profile (k : ℕ) :
    (3 : ℤ) * iterateScatter3 k source3 0 =
        (2 : ℤ) ^ k + 2 * (-1 : ℤ) ^ k ∧
    (3 : ℤ) * iterateScatter3 k source3 1 =
        (2 : ℤ) ^ k - (-1 : ℤ) ^ k ∧
    (3 : ℤ) * iterateScatter3 k source3 2 =
        (2 : ℤ) ^ k - (-1 : ℤ) ^ k := by
  have hm := iterate_mass k source3
  have hs := iterate_symmetry k
  have hd := iterate_difference k
  have hv : mass3 source3 = 1 := by norm_num [mass3, source3]
  rw [hv] at hm
  simp only [mul_one, mass3] at hm
  constructor
  · linarith
  constructor
  · linarith
  · linarith

end SquareZeroNetwork
