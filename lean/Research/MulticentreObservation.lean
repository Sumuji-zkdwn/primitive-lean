import Mathlib.Tactic

/-!
# Multiple gravitational centres and observer-dependent objects

A two-centre Gibbons--Hawking metric has harmonic potential
H = 1 + q/|x-a e_z| + q/|x+a e_z|.
It has the same leading far-field monopole term as a single centre
of charge 2q, but their higher multipoles differ.

Lean proves exact rational algebra, two explicit observer signatures,
and integer flux/Chern additivity. Smooth Ricci-flatness depends on the
standard Gibbons--Hawking theorem; the independent SymPy oracle checks
harmonicity and the connection equation but does not prove the theorem.
-/

namespace MulticentreObservation

/-- The two-centre harmonic function along the symmetry axis, r>a. -/
def twoAxis (q a r : ℚ) : ℚ :=
  1 + q / (r - a) + q / (r + a)

/-- A single exterior effective centre carrying twice the charge. -/
def oneAxis (q r : ℚ) : ℚ :=
  1 + 2 * q / r

/-- Clear all axis denominators: the remaining gap is a quadrupole. -/
theorem cleared_axis_gap (q a r : ℚ) :
    q * r * (r + a) + q * r * (r - a) -
      2 * q * (r - a) * (r + a) = 2 * q * a ^ 2 := by
  ring

/-- A finite exact witness that equal leading monopole charges do not
    make two-centre and one-centre observer readouts identical. -/
theorem axis_gap_example :
    twoAxis 1 1 3 - oneAxis 1 3 = 1 / 12 := by
  norm_num [twoAxis, oneAxis]

theorem axis_gap_nonzero : twoAxis 1 1 3 ≠ oneAxis 1 3 := by
  norm_num [twoAxis, oneAxis]

/-- The first surviving multipole for centres at +a and -a. -/
def axisQuadrupole (q a : ℚ) : ℚ := 2 * q * a ^ 2

/-- An equatorial observer sees the opposite-sign quadrupole. -/
def equatorQuadrupole (q a : ℚ) : ℚ := -q * a ^ 2

theorem quadrupole_relation (q a : ℚ) :
    axisQuadrupole q a = -2 * equatorQuadrupole q a := by
  unfold axisQuadrupole equatorQuadrupole
  ring

theorem quadrupole_even_in_separation (q a : ℚ) :
    axisQuadrupole q (-a) = axisQuadrupole q a := by
  unfold axisQuadrupole
  ring

theorem quadrupole_positive (q a : ℚ)
    (hq : 0 < q) (ha : a ≠ 0) :
    0 < axisQuadrupole q a := by
  have ha2 : 0 < a ^ 2 := sq_pos_of_ne_zero ha
  unfold axisQuadrupole
  exact mul_pos (mul_pos (by norm_num : (0 : ℚ) < 2) hq) ha2

/-- The 1/r coefficient at infinity does not encode centre separation. -/
def farMonopole (q a : ℚ) : ℚ := 2 * q

theorem monopole_blind_to_separation (q a b : ℚ) :
    farMonopole q a = farMonopole q b := rfl

/-- But the next multipole detects a concrete change of separation. -/
theorem first_vs_second_moment :
    farMonopole 1 1 = farMonopole 1 2 ∧
    axisQuadrupole 1 1 ≠ axisQuadrupole 1 2 := by
  norm_num [farMonopole, axisQuadrupole]

/-- Additive magnetic flux of N equal centres, modulo 4pi normalization. -/
def fluxUnits (n : ℕ) (q : ℚ) : ℚ :=
  -(n : ℚ) * q

theorem flux_additive (m n : ℕ) (q : ℚ) :
    fluxUnits (m + n) q = fluxUnits m q + fluxUnits n q := by
  simp [fluxUnits, Nat.cast_add]
  ring

/-- Chern number of the circle fibration, with a common 4pi*q period. -/
def firstChern (n : ℕ) : ℤ := -(n : ℤ)

theorem chern_additive (m n : ℕ) :
    firstChern (m + n) = firstChern m + firstChern n := by
  simp [firstChern, Nat.cast_add]
  ring

theorem one_and_two_centre_chern :
    firstChern 1 = -1 ∧ firstChern 2 = -2 := by
  norm_num [firstChern]

/-- Correct normalization: one center contributes one negative charge. -/
theorem local_chern_normalization (n : ℕ) :
    firstChern (n + 1) = firstChern n - 1 := by
  simp [firstChern, Nat.cast_add]
  ring

end MulticentreObservation
