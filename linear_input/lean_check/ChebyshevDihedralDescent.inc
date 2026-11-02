/-!
# Generic Chebyshev radical certificates for the dihedral descent

The earlier GaloisChebyshev and KummerDihedral supplements treat the cubic
Joukowski identity and the cyclic upper extension.  Here the cubic is iterated
for all powers 3^k over any characteristic-zero field, and candidate roots
are proved to be actual roots of an explicitly defined polynomial.

The reconstruction formula shows that two adjacent root candidates determine
the multiplicative coordinate.  It does not assert an equivalence of Galois
groups: that still requires a rational-function-field extension, descent
automorphisms, and a proof of the field degree.
-/

noncomputable section

namespace LinearInputChebyshevDescent

open Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- The multiplicative coordinate modulo inversion. -/
def joukowski (z : K) : K := (z + z⁻¹) / 2

/-- The real-normalized cubic Chebyshev map. -/
def cubic (x : K) : K := 4 * x ^ 3 - 3 * x

/-- The k-fold cubic iterate, of degree 3^k. -/
def chebyIterate (x : K) : ℕ → K
  | 0 => x
  | k + 1 => cubic (chebyIterate x k)

/-- Polynomial corresponding to the cubic map. -/
def cubicPoly : Polynomial K := C (4 : K) * X ^ 3 - C (3 : K) * X

/-- Polynomial composition matching chebyIterate. -/
def chebyPoly : ℕ → Polynomial K
  | 0 => X
  | k + 1 => cubicPoly.comp (chebyPoly k)

theorem cubicPoly_eval (x : K) :
    (cubicPoly (K := K)).eval x = cubic x := by
  simp [cubicPoly, cubic]

theorem chebyPoly_eval (x : K) (k : ℕ) :
    (chebyPoly (K := K) k).eval x = chebyIterate x k := by
  induction k with
  | zero => simp [chebyPoly, chebyIterate]
  | succ k ih =>
    change ((cubicPoly (K := K)).comp (chebyPoly k)).eval x =
      cubic (chebyIterate x k)
    rw [Polynomial.eval_comp, cubicPoly_eval, ih]

theorem cubic_joukowski (z : K) (hz : z ≠ 0) :
    cubic (joukowski z) = joukowski (z ^ 3) := by
  unfold cubic joukowski
  field_simp [hz]
  ring

/-- Every ternary iterate obeys the Joukowski power relation. -/
theorem iterate_joukowski (z : K) (hz : z ≠ 0) (k : ℕ) :
    chebyIterate (joukowski z) k = joukowski (z ^ (3 ^ k)) := by
  induction k with
  | zero => simp [chebyIterate]
  | succ k ih =>
    change cubic (chebyIterate (joukowski z) k) =
      joukowski (z ^ (3 ^ (k + 1)))
    rw [ih, cubic_joukowski (z ^ (3 ^ k)) (pow_ne_zero _ hz)]
    rw [pow_succ, pow_mul]

/-- The j-th radical candidate, before taking inversion orbits. -/
def rootCandidate (ζ z : K) (j : ℕ) : K :=
  joukowski (ζ ^ j * z)

/-- Every radical candidate is an actual root of the iterated equation. -/
theorem candidate_root (k j : ℕ) (ζ z : K)
    (hζ : IsPrimitiveRoot ζ (3 ^ k)) (hz : z ≠ 0) :
    chebyIterate (rootCandidate ζ z j) k =
      joukowski (z ^ (3 ^ k)) := by
  have hm : 3 ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hm
  have hx : ζ ^ j * z ≠ 0 := mul_ne_zero (pow_ne_zero _ hζ0) hz
  change chebyIterate (joukowski (ζ ^ j * z)) k = _
  rw [iterate_joukowski (ζ ^ j * z) hx k]
  congr 1
  rw [mul_pow, ← pow_mul, mul_comm j (3 ^ k), pow_mul, hζ.pow_eq_one]
  simp

/-- A polynomial-level root statement, not just a pointwise map identity. -/
theorem candidate_isRoot (k j : ℕ) (ζ z : K)
    (hζ : IsPrimitiveRoot ζ (3 ^ k)) (hz : z ≠ 0) :
    (chebyPoly (K := K) k -
      C (joukowski (z ^ (3 ^ k)))).IsRoot (rootCandidate ζ z j) := by
  change (chebyPoly (K := K) k -
    C (joukowski (z ^ (3 ^ k)))).eval (rootCandidate ζ z j) = 0
  rw [Polynomial.eval_sub, Polynomial.eval_C, chebyPoly_eval,
    candidate_root k j ζ z hζ hz]
  simp

/-- A primitive root of order at least three cannot equal its inverse. -/
theorem primitive_denom_ne_zero {m : ℕ} {ζ : K}
    (hζ : IsPrimitiveRoot ζ m) (hm : 2 < m) :
    ζ - ζ⁻¹ ≠ 0 := by
  intro h
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by omega)
  have heq : ζ = ζ⁻¹ := sub_eq_zero.mp h
  have htwo : ζ ^ 2 = 1 := by
    calc
      ζ ^ 2 = ζ * ζ := by ring
      _ = ζ * ζ⁻¹ := by rw [heq]
      _ = 1 := mul_inv_cancel₀ hζ0
  have hdiv : m ∣ 2 := hζ.dvd_of_pow_eq_one 2 htwo
  have hle : m ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
  omega

/-- Crucial descent certificate: two adjacent roots recover z itself. -/
theorem reconstruct_z (ζ z : K) (hz : z ≠ 0)
    (hζ : ζ - ζ⁻¹ ≠ 0) :
    z = 2 * (rootCandidate ζ z 1 -
      ζ⁻¹ * rootCandidate ζ z 0) / (ζ - ζ⁻¹) := by
  have hζ0 : ζ ≠ 0 := by
    intro h
    apply hζ
    simp [h]
  apply (eq_div_iff hζ).2
  simp only [rootCandidate, pow_zero, pow_one, one_mul]
  unfold joukowski
  field_simp [hz, hζ0]
  ring

/-- Reconstruction requires no independent nondegeneracy assumption
when the radical has primitive order m > 2. -/
theorem reconstruct_z_primitive {m : ℕ} (ζ z : K)
    (hζ : IsPrimitiveRoot ζ m) (hm : 2 < m) (hz : z ≠ 0) :
    z = 2 * (rootCandidate ζ z 1 -
      ζ⁻¹ * rootCandidate ζ z 0) / (ζ - ζ⁻¹) :=
  reconstruct_z ζ z hz (primitive_denom_ne_zero hζ hm)

/-- The degree-three instance agrees with the existing cubic. -/
theorem chebyIterate_one (x : K) :
    chebyIterate x 1 = cubic x := by
  rfl

end LinearInputChebyshevDescent
