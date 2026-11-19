/-!
Exact Moore-Penrose pseudoinverses of the actual full F16 normal matrices
at the two singular inputs t=+1 and t=-1.

The matrices are formed from the verified signed-basis left pencil;
the pseudoinverse formula uses the three rational spectral projectors
in F16SpectralProjectors. These certificates are not claims about the
general t-dependent real-valued pseudoinverse.
-/

noncomputable section
open scoped Matrix

namespace LinearInputF16SingularPinv

open LinearInputF16Spectral

/-- Actual 16-dimensional rational Gram matrices at the two singular inputs. -/
abbrev gramPlus : QMat :=
  (leftThreeQ + leftTenQ)ᵀ * (leftThreeQ + leftTenQ)

abbrev gramMinus : QMat :=
  (leftThreeQ - leftTenQ)ᵀ * (leftThreeQ - leftTenQ)

/-- Exact singular pseudoinverses, supported only on nonzero eigenspaces. -/
abbrev pinvPlus : QMat := (1 / 4 : ℚ) • plus + (1 / 2 : ℚ) • zero
abbrev pinvMinus : QMat := (1 / 4 : ℚ) • minus + (1 / 2 : ℚ) • zero

private theorem combine_mul (P Z : QMat) (hP : P * P = P) (hZ : Z * Z = Z)
    (hPZ : P * Z = 0) (hZP : Z * P = 0) (a b c d : ℚ) :
    (a • P + b • Z) * (c • P + d • Z) = (a*c) • P + (b*d) • Z := by
  simp only [Matrix.add_mul, Matrix.mul_add, smul_mul_assoc, mul_smul_comm,
    smul_smul, hP, hZ, hPZ, hZP, smul_zero, add_zero, zero_add]
  rw [mul_comm c a, mul_comm d b]

private theorem combine_sym (P Z : QMat) (hP : Pᵀ = P) (hZ : Zᵀ = Z) (a b : ℚ) :
    (a • P + b • Z)ᵀ = a • P + b • Z := by
  rw [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul, hP, hZ]

private theorem zero_plus : zero * plus = 0 := by
  have h := congrArg Matrix.transpose plus_zero_zero
  simpa only [Matrix.transpose_mul, plus_symmetric, zero_symmetric,
    Matrix.transpose_zero] using h

private theorem zero_minus : zero * minus = 0 := by
  have h := congrArg Matrix.transpose minus_zero_zero
  simpa only [Matrix.transpose_mul, minus_symmetric, zero_symmetric,
    Matrix.transpose_zero] using h

/-- The old 16x16 pencil, not a detached toy diagonal model. -/
theorem gramPlus_eigenspaces :
    gramPlus = (4 : ℚ) • plus + (2 : ℚ) • zero := by
  apply LinearInputF16Spectral.eq_of_all_entries
  decide +kernel

theorem gramMinus_eigenspaces :
    gramMinus = (4 : ℚ) • minus + (2 : ℚ) • zero := by
  apply LinearInputF16Spectral.eq_of_all_entries
  decide +kernel

/-- Penrose equation 1, at the positive singular input. -/
theorem plus_penrose_one :
    gramPlus * pinvPlus * gramPlus = gramPlus := by
  simp only [gramPlus_eigenspaces, pinvPlus,
    combine_mul plus zero plus_idempotent zero_idempotent plus_zero_zero zero_plus]
  norm_num

/-- Penrose equation 2, at the positive singular input. -/
theorem plus_penrose_two :
    pinvPlus * gramPlus * pinvPlus = pinvPlus := by
  simp only [gramPlus_eigenspaces, pinvPlus,
    combine_mul plus zero plus_idempotent zero_idempotent plus_zero_zero zero_plus]
  norm_num

/-- Penrose symmetry equations at the positive singular input. -/
theorem plus_penrose_three :
    (gramPlus * pinvPlus)ᵀ = gramPlus * pinvPlus := by
  simp only [gramPlus_eigenspaces, pinvPlus,
    combine_mul plus zero plus_idempotent zero_idempotent plus_zero_zero zero_plus,
    combine_sym plus zero plus_symmetric zero_symmetric]

theorem plus_penrose_four :
    (pinvPlus * gramPlus)ᵀ = pinvPlus * gramPlus := by
  simp only [gramPlus_eigenspaces, pinvPlus,
    combine_mul plus zero plus_idempotent zero_idempotent plus_zero_zero zero_plus,
    combine_sym plus zero plus_symmetric zero_symmetric]

/-- Penrose equation 1, at the negative singular input. -/
theorem minus_penrose_one :
    gramMinus * pinvMinus * gramMinus = gramMinus := by
  simp only [gramMinus_eigenspaces, pinvMinus,
    combine_mul minus zero minus_idempotent zero_idempotent minus_zero_zero zero_minus]
  norm_num

/-- Penrose equation 2, at the negative singular input. -/
theorem minus_penrose_two :
    pinvMinus * gramMinus * pinvMinus = pinvMinus := by
  simp only [gramMinus_eigenspaces, pinvMinus,
    combine_mul minus zero minus_idempotent zero_idempotent minus_zero_zero zero_minus]
  norm_num

/-- Penrose symmetry equations at the negative singular input. -/
theorem minus_penrose_three :
    (gramMinus * pinvMinus)ᵀ = gramMinus * pinvMinus := by
  simp only [gramMinus_eigenspaces, pinvMinus,
    combine_mul minus zero minus_idempotent zero_idempotent minus_zero_zero zero_minus,
    combine_sym minus zero minus_symmetric zero_symmetric]

theorem minus_penrose_four :
    (pinvMinus * gramMinus)ᵀ = pinvMinus * gramMinus := by
  simp only [gramMinus_eigenspaces, pinvMinus,
    combine_mul minus zero minus_idempotent zero_idempotent minus_zero_zero zero_minus,
    combine_sym minus zero minus_symmetric zero_symmetric]

end LinearInputF16SingularPinv
