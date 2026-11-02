/-!
Exact Moore-Penrose pseudoinverses of the actual full F16 normal matrices
at the two singular inputs t=+1 and t=-1.

The matrices are formed from the verified signed-basis left pencil;
the pseudoinverse formula uses the three rational spectral projectors
in F16SpectralProjectors. These certificates are not claims about the
general t-dependent real-valued pseudoinverse.
-/

noncomputable section

namespace LinearInputF16SingularPinv

open LinearInputF16Spectral

/-- Actual 16-dimensional rational Gram matrices at the two singular inputs. -/
def gramPlus : QMat :=
  (leftThreeQ + leftTenQ)ᵀ * (leftThreeQ + leftTenQ)

def gramMinus : QMat :=
  (leftThreeQ - leftTenQ)ᵀ * (leftThreeQ - leftTenQ)

/-- Exact singular pseudoinverses, supported only on nonzero eigenspaces. -/
def pinvPlus : QMat := (1 / 4 : ℚ) • plus + (1 / 2 : ℚ) • zero
def pinvMinus : QMat := (1 / 4 : ℚ) • minus + (1 / 2 : ℚ) • zero

/-- The old 16x16 pencil, not a detached toy diagonal model. -/
theorem gramPlus_eigenspaces :
    gramPlus = (4 : ℚ) • plus + (2 : ℚ) • zero := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem gramMinus_eigenspaces :
    gramMinus = (4 : ℚ) • minus + (2 : ℚ) • zero := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Penrose equation 1, at the positive singular input. -/
theorem plus_penrose_one :
    gramPlus * pinvPlus * gramPlus = gramPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Penrose equation 2, at the positive singular input. -/
theorem plus_penrose_two :
    pinvPlus * gramPlus * pinvPlus = pinvPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Penrose symmetry equations at the positive singular input. -/
theorem plus_penrose_three :
    (gramPlus * pinvPlus)ᵀ = gramPlus * pinvPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem plus_penrose_four :
    (pinvPlus * gramPlus)ᵀ = pinvPlus * gramPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Penrose equation 1, at the negative singular input. -/
theorem minus_penrose_one :
    gramMinus * pinvMinus * gramMinus = gramMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Penrose equation 2, at the negative singular input. -/
theorem minus_penrose_two :
    pinvMinus * gramMinus * pinvMinus = pinvMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Penrose symmetry equations at the negative singular input. -/
theorem minus_penrose_three :
    (gramMinus * pinvMinus)ᵀ = gramMinus * pinvMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem minus_penrose_four :
    (pinvMinus * gramMinus)ᵀ = pinvMinus * gramMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end LinearInputF16SingularPinv
