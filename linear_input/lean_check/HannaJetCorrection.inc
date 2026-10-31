/-!
# Hanna coefficient-7 local correction using first-order formal jets

A first jet (a0,a1) represents a0 + a1*x modulo x^2.
For Hanna's alternative generating-function form
  A = Σ_k x^(2k) A^(k^2) / (1 - 2*x*A^k)^(k+1),
the k=3 contribution begins with x^6.  Thus its coefficient of
x^7 only depends on the first jet of A, which is (1,2).
The denominator's inverse at k=3 has first jet (1,8).

This file certifies the local correction 18 -> 26 (difference 8).
It does not by itself prove that the full formal-series coefficient is
6022 or 6030, or identify the series with F0 retraction counts.
-/

noncomputable section

namespace LinearInputHannaJets

/-- Multiplication modulo x^2 of two integer-coefficient series. -/
def jetMul (a b : ℤ × ℤ) : ℤ × ℤ :=
  (a.1 * b.1, a.1 * b.2 + a.2 * b.1)

def jetAdd (a b : ℤ × ℤ) : ℤ × ℤ :=
  (a.1 + b.1, a.2 + b.2)

/-- Repeated jet multiplication (the first jet of a power). -/
def jetPow (a : ℤ × ℤ) : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 => jetMul a (jetPow a n)

def jetX : ℤ × ℤ := (0, 1)
def initialJet : ℤ × ℤ := (1, 2)

/-- First jet of 1 - 2*x*A^3 when A(0)=1 and A'(0)=2. -/
def k3Denominator : ℤ × ℤ :=
  jetAdd (1, 0) (jetMul (-2, 0) (jetMul jetX (jetPow initialJet 3)))

theorem k3_denominator_first_jet : k3Denominator = (1, -2) := by
  decide

/-- (1+2*x)^4 is the first-order inverse of (1-2*x)^4. -/
theorem k3_inverse_first_jet :
    jetMul (jetPow k3Denominator 4) (jetPow (1, 2) 4) = (1, 0) := by
  decide

def k3Omitted : ℤ × ℤ := jetPow initialJet 9

def k3Complete : ℤ × ℤ :=
  jetMul k3Omitted (jetPow (1, 2) 4)

/-- Coefficients of x^7 in the k=3 term with/without its denominator. -/
theorem k3_coefficient_correction :
    k3Omitted.2 = 18 ∧
    k3Complete.2 = 26 ∧
    k3Complete.2 - k3Omitted.2 = 8 := by
  decide

/-- Conditional arithmetic reconciliation; 6022 is NOT deduced here. -/
theorem seventh_coefficient_correction (a : ℤ) (h : a = 6022) :
    a + (k3Complete.2 - k3Omitted.2) = 6030 := by
  rw [h, k3_coefficient_correction.2.2]
  norm_num

end LinearInputHannaJets
