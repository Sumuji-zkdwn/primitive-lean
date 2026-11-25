import Mathlib.Tactic

/-! Algebraic certificates for the exact compact non-CMC data.
    The TT construction, Cauchy locality, and curvature asymptotics are
    separate analytic/SymPy arguments. -/
namespace KKHorizonExactCompactData

theorem localized_hamiltonian (a b d e Q : ℝ) :
    (3 * (a+d) + (b-2*d))^2 -
      (3 * (a+d)^2 + (b-2*d)^2 + e^2*Q) =
      6*a*(a+b)+6*(b*d-d^2)-e^2*Q := by ring

theorem root_cancels (b c e Q : ℝ)
    (hc : c^2 = b^2 - 2*e^2*Q/3) :
    6*(b*((b-c)/2)-((b-c)/2)^2)-e^2*Q = 0 := by
  calc
    _ = (3/2 : ℝ)*(b^2-c^2)-e^2*Q := by ring
    _ = 0 := by rw [hc]; ring

theorem trace_and_volume_combination (a b d : ℝ) :
    3*(a+d)+(b-2*d) = 3*a+b+d ∧
    2*(a+d)+(b-2*d) = 2*a+b := by constructor <;> ring

theorem interior_first_integral (b c e N : ℝ)
    (hc : c^2 = b^2-4*e^2/3) :
    (N*c)^2+4*(N*e)^2/3 = (N*b)^2 := by
  calc
    _ = N^2*(c^2+4*e^2/3) := by ring
    _ = (N*b)^2 := by rw [hc]; ring

theorem causal_margin (D P : ℝ) (hD : 0 < D) (hP : |P| ≤ D/2) :
    0 < D - |P| := by linarith

end KKHorizonExactCompactData
