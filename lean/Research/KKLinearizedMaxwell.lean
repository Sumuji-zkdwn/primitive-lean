import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# A propagating U(1) mode from 5D vacuum Einstein gravity (linear order)

The physical 5D metric is Lorentzian (-,+,+,+,+) with a circle
coordinate w. Cylinder-condition perturbations h_{mu,w}=A_mu(x)
of flat 5D gravity produce mixed linearized Ricci equations:
  Ric^(1)_{mu,w} = (k² epsilon_mu - k_mu k.epsilon)/2
for a plane wave A_mu=epsilon_mu exp(i k.x).

The metric-to-Ricci differentiation is an EXTERNAL input here,
independently calculated from the defining 5D linearized Ricci
operator by tools/check_kk_maxwell.py. Lean proves the exact
gauge invariance, null transverse propagating witness, and algebraic
Kaluza--Klein metric relations. There is no claim of a full
nonlinear Einstein or quantum Standard Model proof in Lean.

The independent SymPy oracle also calculates the FULL 5D Ricci tensor
of a constant magnetic Kaluza--Klein ansatz. It proves that fixing the
circle radius (dilaton) is inconsistent with this non-null magnetic
vacuum configuration: Ric_{ww}=B²/2, not zero.
-/

namespace KKLinearizedMaxwell

abbrev Wave4 := Fin 4 → ℚ
abbrev Metric5 := Matrix (Fin 5) (Fin 5) ℚ

/-- Lorentzian signature (-,+,+,+) inner product on covectors. -/
def lorentzDot (k e : Wave4) : ℚ :=
  -(k 0) * e 0 + (k 1)*e 1 + (k 2)*e 2 + (k 3)*e 3

def gaugeShift (k e : Wave4) (alpha : ℚ) : Wave4 :=
  fun mu => e mu + alpha * k mu

/-- Real algebraic coefficient of the mixed linearized 5D Ricci tensor
in the Fourier representation of a circle-invariant perturbation. -/
def mixedRicci (k e : Wave4) (mu : Fin 4) : ℚ :=
  (lorentzDot k k * e mu - k mu * lorentzDot k e) / 2

/-- Coefficient of the mixed Kaluza--Klein field-strength two-form. -/
def fieldStrength (k e : Wave4) (mu nu : Fin 4) : ℚ :=
  k mu * e nu - k nu * e mu

/-- The metric's circle-coordinate gauge change leaves mixed Ricci
invariant, without requiring Lorenz gauge or the vacuum equations. -/
theorem mixedRicci_gauge_invariant
    (k e : Wave4) (alpha : ℚ) (mu : Fin 4) :
    mixedRicci k (gaugeShift k e alpha) mu =
      mixedRicci k e mu := by
  simp only [mixedRicci, gaugeShift, lorentzDot]
  ring

/-- The emergent Maxwell field strength is likewise gauge invariant. -/
theorem fieldStrength_gauge_invariant
    (k e : Wave4) (alpha : ℚ) (mu nu : Fin 4) :
    fieldStrength k (gaugeShift k e alpha) mu nu =
      fieldStrength k e mu nu := by
  simp only [fieldStrength, gaugeShift]
  ring

/-- A null wave vector and transverse polarization solve the mixed
linearized 5D Ricci vacuum equation for every observed index. -/
theorem null_transverse_implies_mixed_vacuum
    (k e : Wave4) (hnull : lorentzDot k k = 0)
    (htrans : lorentzDot k e = 0) :
    ∀ mu : Fin 4, mixedRicci k e mu = 0 := by
  intro mu
  simp [mixedRicci, hnull, htrans]

def lightlikeK : Wave4 := ![1, 0, 0, 1]
def transverseE : Wave4 := ![0, 1, 0, 0]

theorem explicit_null : lorentzDot lightlikeK lightlikeK = 0 := by
  norm_num [lorentzDot, lightlikeK]

theorem explicit_transverse :
    lorentzDot lightlikeK transverseE = 0 := by
  norm_num [lorentzDot, lightlikeK, transverseE]

theorem explicit_vacuum_wave :
    ∀ mu : Fin 4, mixedRicci lightlikeK transverseE mu = 0 := by
  exact null_transverse_implies_mixed_vacuum lightlikeK transverseE
    explicit_null explicit_transverse

/-- The solution is not pure gauge: its field strength is nonzero. -/
theorem explicit_wave_has_curvature :
    fieldStrength lightlikeK transverseE 0 1 = 1 := by
  norm_num [fieldStrength, lightlikeK, transverseE]

/-- The simplest nonlinear KK metric on Minkowski4 with A_y=B*x. -/
def magneticMetric (B x : ℚ) : Metric5 :=
  !![-1, 0, 0, 0, 0;
      0, 1, 0, 0, 0;
      0, 0, 1+(B*x)^2, 0, B*x;
      0, 0, 0, 1, 0;
      0, 0, B*x, 0, 1]

def magneticInverse (B x : ℚ) : Metric5 :=
  !![-1, 0, 0, 0, 0;
      0, 1, 0, 0, 0;
      0, 0, 1, 0, -(B*x);
      0, 0, 0, 1, 0;
      0, 0, -(B*x), 0, 1+(B*x)^2]

/-- This metric's exact inverse is an algebraic identity in B and x. -/
theorem magnetic_inverse_check (B x : ℚ) :
    magneticMetric B x * magneticInverse B x = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [magneticMetric, magneticInverse,
      Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

/-- In this example F_{xy}=B and F_mu_nu F^mu_nu = 2 B². -/
def magneticF2 (B : ℚ) : ℚ := 2 * B ^ 2

/-- Independent SymPy Ricci calculation gives R5=-B²/2. -/
def measuredScalar5 (B : ℚ) : ℚ := -(B ^ 2) / 2

/-- Independent SymPy Ricci calculation gives Ric_{ww}=+B²/2. -/
def measuredRicciWW (B : ℚ) : ℚ := B ^ 2 / 2

theorem scalar_is_maxwell_kinetic (B : ℚ) :
    measuredScalar5 B = -(magneticF2 B) / 4 := by
  unfold measuredScalar5 magneticF2
  ring

theorem ww_ricci_is_quarter_f2 (B : ℚ) :
    measuredRicciWW B = (magneticF2 B) / 4 := by
  unfold measuredRicciWW magneticF2
  ring

/-- A nonzero, constant magnetic field cannot satisfy all the 5D
vacuum equations with both flat base metric and fixed circle radius.
This is a SPECIFIC exact geometry witness, not a general no-go for
all 5D Ricci-flat Kaluza--Klein solutions. -/
theorem nonzero_magnetic_obstructs_vacuum
    (B : ℚ) (hB : B ≠ 0) : measuredRicciWW B ≠ 0 := by
  unfold measuredRicciWW
  exact div_ne_zero (pow_ne_zero 2 hB) (by norm_num)

/-- If the circle field equation in pure vacuum forces RicWW=0,
a fixed-radius constant magnetic field in this ansatz must vanish. -/
theorem fixed_radius_magnetic_vacuum_only_zero
    (B : ℚ) (hWW : measuredRicciWW B = 0) : B = 0 := by
  by_contra hB
  exact (nonzero_magnetic_obstructs_vacuum B hB) hWW

end KKLinearizedMaxwell
