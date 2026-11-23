import Mathlib.Tactic

/-!
# Local radial Kaluza--Klein vacuum and EMD: polynomial certificates

Axiom/compilation status is determined by the dedicated CI; this is an
algebraic certificate model, not a formalized Lorentzian curvature derivation.

The independent oracle `check_radial_bridge.py` differentiates the metric
  ds5^2 = -dt^2 + H(r) (dr^2 + r^2 dOmega^2)
                + H(r)^(-1) (dpsi + b cos(theta) dvarphi)^2.

Below r,h,dH,ddH,b,s,c are *formal rational scalars* standing for
r, H(r), H'(r), H''(r), b, sin(theta), cos(theta).
This file proves algebraic identities about the oracle's numerator
certificates, NOT that these scalars come from an actual differentiable
metric/connection. The latter step is outside the Lean kernel here.
-/

namespace KKRadialVacuumBridge

/-- Radial harmonicity defect L=r H''+2H'. -/
def harmonic (r dh ddh : ℚ) : ℚ := r * ddh + 2 * dh

/-- Magnetic charge minus squared radial flux: C=b²-(r²H')². -/
def charge (r dh b : ℚ) : ℚ := b^2 - (r^2 * dh)^2

/-- Common numerator Q=C+r³ H L of the remaining 5D Ricci entries. -/
def total (r h dh ddh b : ℚ) : ℚ :=
  charge r dh b + r^3 * h * harmonic r dh ddh

/-- Two 5D Ricci numerators, after removing nonzero denominators. -/
def ricciRadialNumerator (r dh ddh : ℚ) : ℚ :=
  -(harmonic r dh ddh)

def ricciFibreNumerator (r h dh ddh b : ℚ) : ℚ :=
  total r h dh ddh b

/-- Other possible 5D Ricci numerators in the general-H radial ansatz. -/
def ricciThetaNumerator (r h dh ddh b : ℚ) : ℚ :=
  -(total r h dh ddh b)

def ricciPhiNumerator (r h dh ddh b s c : ℚ) : ℚ :=
  -((r*h*s)^2-(b*c)^2) * total r h dh ddh b

def ricciPhiPsiNumerator (r h dh ddh b c : ℚ) : ℚ :=
  b*c*total r h dh ddh b

/-- Normalized 4D EMD Ricci-form Einstein residual numerators. -/
def emdTimeNumerator (r h dh ddh b : ℚ) : ℚ :=
  -(total r h dh ddh b)

def emdRadialNumerator (r h dh ddh b : ℚ) : ℚ :=
  charge r dh b - r^3 * h * harmonic r dh ddh

def emdAngularNumerator (r h dh ddh b : ℚ) : ℚ :=
  -(total r h dh ddh b)

def emdScalarNumerator (r h dh ddh b : ℚ) : ℚ :=
  total r h dh ddh b

/-- The polynomial decomposition replacing a full 5D Ricci calculation. -/
theorem total_decomposition (r h dh ddh b : ℚ) :
    total r h dh ddh b =
      b^2-(r^2*dh)^2 + r^3*h*(r*ddh+2*dh) := by
  unfold total charge harmonic
  ring

/-- The 5D radial/fibre equations imply exactly the two radial defects. -/
def twoRicciCertificate (r h dh ddh b : ℚ) : Prop :=
  ricciRadialNumerator r dh ddh = 0 ∧
  ricciFibreNumerator r h dh ddh b = 0

theorem two_ricci_iff_defects (r h dh ddh b : ℚ) :
    twoRicciCertificate r h dh ddh b ↔
      harmonic r dh ddh = 0 ∧ charge r dh b = 0 := by
  constructor
  · rintro ⟨hR,hF⟩
    have hL : harmonic r dh ddh = 0 := by
      have hn : -(harmonic r dh ddh) = 0 := by
        simpa [ricciRadialNumerator] using hR
      exact neg_eq_zero.mp hn
    have hQ : total r h dh ddh b = 0 := hF
    have hC : charge r dh b = 0 := by
      simpa [total, hL] using hQ
    exact ⟨hL,hC⟩
  · rintro ⟨hL,hC⟩
    constructor
    · simp [ricciRadialNumerator, hL]
    · simp [ricciFibreNumerator, total, hL, hC]

/-- Adding angular and mixed components does not introduce conditions. -/
def allRicciCertificate (r h dh ddh b s c : ℚ) : Prop :=
  twoRicciCertificate r h dh ddh b ∧
  ricciThetaNumerator r h dh ddh b = 0 ∧
  ricciPhiNumerator r h dh ddh b s c = 0 ∧
  ricciPhiPsiNumerator r h dh ddh b c = 0

theorem all_ricci_iff_two (r h dh ddh b s c : ℚ) :
    allRicciCertificate r h dh ddh b s c ↔
      twoRicciCertificate r h dh ddh b := by
  constructor
  · intro hAll
    exact hAll.1
  · intro hTwo
    have hQ : total r h dh ddh b = 0 := hTwo.2
    refine ⟨hTwo, ?_, ?_, ?_⟩
    · simp [ricciThetaNumerator, hQ]
    · simp [ricciPhiNumerator, hQ]
    · simp [ricciPhiPsiNumerator, hQ]

/-- The two essential normalized 4D Einstein residuals suffice. -/
def twoEinsteinCertificate (r h dh ddh b : ℚ) : Prop :=
  emdTimeNumerator r h dh ddh b = 0 ∧
  emdRadialNumerator r h dh ddh b = 0

/-- Algebraic 4D<->5D equivalence for the *normalized radial symbols*.
The hypotheses r!=0,h!=0 are needed to recover L from r³ h L=0. -/
theorem two_einstein_iff_two_ricci (r h dh ddh b : ℚ)
    (hr : r ≠ 0) (hh : h ≠ 0) :
    twoEinsteinCertificate r h dh ddh b ↔
      twoRicciCertificate r h dh ddh b := by
  constructor
  · rintro ⟨hTime,hRadial⟩
    have hQ : total r h dh ddh b = 0 := by
      have hn : -(total r h dh ddh b) = 0 := by
        simpa [emdTimeNumerator] using hTime
      exact neg_eq_zero.mp hn
    have hE : charge r dh b - r^3*h*harmonic r dh ddh = 0 := by
      simpa [emdRadialNumerator] using hRadial
    have hProduct : (r^3*h)*harmonic r dh ddh = 0 := by
      dsimp [total] at hQ
      linarith
    have hCoeff : (r^3*h : ℚ) ≠ 0 :=
      mul_ne_zero (pow_ne_zero 3 hr) hh
    have hL : harmonic r dh ddh = 0 :=
      (mul_eq_zero.mp hProduct).resolve_left hCoeff
    exact ⟨by simp [ricciRadialNumerator, hL], hQ⟩
  · rintro ⟨hR,hF⟩
    have hL : harmonic r dh ddh = 0 := by
      have hn : -(harmonic r dh ddh) = 0 := by
        simpa [ricciRadialNumerator] using hR
      exact neg_eq_zero.mp hn
    have hQ : total r h dh ddh b = 0 := hF
    have hC : charge r dh b = 0 := by
      simpa [total, hL] using hQ
    constructor
    · simp [emdTimeNumerator, hQ]
    · simp [emdRadialNumerator, hC, hL]

/-- All other 4D component/source numerators vanish with the same Q. -/
def allEinsteinCertificate (r h dh ddh b : ℚ) : Prop :=
  twoEinsteinCertificate r h dh ddh b ∧
  emdAngularNumerator r h dh ddh b = 0 ∧
  emdScalarNumerator r h dh ddh b = 0

theorem all_einstein_iff_two (r h dh ddh b : ℚ) :
    allEinsteinCertificate r h dh ddh b ↔
      twoEinsteinCertificate r h dh ddh b := by
  constructor
  · intro hAll
    exact hAll.1
  · intro hTwo
    have hQ : total r h dh ddh b = 0 := by
      have hn : -(total r h dh ddh b) = 0 := by
        simpa [emdTimeNumerator] using hTwo.1
      exact neg_eq_zero.mp hn
    exact ⟨hTwo, by simp [emdAngularNumerator, hQ],
                  by simp [emdScalarNumerator, hQ]⟩

/-- Fully polynomial bridge; no differential geometry formalized here. -/
theorem fiveD_iff_fourD_certificates (r h dh ddh b s c : ℚ)
    (hr : r ≠ 0) (hh : h ≠ 0) :
    allRicciCertificate r h dh ddh b s c ↔
      allEinsteinCertificate r h dh ddh b := by
  calc
    allRicciCertificate r h dh ddh b s c ↔
        twoRicciCertificate r h dh ddh b :=
      all_ricci_iff_two r h dh ddh b s c
    _ ↔ twoEinsteinCertificate r h dh ddh b :=
      (two_einstein_iff_two_ricci r h dh ddh b hr hh).symm
    _ ↔ allEinsteinCertificate r h dh ddh b :=
      (all_einstein_iff_two r h dh ddh b).symm

/-- Difference of the two normalized 4D Einstein equations isolates charge. -/
theorem radial_einstein_difference (r h dh ddh b : ℚ) :
    emdTimeNumerator r h dh ddh b -
      emdRadialNumerator r h dh ddh b =
    -2*charge r dh b := by
  unfold emdTimeNumerator emdRadialNumerator total
  ring

/-- Their sum isolates harmonicity (up to a nonzero r³ h factor). -/
theorem radial_einstein_sum (r h dh ddh b : ℚ) :
    emdTimeNumerator r h dh ddh b +
      emdRadialNumerator r h dh ddh b =
    -2*r^3*h*harmonic r dh ddh := by
  unfold emdTimeNumerator emdRadialNumerator total
  ring

end KKRadialVacuumBridge