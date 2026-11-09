import KerrKoopman.AnalyticPDE

/-! The actual fixed-point fields attain the supplied initial Fourier data. -/

namespace KerrKoopman.AnalyticInitial

noncomputable section
set_option backward.isDefEq.respectTransparency false
open AnalyticLift AnalyticAssembly AnalyticFields AnalyticPDE
open AnalyticDuhamel AnalyticModeODE AnalyticFourierDuhamel
open Phase3WeightedDerivative Phase3WeightedRealDecode

def zeroTime (p : Data) : AnalyticLift.Time p.T := ⟨0, le_rfl, p.time_nonneg⟩

theorem mode_initial_zero (T : ℝ) (hT : 0 ≤ T) (β c : ℝ) (hβ : 0 < β)
    (k : ℤ) (f : C(AnalyticLift.Time T, ℂ)) :
    mode T hT β c hβ k f ⟨0, le_rfl, hT⟩ = 0 := by
  change multiplier k * (oscillatoryCLM T hT β |(k : ℝ)| (c * k) hβ (abs_nonneg _) f
    ⟨0, le_rfl, hT⟩) = 0
  rw [← rawOsc_eq T hT β |(k : ℝ)| (c * k) hβ (abs_nonneg _) f ⟨0, le_rfl, hT⟩]
  simp [rawOsc, rawMode_zero]

theorem branch_initial (p : Data) (b : Bool) (k : ℤ) :
    branchTrace p b k (zeroTime p) = component b (p.initial k) := by
  have hm := branch_mild p b k (zeroTime p)
  simpa [zeroTime, waveFactor, mode_initial_zero] using hm

/-- Reconstruction of the given weighted initial coefficients in the fixed
Fourier basis. The width 1/2 is removed explicitly. -/
def initialBranch (p : Data) (b : Bool) (x : ℝ) : ℝ :=
  (∑' k : ℤ, modeValue (1 / 2) k (component b (p.initial k)) x).re

theorem decode_branch_initial (p : Data) (b : Bool) (x : ℝ) :
    decode p (branchTrace p b) (zeroTime p) x = initialBranch p b x := by
  rw [decode_eq]
  unfold realDecode rawDecode initialBranch
  apply congrArg Complex.re
  apply tsum_congr
  intro k
  rw [branch_initial]
  simp [width, zeroTime]

def initialDisplacement (p : Data) (x : ℝ) : ℝ :=
  4 / 3 + speed * (initialBranch p true x - initialBranch p false x)

def initialMagnetic (p : Data) (x : ℝ) : ℝ :=
  3 / 10 + (1 / 2) * (initialBranch p true x + initialBranch p false x)

theorem displacement_initial (p : Data) (x : ℝ) :
    displacementField p (zeroTime p) x = initialDisplacement p x := by
  rw [displacementField_eq, decode_branch_initial, decode_branch_initial]
  rfl

theorem magnetic_initial (p : Data) (x : ℝ) :
    magnetic p (zeroTime p) x = initialMagnetic p x := by
  rw [magnetic_eq, decode_branch_initial, decode_branch_initial]
  rfl

theorem electric_initial (p : Data) (x : ℝ) :
    electric p (zeroTime p) x =
      ExplicitMaterial.electricOfDisplacement (initialDisplacement p x) := by
  rw [← displacement_initial, material_identity]
  exact (ExplicitMaterial.electricOfDisplacement_constitutive (electric p (zeroTime p) x)).symm

end
end KerrKoopman.AnalyticInitial
