import FluidPrismPhaseMemory

/-!
# Thin-film Airy reflectance for a fluid memory interface

This is an optical upgrade to PR #92. The light reflects from an ideal
planar, nonabsorbing, isotropic three-medium stack: N-BASF64 glass,
a liquid film, and air. Incidence is normal, all reflections are coherent,
and the optical constants are real and dispersionless within one wavelength.
The prism geometry, oblique incidence, s/p polarization and actual fluid
mechanics are not included. No experimental memory device is claimed.

For interface amplitude reflection coefficients a,b, the film reflectance
as a function of roundtrip phase cosine x is
 (a²+b²+2ab x)/(1+a²b²+2ab x).
This is the coherent multi-reflection Airy result, not a fitted Boolean
readout. It has unavoidable phase-period ambiguity.

Sample n0=1.67667 is the SCHOTT N-BASF64 value at 1529.6 nm;
n1=1.4 is an explicit illustrative (unmeasured) fluid index, n2=1 air.
-/

noncomputable section
namespace PrismAiryReflectance

/-- Real amplitude Fresnel reflection coefficient at normal incidence. -/
def fresnel (n m : ℝ) : ℝ := (n-m)/(n+m)

/-- Thin-film reflectance from two interfaces and roundtrip cosine x. -/
def airy (a b x : ℝ) : ℝ :=
  (a^2+b^2+2*a*b*x)/(1+a^2*b^2+2*a*b*x)

/-- Optical roundtrip phase of the liquid slab, single wavelength. -/
def roundtripPhase (n thickness wavelength : ℝ) : ℝ :=
  4*Real.pi*n*thickness/wavelength

def filmReflect (n0 n1 n2 wavelength thickness : ℝ) : ℝ :=
  airy (fresnel n0 n1) (fresnel n1 n2)
    (Real.cos (roundtripPhase n1 thickness wavelength))

theorem fresnel_same (n : ℝ) : fresnel n n = 0 := by
  simp [fresnel]

/-- An index-matched first interface eliminates all thickness contrast. -/
theorem first_interface_matched (b x : ℝ) : airy 0 b x = b^2 := by
  simp [airy]

/-- Likewise if the other interface is optically absent. -/
theorem second_interface_matched (a x : ℝ) : airy a 0 x = a^2 := by
  simp [airy]

/-- Constructive interference has a simple rational Fresnel expression. -/
theorem airy_at_one (a b : ℝ) :
    airy a b 1 = ((a+b)/(1+a*b))^2 := by
  unfold airy
  have hn : a^2+b^2+2*a*b*1 = (a+b)^2 := by ring
  have hd : 1+a^2*b^2+2*a*b*1 = (1+a*b)^2 := by ring
  rw [hn, hd, div_pow]

/-- Destructive interference has a second rational expression. -/
theorem airy_at_neg_one (a b : ℝ) :
    airy a b (-1) = ((a-b)/(1-a*b))^2 := by
  unfold airy
  have hn : a^2+b^2+2*a*b*(-1) = (a-b)^2 := by ring
  have hd : 1+a^2*b^2+2*a*b*(-1) = (1-a*b)^2 := by ring
  rw [hn, hd, div_pow]

/-- Exact Airy fringe contrast, including the multiple-reflection
    denominator. Only the two nonzero denominators are assumed. -/
theorem airy_contrast (a b : ℝ)
    (hp : 1+a*b ≠ 0) (hm : 1-a*b ≠ 0) :
    airy a b 1 - airy a b (-1) =
      4*a*b*(1-a^2)*(1-b^2)/
      ((1+a*b)^2*(1-a*b)^2) := by
  rw [airy_at_one, airy_at_neg_one]
  field_simp
  ring

/-- Repetition of a thickness by half the optical wavelength leaves the
    roundtrip cosine (and hence reflectance) unchanged. -/
theorem roundtrip_period (n thickness wavelength : ℝ)
    (hn : n ≠ 0) (hw : wavelength ≠ 0) :
    roundtripPhase n (thickness+wavelength/(2*n)) wavelength =
      roundtripPhase n thickness wavelength+2*Real.pi := by
  unfold roundtripPhase
  field_simp
  ring

theorem reflectance_period (n0 n1 n2 wavelength thickness : ℝ)
    (hn : n1 ≠ 0) (hw : wavelength ≠ 0) :
    filmReflect n0 n1 n2 wavelength
      (thickness+wavelength/(2*n1)) =
    filmReflect n0 n1 n2 wavelength thickness := by
  unfold filmReflect
  rw [roundtrip_period n1 thickness wavelength hn hw, Real.cos_add]
  simp

theorem thickness_shift_nonzero (n wavelength thickness : ℝ)
    (hn : 0 < n) (hw : 0 < wavelength) :
    thickness+wavelength/(2*n) ≠ thickness := by
  have hp : 0 < wavelength/(2*n) := div_pos hw (by positivity)
  linarith

/-- Different positive-thickness films can give identical reflection. -/
theorem thickness_alias (n0 n1 n2 wavelength thickness : ℝ)
    (hn : 0 < n1) (hw : 0 < wavelength) :
    thickness+wavelength/(2*n1) ≠ thickness ∧
      filmReflect n0 n1 n2 wavelength
        (thickness+wavelength/(2*n1)) =
      filmReflect n0 n1 n2 wavelength thickness := by
  exact ⟨thickness_shift_nonzero n1 wavelength thickness hn hw,
    reflectance_period n0 n1 n2 wavelength thickness
      (ne_of_gt hn) (ne_of_gt hw)⟩

theorem phase_at_halfwave (n wavelength : ℝ)
    (hn : n ≠ 0) (hw : wavelength ≠ 0) :
    roundtripPhase n (wavelength/(2*n)) wavelength =
      2*Real.pi := by
  unfold roundtripPhase
  field_simp
  ring

theorem phase_at_three_quarters (n wavelength : ℝ)
    (hn : n ≠ 0) (hw : wavelength ≠ 0) :
    roundtripPhase n (3*wavelength/(4*n)) wavelength =
      3*Real.pi := by
  unfold roundtripPhase
  field_simp
  ring

theorem film_halfwave_high (n0 n1 n2 wavelength : ℝ)
    (hn : n1 ≠ 0) (hw : wavelength ≠ 0) :
    filmReflect n0 n1 n2 wavelength (wavelength/(2*n1)) =
      airy (fresnel n0 n1) (fresnel n1 n2) 1 := by
  unfold filmReflect
  rw [phase_at_halfwave n1 wavelength hn hw]
  simp

theorem film_three_quarters_low (n0 n1 n2 wavelength : ℝ)
    (hn : n1 ≠ 0) (hw : wavelength ≠ 0) :
    filmReflect n0 n1 n2 wavelength (3*wavelength/(4*n1)) =
      airy (fresnel n0 n1) (fresnel n1 n2) (-1) := by
  unfold filmReflect
  rw [phase_at_three_quarters n1 wavelength hn hw]
  have hc : Real.cos (3*Real.pi) = -1 := by
    have h3 : 3*Real.pi = 2*Real.pi+Real.pi := by ring
    rw [h3, Real.cos_add]
    simp
  rw [hc]

/-- SCHOTT catalog n at lambda=1529.6nm. -/
def glassIndex : ℝ := 167667/100000

/-- Hypothetical, index-1.4 fluid, NOT a measured candidate liquid. -/
def fluidIndex : ℝ := 7/5

def incidentInterface : ℝ := fresnel glassIndex fluidIndex
def exitInterface : ℝ := fresnel fluidIndex 1

theorem sample_first_interface :
    incidentInterface = (27667:ℝ)/307667 := by
  norm_num [incidentInterface, fresnel, glassIndex, fluidIndex]

theorem sample_second_interface :
    exitInterface = (1:ℝ)/6 := by
  norm_num [exitInterface, fresnel, fluidIndex]

/-- Exact rational reflectance at the two quarter-fringe endpoints. -/
theorem sample_high :
    airy incidentInterface exitInterface 1 =
      ((473669:ℝ)/1873669)^2 := by
  rw [sample_first_interface, sample_second_interface, airy_at_one]
  norm_num

theorem sample_low :
    airy incidentInterface exitInterface (-1) =
      ((141665:ℝ)/1818335)^2 := by
  rw [sample_first_interface, sample_second_interface, airy_at_neg_one]
  norm_num

theorem sample_contrast_positive :
    airy incidentInterface exitInterface (-1) <
      airy incidentInterface exitInterface 1 := by
  rw [sample_high, sample_low]
  norm_num

/-- The middle threshold succeeds when the absolute reflectance error for
    either sampled film state is strictly smaller than half the true
    absolute contrast. This is deterministic; shot noise is not modeled. -/
theorem contrast_margin (high low error : ℝ)
    (hgap : low < high)
    (he : |error| < (high-low)/2) :
    low+error < (high+low)/2 ∧
      (high+low)/2 < high+error := by
  have hlow := (abs_lt.mp he).1
  have hhigh := (abs_lt.mp he).2
  constructor <;> linarith

/-- The previously assumed quartic memory energy has a saddle-node
    candidate at normalized h=-r and drive u=2r/3 when 3r²=1.
    This does not derive a fluid PDE or identify an experimental threshold. -/
theorem quartic_fold_positive_drive (r : ℝ) (hr : 3*r^2=1) :
    FluidPrismPhaseMemory.energySlope (-r) (2*r/3) = 0 ∧
    FluidPrismPhaseMemory.energyCurvature (-r) = 0 := by
  have hr2 : r^2 = 1/3 := by linarith
  have hr3 : r^3 = r/3 := by
    calc
      r^3 = r*r^2 := by ring
      _ = r/3 := by rw [hr2]; ring
  constructor
  · unfold FluidPrismPhaseMemory.energySlope
    rw [show (-r)^3 = -(r^3) by ring, hr3]
    ring
  · unfold FluidPrismPhaseMemory.energyCurvature
    nlinarith [hr]

theorem critical_root_has_required_square :
    3*(Real.sqrt (3:ℝ)/3)^2 = 1 := by
  have hs : (Real.sqrt (3:ℝ))^2 = 3 :=
    Real.sq_sqrt (by norm_num)
  nlinarith [hs]

theorem explicit_fold :
    FluidPrismPhaseMemory.energySlope
        (-(Real.sqrt (3:ℝ)/3)) (2*(Real.sqrt (3:ℝ)/3)/3) = 0 ∧
    FluidPrismPhaseMemory.energyCurvature
        (-(Real.sqrt (3:ℝ)/3)) = 0 :=
  quartic_fold_positive_drive (Real.sqrt (3:ℝ)/3)
    critical_root_has_required_square

end PrismAiryReflectance
