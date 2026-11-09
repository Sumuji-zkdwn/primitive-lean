import KerrKoopman.PrimitiveSource
import KerrKoopman.Riccati
import KerrKoopman.FiniteEnergy
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# The Kerr material law derived from primitive-lean's quartic certificates

The primitive quartic has coefficients lambda = 1/3 and r = 1. Its derivative
is D(E) = E + E^3/3. The quartic itself is the electric coenergy; the physical
electric energy is its Legendre value E*D(E) - coenergy(E). No evolution equation
or Koopman representation follows from this static constitutive derivation.
-/

namespace KerrKoopman.PrimitiveConstitutive

noncomputable section

open KerrKoopman.Riccati

def coenergy (e : ℝ) : ℝ := e ^ 2 / 2 + e ^ 4 / 12

def tiltedPotential (d e : ℝ) : ℝ := coenergy e - d * e

theorem constitutive_eq_primitive_input (e : ℝ) :
    constitutive e = LinearInputDesign.input (1 / 3) 1 e := by
  unfold constitutive LinearInputDesign.input
  ring

theorem tilted_eq_primitive_potential (d e : ℝ) :
    tiltedPotential d e = LinearInputCalculus.potential (1 / 3) 1 d e := by
  unfold tiltedPotential coenergy LinearInputCalculus.potential
  ring

theorem tilted_eq_primitive_f (d e : ℝ) :
    tiltedPotential d e = LinearInputDesign.f (1 / 3) 1 d e := by
  unfold tiltedPotential coenergy LinearInputDesign.f
  ring

/-- An actual derivative obtained by instantiating primitive-lean's theorem. -/
theorem coenergy_hasDerivAt (e : ℝ) :
    HasDerivAt coenergy (constitutive e) e := by
  have h := LinearInputCalculus.hasDerivAt_potential (1 / 3) 1 0 e
  have hf : coenergy = LinearInputCalculus.potential (1 / 3) 1 0 := by
    funext x
    dsimp [coenergy, LinearInputCalculus.potential]
    ring
  rw [hf]
  convert h using 1
  unfold constitutive
  ring

/-- The primitive scalar-gap certificate becomes a global Kerr support identity. -/
theorem constitutive_gap (a e : ℝ) :
    coenergy e - coenergy a - constitutive a * (e - a) =
      (e - a) ^ 2 * ((e + a) ^ 2 / 12 + (a ^ 2 / 3 + 1) / 2) := by
  have h := LinearInputDesign.scalar_gap (1 / 3) 1 a e
  rw [← constitutive_eq_primitive_input a] at h
  simp only [← tilted_eq_primitive_f, tiltedPotential] at h
  convert h using 1 <;> ring

/-- A displacement error cannot flatten the material energy below a quadratic. -/
theorem quadratic_support (a e : ℝ) :
    (e - a) ^ 2 / 2 ≤
      coenergy e - coenergy a - constitutive a * (e - a) := by
  rw [constitutive_gap]
  have hs : 0 ≤ (e - a) ^ 2 := sq_nonneg _
  have hp : 0 ≤ (e + a) ^ 2 := sq_nonneg _
  have ha : 0 ≤ a ^ 2 := sq_nonneg _
  nlinarith [mul_nonneg hs hp, mul_nonneg hs ha]

/-- The static constitutive relation is exactly the global-minimum condition. -/
theorem global_minimum_iff_constitutive (d a : ℝ) :
    (∀ e : ℝ, tiltedPotential d a ≤ tiltedPotential d e) ↔
      d = constitutive a := by
  constructor
  · intro hmin
    have h := LinearInputCalculus.global_minimum_forces_input
      (lam := (1 / 3 : ℝ)) (r := 1) (u := d) (a := a)
      (fun e => by simpa only [← tilted_eq_primitive_potential] using hmin e)
    simpa only [constitutive_eq_primitive_input, LinearInputDesign.input] using h
  · intro hd
    subst d
    have hmin := LinearInputDesign.globalMin_of_margin
      (lam := (1 / 3 : ℝ)) (r := 1) (a := a) (by norm_num)
      (by positivity)
    intro e
    have h := hmin e (Real.sqrt 2 * e)
    simpa only [LinearInputDesign.E, sub_self, zero_pow (by decide : 2 ≠ 0),
      zero_div, add_zero, ← constitutive_eq_primitive_input,
      ← tilted_eq_primitive_f] using h

/-- Each prescribed displacement has at most one global minimizing field. -/
theorem minimizer_unique {d a e : ℝ}
    (ha : d = constitutive a)
    (he : ∀ x : ℝ, tiltedPotential d e ≤ tiltedPotential d x) : e = a := by
  have hmin := (global_minimum_iff_constitutive d a).mpr ha
  have heq : tiltedPotential d e = tiltedPotential d a :=
    le_antisymm (he a) (hmin e)
  have h := quadratic_support a e
  have hs : coenergy e - coenergy a - constitutive a * (e - a) = 0 := by
    dsimp [tiltedPotential] at heq
    rw [ha] at heq
    linarith
  rw [hs] at h
  nlinarith [sq_nonneg (e - a)]

/-- primitive-lean's critical value is minus the physical electric energy. -/
theorem electric_energy_eq_negative_minimum (e : ℝ) :
    FiniteEnergy.density e 0 = -tiltedPotential (constitutive e) e := by
  have h := LinearInputCalculus.critical_value
    (lam := (1 / 3 : ℝ)) (r := 1) (u := constitutive e) (x := e)
    (by rw [constitutive_eq_primitive_input]; rfl)
  rw [← tilted_eq_primitive_potential] at h
  dsimp [FiniteEnergy.density]
  linarith

/-- The physical Kerr density is the magnetic square plus the Legendre value. -/
theorem physical_density_legendre (e h : ℝ) :
    FiniteEnergy.density e h = h ^ 2 / 2 + e * constitutive e - coenergy e := by
  have he := electric_energy_eq_negative_minimum e
  dsimp [FiniteEnergy.density, tiltedPotential] at he ⊢
  nlinarith

/-- Strong monotonicity follows from two opposite primitive support inequalities. -/
theorem constitutive_strong_monotone (a e : ℝ) :
    (e - a) ^ 2 ≤ (constitutive e - constitutive a) * (e - a) := by
  have hae := quadratic_support a e
  have hea := quadratic_support e a
  nlinarith

theorem constitutive_injective : Function.Injective constitutive := by
  intro a e heq
  have h := constitutive_strong_monotone a e
  rw [heq, sub_self, zero_mul] at h
  nlinarith [sq_nonneg (e - a)]

/-- A pointwise displacement residual bounds the field reconstruction error. -/
theorem constitutive_inverse_stability (a e : ℝ) :
    |e - a| ≤ |constitutive e - constitutive a| := by
  have h := constitutive_strong_monotone a e
  have hprod : (constitutive e - constitutive a) * (e - a) ≤
      |constitutive e - constitutive a| * |e - a| := by
    rw [← abs_mul]
    exact le_abs_self _
  have he : 0 ≤ |e - a| := abs_nonneg _
  have hd : 0 ≤ |constitutive e - constitutive a| := abs_nonneg _
  have hs : |e - a| ^ 2 = (e - a) ^ 2 := sq_abs _
  nlinarith

/-- An approximate minimum gives an explicit a posteriori field error. -/
theorem minimization_error_bound {a e ε : ℝ}
    (herror : tiltedPotential (constitutive a) e -
      tiltedPotential (constitutive a) a ≤ ε) :
    |e - a| ≤ Real.sqrt (2 * ε / (a ^ 2 / 3 + 1)) := by
  have h := LinearInputDesign.position_error
    (lam := (1 / 3 : ℝ)) (r := 1) (a := a) (x := e)
    (y := Real.sqrt 2 * e) (eps := ε) (by norm_num) (by positivity)
    (by simpa only [LinearInputDesign.E, sub_self, zero_pow (by decide : 2 ≠ 0),
      zero_div, add_zero, ← constitutive_eq_primitive_input,
      ← tilted_eq_primitive_f] using herror)
  have hden : (1 / 3 : ℝ) * a ^ 2 + 1 = a ^ 2 / 3 + 1 := by ring
  simpa only [hden] using h

/-- Every displacement has a material preimage in this explicit finite bracket.
The intermediate-value argument is applied to the actual continuous cubic. -/
theorem constitutive_preimage_in_bracket (d : ℝ) :
    ∃ e ∈ Set.Icc (-(|d| + 1)) (|d| + 1), constitutive e = d := by
  let m : ℝ := |d| + 1
  have hm : 0 ≤ m := by dsimp [m]; positivity
  have hp : 0 ≤ m ^ 3 := pow_nonneg hm 3
  have hlo : constitutive (-m) ≤ d := by
    calc
      constitutive (-m) = -m - m ^ 3 / 3 := by unfold constitutive; ring
      _ ≤ -m := by linarith
      _ ≤ d := by dsimp [m]; linarith [neg_abs_le d]
  have hhi : d ≤ constitutive m := by
    calc
      d ≤ m := by dsimp [m]; linarith [le_abs_self d]
      _ ≤ constitutive m := by unfold constitutive; linarith
  have hc : Continuous constitutive := by unfold constitutive; continuity
  have hab : -m ≤ m := by linarith
  exact intermediate_value_Icc hab hc.continuousOn ⟨hlo, hhi⟩

theorem constitutive_surjective : Function.Surjective constitutive := by
  intro d
  obtain ⟨e, _, he⟩ := constitutive_preimage_in_bracket d
  exact ⟨e, he⟩

theorem constitutive_bijective : Function.Bijective constitutive :=
  ⟨constitutive_injective, constitutive_surjective⟩

/-- One fixed material coordinate for all initial fields. Its inverse below is
an implicitly specified algebraic inverse, not a formula for physical time flow. -/
def constitutiveEquiv : ℝ ≃ ℝ :=
  Equiv.ofBijective constitutive constitutive_bijective

def materialInverse (d : ℝ) : ℝ := constitutiveEquiv.symm d

theorem constitutiveEquiv_apply (e : ℝ) : constitutiveEquiv e = constitutive e := rfl

theorem constitutive_materialInverse (d : ℝ) :
    constitutive (materialInverse d) = d :=
  constitutiveEquiv.apply_symm_apply d

theorem materialInverse_constitutive (e : ℝ) :
    materialInverse (constitutive e) = e :=
  constitutiveEquiv.symm_apply_apply e

/-- Existence and uniqueness hold for every prescribed real displacement. -/
theorem existsUnique_global_minimum (d : ℝ) :
    ∃! a : ℝ, ∀ e : ℝ, tiltedPotential d a ≤ tiltedPotential d e := by
  refine ⟨materialInverse d, ?_, ?_⟩
  · exact (global_minimum_iff_constitutive d _).mpr
      (constitutive_materialInverse d).symm
  · intro a ha
    exact minimizer_unique (constitutive_materialInverse d).symm ha

/-- The shared inverse coordinate has a global displacement-to-field error bound. -/
theorem materialInverse_stability (d₁ d₂ : ℝ) :
    |materialInverse d₁ - materialInverse d₂| ≤ |d₁ - d₂| := by
  simpa only [constitutive_materialInverse] using
    constitutive_inverse_stability (materialInverse d₂) (materialInverse d₁)

theorem materialInverse_lipschitz : LipschitzWith 1 materialInverse := by
  apply LipschitzWith.of_dist_le_mul
  intro d₁ d₂
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using materialInverse_stability d₁ d₂

end

end KerrKoopman.PrimitiveConstitutive
