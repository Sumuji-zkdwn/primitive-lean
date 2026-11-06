import Mathlib.Analysis.ODE.PicardLindelof
import TwoMotionEmissionConsequences

/-!
# Initial-value construction for the two-motion emission model

For the concrete PR #88 parameters κ=c=g=1 and ω₁=ω₂=0, the vector field is a
polynomial map on ℝ⁵. Mathlib's Picard–Lindelöf theorem therefore constructs a
local path from (x₁,v₁,x₂,v₂,y)=(1,0,1,0,0). The existing conditional emission
 theorem then gives strictly positive outgoing work on some positive interval.
This formalizes local existence and the connection to the existing theorem; it
does not formalize global continuation to t=1 or an analytic Taylor remainder.
-/

noncomputable section
open Set
namespace TwoMotionEmission

abbrev IVPState := Fin 5 → ℝ

def ivpForce (q : IVPState) : ℝ := q 0 * q 2 - q 4

def ivpVectorField (q : IVPState) : IVPState :=
  ![q 1, -q 2 * ivpForce q, q 3, -q 0 * ivpForce q, ivpForce q / 2]

def ivpInitial : IVPState := ![1, 0, 1, 0, 0]

def ivpPath (α : ℝ → IVPState) : Path where
  x₁ := fun t => α t 0
  v₁ := fun t => α t 1
  x₂ := fun t => α t 2
  v₂ := fun t => α t 3
  y := fun t => α t 4

theorem ivpVectorField_contDiff : ContDiff ℝ 1 ivpVectorField := by
  fun_prop [ivpVectorField, ivpForce]

theorem ivp_components_solve (α : ℝ → IVPState) (t : ℝ)
    (hα : HasDerivAt α (ivpVectorField (α t)) t) :
    SolvesAt 1 1 0 0 1 (ivpPath α) t := by
  have h := hasDerivAt_pi.mp hα
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [ivpPath, ivpVectorField] using h 0
  · simpa [ivpPath, ivpVectorField, forceAlong, force, ivpForce] using h 1
  · simpa [ivpPath, ivpVectorField] using h 2
  · simpa [ivpPath, ivpVectorField, forceAlong, force, ivpForce] using h 3
  · simpa [ivpPath, ivpVectorField, forceAlong, force, ivpForce] using h 4

/-- Picard–Lindelöf constructs an actual local solution of this initial-value problem. -/
theorem exists_local_ivp :
    ∃ z : Path, z.x₁ 0 = 1 ∧ z.v₁ 0 = 0 ∧ z.x₂ 0 = 1 ∧ z.v₂ 0 = 0 ∧ z.y 0 = 0 ∧
      ∃ ε : ℝ, 0 < ε ∧
        ∀ t ∈ Ioo (-ε) ε, SolvesAt 1 1 0 0 1 z t := by
  obtain ⟨α, hα₀, ε, hε, hα⟩ :=
    ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀
      (ivpVectorField_contDiff.contDiffAt ivpInitial) 0
  refine ⟨ivpPath α, ?_, ?_, ?_, ?_, ?_, ε, hε, ?_⟩
  · simpa [ivpPath, ivpInitial] using congrFun hα₀ (0 : Fin 5)
  · simpa [ivpPath, ivpInitial] using congrFun hα₀ (1 : Fin 5)
  · simpa [ivpPath, ivpInitial] using congrFun hα₀ (2 : Fin 5)
  · simpa [ivpPath, ivpInitial] using congrFun hα₀ (3 : Fin 5)
  · simpa [ivpPath, ivpInitial] using congrFun hα₀ (4 : Fin 5)
  · intro t ht
    exact ivp_components_solve α t (hα t ht)

/-- The actual initial derivatives follow from the constructed path and its IVP. -/
theorem initial_derivatives_of_ivp (z : Path)
    (hx₁ : z.x₁ 0 = 1) (hv₁ : z.v₁ 0 = 0)
    (hx₂ : z.x₂ 0 = 1) (hv₂ : z.v₂ 0 = 0) (hy : z.y 0 = 0)
    (hz : SolvesAt 1 1 0 0 1 z 0) :
    deriv z.x₁ 0 = 0 ∧ deriv z.x₂ 0 = 0 ∧
    deriv z.v₁ 0 = -1 ∧ deriv z.v₂ 0 = -1 ∧ deriv z.y 0 = 1/2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hz.dx₁.deriv, hv₁]
  · rw [hz.dx₂.deriv, hv₂]
  · rw [hz.dv₁.deriv]
    simp [forceAlong, force, hx₁, hx₂, hy]
  · rw [hz.dv₂.deriv]
    simp [forceAlong, force, hx₁, hx₂, hy]
  · rw [hz.dy.deriv]
    simp [forceAlong, force, hx₁, hx₂, hy]

/-- From the locally constructed IVP path, the existing PR #88 theorem yields positive work. -/
theorem exists_local_ivp_with_positive_emission :
    ∃ z : Path, ∃ T : ℝ, 0 < T ∧
      z.x₁ 0 = 1 ∧ z.v₁ 0 = 0 ∧ z.x₂ 0 = 1 ∧ z.v₂ 0 = 0 ∧ z.y 0 = 0 ∧
      (∀ t ∈ Icc 0 T, SolvesAt 1 1 0 0 1 z t) ∧
      0 < emitted 1 (forceAlong 1 1 z) T := by
  obtain ⟨z, hx₁, hv₁, hx₂, hv₂, hy, ε, hε, hsolves⟩ := exists_local_ivp
  let T : ℝ := ε/2
  have hT : 0 < T := by dsimp [T]; linarith
  have hz : ∀ t ∈ Icc 0 T, SolvesAt 1 1 0 0 1 z t := by
    intro t ht
    apply hsolves t
    constructor <;> dsimp [T] <;> linarith
  have hproduct : ∃ t ∈ Icc 0 T, z.x₁ t * z.x₂ t ≠ 0 := by
    refine ⟨0, ?_, ?_⟩
    · constructor <;> simp [T, hε.le]
    · rw [hx₁, hx₂]
      norm_num
  have hwork :=
    (emitted_pos_iff_product_nonzero
      (κ := 1) (c := 1) (T := T) (by norm_num) (by norm_num) hT
      (g := 1) (by norm_num) (ω₁ := 0) (ω₂ := 0) z hy hz).2 hproduct
  exact ⟨z, T, hT, hx₁, hv₁, hx₂, hv₂, hy, hz, hwork⟩

end TwoMotionEmission
