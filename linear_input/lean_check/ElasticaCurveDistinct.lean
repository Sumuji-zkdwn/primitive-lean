import ElasticaFixedBoundaryWitness

noncomputable section
namespace FixedBoundaryCurveDistinct
open FixedBoundaryWitness

def coordinates (i : Fin 3) : (ℝ → ℝ) × (ℝ → ℝ) :=
  (Elastica.xCoord (angle i) 0, Elastica.yCoord (angle i) 0)

theorem same_coordinates_same_curvature (i j : Fin 3)
    (h : coordinates i = coordinates j) (s : ℝ) :
    Elastica.curvature (angle i) s = Elastica.curvature (angle j) s := by
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  change Elastica.xCoord (angle i) 0 = Elastica.xCoord (angle j) 0 at hx
  change Elastica.yCoord (angle i) 0 = Elastica.yCoord (angle j) 0 at hy
  have hi : Differentiable ℝ (angle i) :=
    (angle_smooth i).differentiable (by simp)
  have hj : Differentiable ℝ (angle j) :=
    (angle_smooth j).differentiable (by simp)
  have eqi := Elastica.signed_curvature_eq_deriv hi 0 0 s
  have eqj := Elastica.signed_curvature_eq_deriv hj 0 0 s
  have hc :
      deriv (Elastica.xCoord (angle i) 0) s *
          deriv (deriv (Elastica.yCoord (angle i) 0)) s -
        deriv (Elastica.yCoord (angle i) 0) s *
          deriv (deriv (Elastica.xCoord (angle i) 0)) s =
      deriv (Elastica.xCoord (angle j) 0) s *
          deriv (deriv (Elastica.yCoord (angle j) 0)) s -
        deriv (Elastica.yCoord (angle j) 0) s *
          deriv (deriv (Elastica.xCoord (angle j) 0)) s := by rw [hx, hy]
  exact eqi.symm.trans (hc.trans eqj)

theorem curvature_zero_quarter :
    Elastica.curvature (angle (0 : Fin 3)) (1 / 4) = Real.pi := by
  change deriv f (1 / 4) = Real.pi
  have h₁ : 2 * Real.pi * (1 / 4 : ℝ) = Real.pi / 2 := by ring
  have h₂ : 4 * Real.pi * (1 / 4 : ℝ) = Real.pi := by ring
  have h := (hasDeriv_f (1 / 4)).deriv
  rw [h₁, h₂] at h
  simpa using h

theorem curvature_one_quarter :
    Elastica.curvature (angle (1 : Fin 3)) (1 / 4) = -Real.pi := by
  change deriv (fun s => -f s) (1 / 4) = -Real.pi
  have h₁ : 2 * Real.pi * (1 / 4 : ℝ) = Real.pi / 2 := by ring
  have h₂ : 4 * Real.pi * (1 / 4 : ℝ) = Real.pi := by ring
  have h := (hasDeriv_f (1 / 4)).neg.deriv
  rw [h₁, h₂] at h
  simpa using h

theorem coords_zero_ne_one : coordinates (0 : Fin 3) ≠ coordinates 1 := by
  intro h
  have hc := same_coordinates_same_curvature 0 1 h (1 / 4)
  rw [curvature_zero_quarter, curvature_one_quarter] at hc
  linarith [Real.pi_pos]

theorem coords_zero_ne_two : coordinates (0 : Fin 3) ≠ coordinates 2 := by
  intro h
  have hc := same_coordinates_same_curvature 0 2 h 0
  rw [curvature_zero, curvature_two] at hc
  linarith [Real.pi_pos]

theorem coords_one_ne_two : coordinates (1 : Fin 3) ≠ coordinates 2 := by
  intro h
  have hc := same_coordinates_same_curvature 1 2 h 0
  rw [curvature_one, curvature_two] at hc
  linarith [Real.pi_pos]

theorem coordinates_injective : Function.Injective coordinates := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first
    | rfl
    | exact (coords_zero_ne_one h).elim
    | exact (coords_zero_ne_one h.symm).elim
    | exact (coords_zero_ne_two h).elim
    | exact (coords_zero_ne_two h.symm).elim
    | exact (coords_one_ne_two h).elim
    | exact (coords_one_ne_two h.symm).elim

#print axioms coordinates_injective
end FixedBoundaryCurveDistinct
