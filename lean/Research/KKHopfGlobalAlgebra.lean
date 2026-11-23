import Mathlib.Tactic

/-!
# Global Hopf polynomial projection and diagonal U(1) circle symmetry
z1=X0+i*X1, z2=X2+i*X3. The projection to R3 is a global polynomial
map, invariant under multiplication of both complex coordinates by
a unit-modulus number. This does not yet construct the quotient
S3/U(1) as a smooth principal-bundle atlas.
-/
namespace KKHopfGlobalAlgebra
abbrev X4 := Fin 4 → ℝ

def radiusSq (X : X4) : ℝ := X 0^2+X 1^2+X 2^2+X 3^2
def hopfX (X : X4) : ℝ := 2*(X 0*X 2+X 1*X 3)
def hopfY (X : X4) : ℝ := 2*(X 0*X 3-X 1*X 2)
def hopfZ (X : X4) : ℝ := X 0^2+X 1^2-X 2^2-X 3^2

theorem hopf_norm (X : X4) :
    (hopfX X)^2+(hopfY X)^2+(hopfZ X)^2 = (radiusSq X)^2 := by
  unfold hopfX hopfY hopfZ radiusSq
  ring

def rotate (c s : ℝ) (X : X4) : X4 := fun i =>
  if i=0 then c*X 0-s*X 1
  else if i=1 then s*X 0+c*X 1
  else if i=2 then c*X 2-s*X 3
  else s*X 2+c*X 3

theorem rotate_comp (c s d t : ℝ) (X : X4) :
    rotate c s (rotate d t X) = rotate (c*d-s*t) (s*d+c*t) X := by
  funext i
  fin_cases i <;> simp [rotate] <;> ring

theorem hopf_rotate_x (c s : ℝ) (X : X4) :
    hopfX (rotate c s X) = (c^2+s^2)*hopfX X := by
  simp [rotate, hopfX]
  ring

theorem hopf_rotate_y (c s : ℝ) (X : X4) :
    hopfY (rotate c s X) = (c^2+s^2)*hopfY X := by
  simp [rotate, hopfY]
  ring

theorem hopf_rotate_z (c s : ℝ) (X : X4) :
    hopfZ (rotate c s X) = (c^2+s^2)*hopfZ X := by
  simp [rotate, hopfZ]
  ring

theorem radius_rotate (c s : ℝ) (X : X4) :
    radiusSq (rotate c s X) = (c^2+s^2)*radiusSq X := by
  simp [rotate, radiusSq]
  ring

theorem hopf_unit_circle_invariant (c s : ℝ) (X : X4)
    (hc : c^2+s^2=1) :
    hopfX (rotate c s X)=hopfX X ∧
    hopfY (rotate c s X)=hopfY X ∧
    hopfZ (rotate c s X)=hopfZ X ∧
    radiusSq (rotate c s X)=radiusSq X := by
  simp [hopf_rotate_x, hopf_rotate_y, hopf_rotate_z, radius_rotate, hc]

theorem hopf_base_nonzero_of_radiusSq_pos (X : X4)
    (hr : 0 < radiusSq X) :
    hopfX X ≠ 0 ∨ hopfY X ≠ 0 ∨ hopfZ X ≠ 0 := by
  by_contra hn
  push Not at hn
  rcases hn with ⟨hx,hy,hz⟩
  have hsq := hopf_norm X
  rw [hx,hy,hz] at hsq
  nlinarith [sq_pos_of_pos hr]

end KKHopfGlobalAlgebra
