/-!
F16 saddle / Cantor horseshoe bridge, added to the verified PR #23 branch.
The branch translations and two-digit selection are explicit new model choices.
This file does not prove any Hausdorff dimension statement.
-/

noncomputable section

namespace LinearInputF16SaddleCantor

open LinearInputF16UnexpectedBridges

/-- Derived from the concrete F16 reflection block 5. -/
def saddle (z : ℝ × ℝ) : ℝ × ℝ :=
  ((5 * z.1 + 4 * (signedAction 5 z).1) / 3,
   (5 * z.2 + 4 * (signedAction 5 z).2) / 3)

theorem saddle_formula (z : ℝ × ℝ) :
    saddle z = ((5 * z.1 + 4 * z.2) / 3, (5 * z.2 + 4 * z.1) / 3) := by
  simp [saddle, reflection_sample]

def eigenCoords (z : ℝ × ℝ) : ℝ × ℝ := (z.1 + z.2, z.1 - z.2)

def fromEigen (z : ℝ × ℝ) : ℝ × ℝ :=
  ((z.1 + z.2) / 2, (z.1 - z.2) / 2)

theorem eigen_fromEigen (z : ℝ × ℝ) :
    eigenCoords (fromEigen z) = z := by
  rcases z with ⟨u, v⟩
  apply Prod.ext <;> simp [eigenCoords, fromEigen] <;> ring

/-- The hyperbolic diagonal normal form is (3u, v/3). -/
theorem saddle_eigen (z : ℝ × ℝ) :
    eigenCoords (saddle z) =
      (3 * (eigenCoords z).1, (eigenCoords z).2 / 3) := by
  rcases z with ⟨x, y⟩
  rw [saddle_formula]
  apply Prod.ext <;> simp [eigenCoords] <;> ring

theorem saddle_zero : saddle (0, 0) = (0, 0) := by
  simp [saddle_formula]

theorem saddle_expands (t : ℝ) : saddle (t, t) = (3 * t, 3 * t) := by
  rw [saddle_formula]
  apply Prod.ext <;> dsimp <;> ring

theorem saddle_contracts (t : ℝ) :
    saddle (t, -t) = (t / 3, -(t / 3)) := by
  rw [saddle_formula]
  apply Prod.ext <;> dsimp <;> ring

theorem saddle_det_one :
    (5 / 3 : ℝ) * (5 / 3) - (4 / 3) * (4 / 3) = 1 := by
  norm_num

/-- Keeping only the outer two symbols of the existing ternary labels. -/
def keptDigit (b : Fin 2) : Fin 3 := if b = 0 then 0 else 2

theorem keptDigit_injective : Function.Injective keptDigit := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [keptDigit] at *

def keptWords (n : ℕ) (w : Fin n → Fin 2) : Fin n → Fin 3 :=
  fun i => keptDigit (w i)

theorem keptWords_injective (n : ℕ) : Function.Injective (keptWords n) := by
  intro v w h
  funext i
  exact keptDigit_injective (congrFun h i)

theorem keptWords_card (n : ℕ) :
    Fintype.card (Fin n → Fin 2) = 2 ^ n := by
  simp

/-- New two-branch affine model, with linear part inherited from F16. -/
def branch (b : Fin 2) (p : ℝ × ℝ) : ℝ × ℝ :=
  (3 * p.1 - ((keptDigit b).val : ℝ),
   (p.2 + ((keptDigit b).val : ℝ)) / 3)

theorem branch_from_saddle (b : Fin 2) (p : ℝ × ℝ) :
    branch b p =
      ((eigenCoords (saddle (fromEigen p))).1 - ((keptDigit b).val : ℝ),
       (eigenCoords (saddle (fromEigen p))).2 + ((keptDigit b).val : ℝ) / 3) := by
  rcases p with ⟨u, v⟩
  rw [saddle_formula]
  apply Prod.ext <;> simp [branch, eigenCoords, fromEigen] <;> ring

theorem branch_injective (b : Fin 2) : Function.Injective (branch b) := by
  intro p q h
  rcases p with ⟨x, y⟩
  rcases q with ⟨u, v⟩
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  dsimp [branch] at hx hy
  have hxu : x = u := by linarith
  have hyv : y = v := by linarith
  simp [hxu, hyv]

theorem branch_zero : branch 0 (0, 0) = (0, 0) := by
  simp [branch, keptDigit]

/-- F0's existing collapse theorem excludes nontrivial two-cycles under
reconstruction and compatibility. A horseshoe must retain extra history. -/
theorem compatible_F0_no_two_cycle
    {α I : Type*} {K : α → α}
    (hK : LinearInputF0.Idempotent K)
    {split : α → I → α} {collect : (I → α) → α}
    (hA : LinearInputF0.Reconstructs split collect)
    (hB : LinearInputF0.Compatible K split)
    {x y : α}
    (hxy : LinearInputF0.step K split collect x = y)
    (hyx : LinearInputF0.step K split collect y = x) : x = y := by
  have hc := LinearInputF0.A_B_collapse hK hA hB
  rw [hc] at hxy hyx
  calc
    x = K y := hyx.symm
    _ = K (K x) := by rw [hxy]
    _ = K x := hK x
    _ = y := hxy

end LinearInputF16SaddleCantor
