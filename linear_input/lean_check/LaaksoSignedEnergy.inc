/-!
The signed-connection energy on the first labelled Laakso graph.
This is the specialization lambda = kappa = 1 and u = 0 of Research's
SIGNED_CONNECTIONS.md, section 4, with q_i = (x_i,y_i). It is distinct
from the scalar cubic-reaction model in LaaksoNonlinearObstruction.inc.

The flipped sector has a uniform positive lower bound. No sharpness of
that bound, existence of a minimizer, dynamics or continuum claim is made.
-/

noncomputable section

namespace LinearInputLaaksoSignedEnergy

open LinearInputLaaksoFiniteGraph LinearInputLaaksoSigned

abbrev State := Fin 6 → ℝ × ℝ

/-- Two wells at (1,sqrt 2) and (-1,-sqrt 2). -/
def localPotential (q : ℝ × ℝ) : ℝ :=
  (q.1 ^ 2 - 1) ^ 2 / 4 + (q.2 - Real.sqrt 2 * q.1) ^ 2 / 2

/-- The local term is the existing linear-input energy with its well value
shifted to zero; the shift does not replace its defining formula. -/
theorem localPotential_eq_design_energy (q : ℝ × ℝ) :
    localPotential q = LinearInputDesign.E 1 (-1) 0 q.1 q.2 + 1 / 4 := by
  unfold localPotential LinearInputDesign.E LinearInputDesign.f
  ring

/-- One contribution for each edge ID, including both parallel edges. -/
def edgeEnergy (τ : Twist) (q : State) (e : Fin 6) : ℝ :=
  (((q (firstSource e)).1 - sign τ e * (q (firstTarget e)).1) ^ 2 +
    ((q (firstSource e)).2 - sign τ e * (q (firstTarget e)).2) ^ 2) / 2

def energy (τ : Twist) (q : State) : ℝ :=
  (∑ v : Fin 6, localPotential (q v)) + ∑ e : Fin 6, edgeEnergy τ q e

theorem localPotential_nonneg (q : ℝ × ℝ) : 0 ≤ localPotential q := by
  unfold localPotential
  positivity

theorem edgeEnergy_nonneg (τ : Twist) (q : State) (e : Fin 6) :
    0 ≤ edgeEnergy τ q e := by
  unfold edgeEnergy
  positivity

theorem energy_nonneg (τ : Twist) (q : State) : 0 ≤ energy τ q := by
  exact add_nonneg (Finset.sum_nonneg fun v _ => localPotential_nonneg (q v))
    (Finset.sum_nonneg fun e _ => edgeEnergy_nonneg τ q e)

def constantWell : State := fun _ => (1, Real.sqrt 2)

theorem localPotential_constantWell (v : Fin 6) :
    localPotential (constantWell v) = 0 := by
  simp [localPotential, constantWell]

theorem edgeEnergy_untwisted_constantWell (e : Fin 6) :
    edgeEnergy untwisted constantWell e = 0 := by
  simp [edgeEnergy, constantWell, sign_untwisted]

theorem energy_untwisted_constantWell : energy untwisted constantWell = 0 := by
  simp [energy, localPotential_constantWell, edgeEnergy_untwisted_constantWell]

theorem sum_six (f : Fin 6 → ℝ) :
    ∑ i : Fin 6, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + f 5)))) = _
  ring

theorem energy_expansion (τ : Twist) (q : State) :
    energy τ q =
      (localPotential (q 0) + localPotential (q 1) + localPotential (q 2) +
        localPotential (q 3) + localPotential (q 4) + localPotential (q 5)) +
      (edgeEnergy τ q 0 + edgeEnergy τ q 1 + edgeEnergy τ q 2 +
        edgeEnergy τ q 3 + edgeEnergy τ q 4 + edgeEnergy τ q 5) := by
  unfold energy
  rw [sum_six, sum_six]

/-- The two oppositely signed parallel edges force positive energy even
when all four outer vertices are left unconstrained. -/
theorem middle_energy_decomposition (q : State) :
    localPotential (q 4) + localPotential (q 5) +
        edgeEnergy flipped q 2 + edgeEnergy flipped q 3 =
      1 / 2 + (q 4).1 ^ 4 / 4 + (q 5).1 ^ 4 / 4 +
        ((q 4).1 ^ 2 + (q 5).1 ^ 2) / 2 +
        ((q 4).2 - Real.sqrt 2 * (q 4).1) ^ 2 / 2 +
        ((q 5).2 - Real.sqrt 2 * (q 5).1) ^ 2 / 2 +
        (q 4).2 ^ 2 + (q 5).2 ^ 2 := by
  change ((q 4).1 ^ 2 - 1) ^ 2 / 4 +
      ((q 4).2 - Real.sqrt 2 * (q 4).1) ^ 2 / 2 +
      (((q 5).1 ^ 2 - 1) ^ 2 / 4 +
        ((q 5).2 - Real.sqrt 2 * (q 5).1) ^ 2 / 2) +
      (((q 4).1 - 1 * (q 5).1) ^ 2 + ((q 4).2 - 1 * (q 5).2) ^ 2) / 2 +
      (((q 4).1 - (-1) * (q 5).1) ^ 2 + ((q 4).2 - (-1) * (q 5).2) ^ 2) / 2 = _
  ring

theorem middle_energy_lower_bound (q : State) :
    1 / 2 ≤ localPotential (q 4) + localPotential (q 5) +
      edgeEnergy flipped q 2 + edgeEnergy flipped q 3 := by
  rw [middle_energy_decomposition]
  have h4 := sq_nonneg ((q 4).1 ^ 2)
  have h5 := sq_nonneg ((q 5).1 ^ 2)
  nlinarith [sq_nonneg (q 4).1, sq_nonneg (q 5).1,
    sq_nonneg ((q 4).2 - Real.sqrt 2 * (q 4).1),
    sq_nonneg ((q 5).2 - Real.sqrt 2 * (q 5).1),
    sq_nonneg (q 4).2, sq_nonneg (q 5).2]

/-- A uniform lower bound, not a claim that the infimum equals 1/2. -/
theorem energy_flipped_lower_bound (q : State) : 1 / 2 ≤ energy flipped q := by
  rw [energy_expansion]
  have h := middle_energy_lower_bound q
  have h0 := localPotential_nonneg (q 0)
  have h1 := localPotential_nonneg (q 1)
  have h2 := localPotential_nonneg (q 2)
  have h3 := localPotential_nonneg (q 3)
  have e0 := edgeEnergy_nonneg flipped q 0
  have e1 := edgeEnergy_nonneg flipped q 1
  have e4 := edgeEnergy_nonneg flipped q 4
  have e5 := edgeEnergy_nonneg flipped q 5
  linarith

theorem energy_flipped_pos (q : State) : 0 < energy flipped q := by
  have h := energy_flipped_lower_bound q
  linarith

theorem energy_flipped_ne_zero (q : State) : energy flipped q ≠ 0 :=
  ne_of_gt (energy_flipped_pos q)

theorem edgeEnergy_flip_difference (q : State) (e : Fin 6) :
    edgeEnergy flipped q e - edgeEnergy untwisted q e =
      if e = 3 then 2 * ((q 4).1 * (q 5).1 + (q 4).2 * (q 5).2) else 0 := by
  by_cases h : e = 3
  · subst e
    simp only [ite_true]
    change
      (((q 4).1 - (-1) * (q 5).1) ^ 2 + ((q 4).2 - (-1) * (q 5).2) ^ 2) / 2 -
      (((q 4).1 - 1 * (q 5).1) ^ 2 + ((q 4).2 - 1 * (q 5).2) ^ 2) / 2 = _
    ring
  · simp only [edgeEnergy, sign_flipped_of_ne e h, sign_untwisted, h, if_false,
      sub_self]

/-- Change of the energy at a fixed state when only edge 3 is flipped.
There is no universal direction of energy change under this switch. -/
theorem flip_energy_jump (q : State) :
    energy flipped q - energy untwisted q =
      2 * ((q 4).1 * (q 5).1 + (q 4).2 * (q 5).2) := by
  simp only [energy, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib,
    edgeEnergy_flip_difference]
  simp

theorem flip_can_increase_energy :
    ∃ q : State, energy flipped q - energy untwisted q = 2 := by
  refine ⟨fun _ => (1, 0), ?_⟩
  rw [flip_energy_jump]
  norm_num

theorem flip_can_decrease_energy :
    ∃ q : State, energy flipped q - energy untwisted q = -2 := by
  refine ⟨fun v => if v = 5 then (-1, 0) else (1, 0), ?_⟩
  rw [flip_energy_jump]
  norm_num [Fin.ext_iff]

end LinearInputLaaksoSignedEnergy

end
