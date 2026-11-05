import Mathlib

/-!
# Contest economy: distinguishability, delayed compression and exit

This module is a conditional model, not a theorem about an observed economy.
It separates objective quality from scores, resource expenditure and exit costs.
All proofs are over the reals or rationals; no unproved axioms are introduced.
-/

namespace ContestEconomy

open Finset

/-- A chosen candidate cannot improve on a normalized nonnegative-weight
baseline by more than the objective value range. The score used to choose the
candidate is intentionally arbitrary and does not enter the proof. -/
theorem selection_gain_le_gap
    {ι : Type*} [Fintype ι] (q w : ι → ℝ) (chosen : ι)
    (lower upper : ℝ)
    (hlower : ∀ i, lower ≤ q i)
    (hupper : q chosen ≤ upper)
    (hweight : ∀ i, 0 ≤ w i)
    (hnorm : ∑ i, w i = 1) :
    q chosen - ∑ i, w i * q i ≤ upper - lower := by
  have hweighted :
      (∑ i, w i * lower) ≤ ∑ i, w i * q i := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (hlower i) (hweight i)
  have hlow : (∑ i, w i * lower) = lower := by
    calc
      (∑ i, w i * lower) = (∑ i, w i) * lower := by rw [Finset.sum_mul]
      _ = lower := by rw [hnorm]; ring
  rw [hlow] at hweighted
  linarith

/-- If the selection gain cannot pay for a process cost,
the selection process has negative net additional value. -/
theorem selection_net_negative
    {gain gap cost : ℝ}
    (hgain : gain ≤ gap) (hcost : gap < cost) :
    gain - cost < 0 := by
  linarith

/-- Under the strict negative-discriminant condition a² < 4γ,
the positive successive-state ratio strictly falls:
a - γ/r < r.  This is a LOCAL step, not a global crossing theorem. -/
theorem delayed_ratio_strict_drop
    {a γ r : ℝ} (hr : 0 < r) (hdisc : a * a < 4 * γ) :
    a - γ / r < r := by
  have hquad : 0 < r * r - a * r + γ := by
    nlinarith [sq_nonneg (r - a / 2)]
  calc
    a - γ / r = (a * r - γ) / r := by
      field_simp [ne_of_gt hr]
    _ < r := (div_lt_iff₀ hr).2 (by nlinarith [hquad])

/-- A uniform finite decrement in the positive ratio, valid below a,
under the sharp negative-discriminant condition.
The decrement δ=(γ-a²/4)/a is strictly positive. -/
theorem delayed_ratio_uniform_drop
    {a γ r : ℝ} (ha : 0 < a) (hr : 0 < r) (hrle : r ≤ a)
    (hdisc : a * a < 4 * γ) :
    a - γ / r ≤ r - (γ - a * a / 4) / a := by
  have hδpos : 0 < γ - a * a / 4 := by nlinarith
  have hquad : γ - a * a / 4 ≤ r * r - a * r + γ := by
    nlinarith [sq_nonneg (r - a / 2)]
  have hscaled : ((γ - a * a / 4) / a) * r ≤ γ - a * a / 4 := by
    calc
      ((γ - a * a / 4) / a) * r
          = (γ - a * a / 4) * (r / a) := by ring
      _ ≤ (γ - a * a / 4) * 1 := by
        apply mul_le_mul_of_nonneg_left
        · exact (div_le_iff₀ ha).2 (by linarith)
        · exact le_of_lt hδpos
      _ = γ - a * a / 4 := by ring
  have hbound :
      a * r - γ + ((γ - a * a / 4) / a) * r ≤ r * r := by
    linarith
  have heq :
      a - γ / r + (γ - a * a / 4) / a =
      (a * r - γ + ((γ - a * a / 4) / a) * r) / r := by
    field_simp [ne_of_gt hr]
  have hres : a - γ / r + (γ - a * a / 4) / a ≤ r := by
    rw [heq]
    exact (div_le_iff₀ hr).2 hbound
  linarith

/-- SHARP finite-time threshold theorem. For the delayed recurrence with
z₀>0, z₁=a*z₀ and z_(n+2)=a*z_(n+1)-γ*z_n, if a>0
and a²<4γ, not all z_n can remain positive forever. -/
theorem delayed_crossing_of_negative_discriminant
    (a γ : ℝ) (ha : 0 < a) (hdisc : a * a < 4 * γ)
    (z : ℕ → ℝ) (hz₀ : 0 < z 0)
    (hz₁ : z 1 = a * z 0)
    (hrec : ∀ n : ℕ, z (n + 2) = a * z (n + 1) - γ * z n) :
    ∃ n : ℕ, z n ≤ 0 := by
  by_contra! hpos
  let r : ℕ → ℝ := fun n => z (n + 1) / z n
  have hrpos (n : ℕ) : 0 < r n := by
    exact div_pos (hpos (n + 1)) (hpos n)
  have hr₀ : r 0 = a := by
    dsimp [r]
    rw [hz₁]
    field_simp [ne_of_gt hz₀]
  have hrrec (n : ℕ) : r (n + 1) = a - γ / r n := by
    change z (n + 2) / z (n + 1) = a - γ / (z (n + 1) / z n)
    rw [hrec n]
    field_simp [ne_of_gt (hpos (n + 1)), ne_of_gt (hpos n)]
  have hγpos : 0 < γ := by
    nlinarith [sq_nonneg a]
  have hrle (n : ℕ) : r n ≤ a := by
    cases n with
    | zero => simpa only [hr₀] using (le_refl a)
    | succ n =>
        rw [hrrec n]
        have hdiv : 0 ≤ γ / r n :=
          div_nonneg (le_of_lt hγpos) (le_of_lt (hrpos n))
        linarith
  let δ : ℝ := (γ - a * a / 4) / a
  have hδ : 0 < δ := by
    dsimp [δ]
    exact div_pos (by nlinarith) ha
  have huniform (n : ℕ) : r (n + 1) ≤ r n - δ := by
    rw [hrrec n]
    change a - γ / r n ≤ r n - (γ - a * a / 4) / a
    exact delayed_ratio_uniform_drop ha (hrpos n) (hrle n) hdisc
  have hbound (n : ℕ) : r n + (n : ℝ) * δ ≤ a := by
    induction n with
    | zero => simpa [hr₀]
    | succ n ih =>
        calc
          r (n + 1) + ((n + 1 : ℕ) : ℝ) * δ
              = r (n + 1) + (n : ℝ) * δ + δ := by push_cast; ring
          _ ≤ r n + (n : ℝ) * δ := by linarith [huniform n]
          _ ≤ a := ih
  obtain ⟨N, hN⟩ := exists_nat_gt (a / δ)
  have hNprod : a < (N : ℝ) * δ :=
    (div_lt_iff₀ hδ).1 hN
  have hNbound := hbound N
  have hNpos := hrpos N
  linarith

/-- A stronger, directly finite-horizon sufficient condition for a crossing.
With z₁=a*z₀, z₂=a*z₁-γ*z₀, z₃=a*z₂-γ*z₁,
a² ≤ 2γ forces z₃ ≤ 0. It is stronger than a² < 4γ. -/
theorem delayed_third_step_nonpos
    {a γ z₀ : ℝ} (ha : 0 < a) (hz : 0 < z₀)
    (hstrong : a * a ≤ 2 * γ) :
    a * (a * (a * z₀) - γ * z₀) - γ * (a * z₀) ≤ 0 := by
  have hfactor : a * a - 2 * γ ≤ 0 := by linarith
  have hmul : (a * z₀) * (a * a - 2 * γ) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (le_of_lt (mul_pos ha hz)) hfactor
  calc
    a * (a * (a * z₀) - γ * z₀) - γ * (a * z₀)
        = (a * z₀) * (a * a - 2 * γ) := by ring
    _ ≤ 0 := hmul

/-- Exact rational example in the weaker negative-discriminant regime.
The recurrence with a=7/10, γ=3/20 stays positive at step six and
crosses at step seven. -/
theorem delayed_seventh_step_example :
    let a : ℚ := 7 / 10
    let γ : ℚ := 3 / 20
    let z₀ : ℚ := 9
    let z₁ := a * z₀
    let z₂ := a * z₁ - γ * z₀
    let z₃ := a * z₂ - γ * z₁
    let z₄ := a * z₃ - γ * z₂
    let z₅ := a * z₄ - γ * z₃
    let z₆ := a * z₅ - γ * z₄
    let z₇ := a * z₆ - γ * z₅
    0 < z₆ ∧ z₇ ≤ 0 := by
  norm_num

/-- Partial participation under a two-player symmetric interior mixture:
D>0 is objective quality gap and e=c-h is the net entry cost.
The right-hand side is truncated below at zero. -/
noncomputable def participation (D e : ℝ) : ℝ :=
  max 0 (1 - e / D)

theorem participation_zero_entry_cost (D : ℝ) :
    participation D 0 = 1 := by
  simp [participation]

theorem participation_entry_cost_equals_gap {D : ℝ} (hD : 0 < D) :
    participation D D = 0 := by
  simp [participation, ne_of_gt hD]

/-- If objective gap is at most the positive net entry cost, no one enters
in the selected symmetric equilibrium. -/
theorem participation_stops_of_gap_le_cost
    {D e : ℝ} (hD : 0 < D) (hgap : D ≤ e) :
    participation D e = 0 := by
  have hdiv : 1 ≤ e / D :=
    (le_div_iff₀ hD).2 (by linarith)
  have hnonpos : 1 - e / D ≤ 0 := by linarith
  simp [participation, max_eq_left hnonpos]

/-- Arbitrarily near (D,e)=(0,0), the two approaches e=0 and e=D
give opposite participation rates. -/
theorem participation_paths_disagree_arbitrarily_near
    {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ D < ε ∧
      participation D 0 = 1 ∧ participation D D = 0 := by
  refine ⟨ε / 2, by linarith, by linarith, ?_, ?_⟩
  · exact participation_zero_entry_cost _
  · exact participation_entry_cost_equals_gap (by linarith)

/-- The participation surface has NO common limit as D→0+ and e→0+.
This is a precise epsilon-delta contradiction, independent
of the choice of topology API or a claim about actual human behavior. -/
theorem participation_no_joint_boundary_limit :
    ¬ ∃ L : ℝ, ∀ η : ℝ, 0 < η →
      ∃ δ : ℝ, 0 < δ ∧ ∀ D e : ℝ,
        0 < D → D < δ → 0 ≤ e → e < δ →
        |participation D e - L| < η := by
  rintro ⟨L, hL⟩
  rcases hL (1 / 3) (by norm_num) with ⟨δ, hδ, hclose⟩
  let D : ℝ := δ / 2
  have hD : 0 < D := by dsimp [D]; linarith
  have hDlt : D < δ := by dsimp [D]; linarith
  have h₁ := hclose D 0 hD hDlt (le_refl (0 : ℝ)) (by linarith)
  have h₀ := hclose D D hD hDlt (le_of_lt hD) hDlt
  rw [participation_zero_entry_cost D] at h₁
  rw [participation_entry_cost_equals_gap hD] at h₀
  rcases abs_lt.mp h₁ with ⟨_, h₁hi⟩
  rcases abs_lt.mp h₀ with ⟨h₀lo, _⟩
  linarith

#print axioms ContestEconomy.selection_gain_le_gap
#print axioms ContestEconomy.delayed_ratio_strict_drop
#print axioms ContestEconomy.delayed_ratio_uniform_drop
#print axioms ContestEconomy.delayed_crossing_of_negative_discriminant
#print axioms ContestEconomy.delayed_third_step_nonpos
#print axioms ContestEconomy.delayed_seventh_step_example
#print axioms ContestEconomy.participation_no_joint_boundary_limit

end ContestEconomy
