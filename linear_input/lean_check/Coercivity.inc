import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.MetricSpace.ProperSpace.Real
import Mathlib.Tactic.Continuity

/-!
For every fixed input, the actual quartic energy has compact sublevels and
attains a global minimum. The coercivity estimate is derived algebraically;
neither compactness nor existence of a minimizer is assumed.
-/
noncomputable section
namespace LinearInputCoercivity

open LinearInputDesign

def lowerBoundConstant (lam r u : ℝ) : ℝ := (r - 3) ^ 2 / (4 * lam) + u ^ 2 / 2

theorem continuous_energy (lam r u : ℝ) :
    Continuous (fun z : ℝ × ℝ => E lam r u z.1 z.2) := by
  unfold E f
  fun_prop

/-- An explicit sum-of-squares certificate, valid at every state. -/
theorem coercive_identity {lam : ℝ} (hlam : lam ≠ 0) (r u x y : ℝ) :
    E lam r u x y + lowerBoundConstant lam r u -
      (x ^ 2 + (y - Real.sqrt 2 * x) ^ 2 / 2) =
    (lam * x ^ 2 + r - 3) ^ 2 / (4 * lam) + (x - u) ^ 2 / 2 := by
  unfold E f lowerBoundConstant
  field_simp
  ring

theorem coercive_lower_bound {lam : ℝ} (hlam : 0 < lam) (r u x y : ℝ) :
    x ^ 2 + (y - Real.sqrt 2 * x) ^ 2 / 2 ≤
      E lam r u x y + lowerBoundConstant lam r u := by
  have hs : 0 ≤ (lam * x ^ 2 + r - 3) ^ 2 / (4 * lam) + (x - u) ^ 2 / 2 := by
    positivity
  linarith [coercive_identity (ne_of_gt hlam) r u x y]

/-- Compactness includes empty sublevels and uses no lower restriction on c. -/
theorem isCompact_sublevel {lam : ℝ} (hlam : 0 < lam) (r u c : ℝ) :
    IsCompact {z : ℝ × ℝ | E lam r u z.1 z.2 ≤ c} := by
  let R : ℝ := |c + lowerBoundConstant lam r u| + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hm : c + lowerBoundConstant lam r u ≤ R - 1 := by
    dsimp [R]
    simpa using le_abs_self (c + lowerBoundConstant lam r u)
  have hs : IsClosed {z : ℝ × ℝ | E lam r u z.1 z.2 ≤ c} :=
    isClosed_le (continuous_energy lam r u) continuous_const
  apply (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hs
  intro z hz
  change z.1 ∈ Set.Icc (-R) R ∧ z.2 ∈ Set.Icc (-(4 * R)) (4 * R)
  have hc := coercive_lower_bound hlam r u z.1 z.2
  have hx2 : z.1 ^ 2 ≤ R - 1 := by
    have hsq := sq_nonneg (z.2 - Real.sqrt 2 * z.1)
    dsimp at hz
    linarith
  have ht2 : (z.2 - Real.sqrt 2 * z.1) ^ 2 ≤ 2 * (R - 1) := by
    have hsq := sq_nonneg z.1
    dsimp at hz
    linarith
  have hx : |z.1| ≤ R := by
    have habs := sq_abs z.1
    have hsq := sq_nonneg (R - 1)
    nlinarith [sq_nonneg (|z.1| - R)]
  have ht : |z.2 - Real.sqrt 2 * z.1| ≤ 2 * R := by
    have habs := sq_abs (z.2 - Real.sqrt 2 * z.1)
    have hsq := sq_nonneg (R - 1)
    nlinarith [sq_nonneg (|z.2 - Real.sqrt 2 * z.1| - 2 * R)]
  have hsqrt : |Real.sqrt 2| ≤ 2 := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hy : |z.2| ≤ 4 * R := by
    calc
      |z.2| = |(z.2 - Real.sqrt 2 * z.1) + Real.sqrt 2 * z.1| := by ring_nf
      _ ≤ |z.2 - Real.sqrt 2 * z.1| + |Real.sqrt 2 * z.1| := abs_add_le _ _
      _ = |z.2 - Real.sqrt 2 * z.1| + |Real.sqrt 2| * |z.1| := by rw [abs_mul]
      _ ≤ 2 * R + 2 * R := add_le_add ht (mul_le_mul hsqrt hx (abs_nonneg _) (by norm_num))
      _ = 4 * R := by ring
  exact ⟨abs_le.mp hx, abs_le.mp hy⟩

theorem isCompact_band {lam : ℝ} (hlam : 0 < lam) (r u lo hi : ℝ) :
    IsCompact {z : ℝ × ℝ | lo ≤ E lam r u z.1 z.2 ∧ E lam r u z.1 z.2 ≤ hi} := by
  have hs : IsClosed {z : ℝ × ℝ | lo ≤ E lam r u z.1 z.2 ∧ E lam r u z.1 z.2 ≤ hi} :=
    (isClosed_le continuous_const (continuous_energy lam r u)).inter
      (isClosed_le (continuous_energy lam r u) continuous_const)
  exact (isCompact_sublevel hlam r u hi).of_isClosed_subset hs (fun _ hz => hz.2)

theorem exists_global_minimum {lam : ℝ} (hlam : 0 < lam) (r u : ℝ) :
    ∃ z : ℝ × ℝ, ∀ w : ℝ × ℝ, E lam r u z.1 z.2 ≤ E lam r u w.1 w.2 := by
  let S : Set (ℝ × ℝ) := {z | E lam r u z.1 z.2 ≤ E lam r u 0 0}
  have hne : S.Nonempty := ⟨(0, 0), by change E lam r u 0 0 ≤ E lam r u 0 0; exact le_refl _⟩
  obtain ⟨z, hz, hmin⟩ := (isCompact_sublevel hlam r u (E lam r u 0 0)).exists_isMinOn
    hne (continuous_energy lam r u).continuousOn
  refine ⟨z, fun w => ?_⟩
  by_cases hw : w ∈ S
  · exact hmin hw
  · exact le_trans hz (le_of_lt (lt_of_not_ge hw))

end LinearInputCoercivity
