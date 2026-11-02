/-!
Consequences assembled from the general support/minimum equivalence and the
existing observation results. Support assumptions supply actual global minima;
neither their existence nor convexity or continuity of V is assumed.
The derivative conclusion explicitly requires HasDerivAt at the target.
-/
noncomputable section
namespace LinearInputSupportComposition
open LinearInputObservation LinearInputMinimum

/-- Increasing the input orders any supplied supported targets. Equal targets
are allowed, including when both minima are unique. -/
theorem support_targets_monotone (V : ℝ → ℝ) (u v a b : ℝ) (huv : u < v)
    (hu : ∀ x : ℝ, u * (x - a) ≤ V x - V a)
    (hv : ∀ x : ℝ, v * (x - b) ≤ V x - V b) :
    a ≤ b := by
  exact minimizer_monotone V u v a b huv
    ((minimum_iff_support V a u).mpr hu)
    ((minimum_iff_support V b v).mpr hv)

/-- A supporting input is forced by an actual derivative at the supported
target. This does not assert that the derivative supports V globally. -/
theorem support_input_eq_derivative {V : ℝ → ℝ} {a u d : ℝ}
    (hderiv : HasDerivAt V d a)
    (hs : ∀ x : ℝ, u * (x - a) ≤ V x - V a) :
    u = d := by
  have hmin := (minimum_iff_support V a u).mpr hs
  have hm : IsMinOn (fun x : ℝ => V x - u * x) Set.univ a :=
    fun x _ => hmin x
  have hz := (hm.isLocalMin Filter.univ_mem).hasDerivAt_eq_zero
    (hderiv.sub ((hasDerivAt_id a).const_mul u))
  linarith

/-- Every convex combination of two supporting inputs supports the same
target. The conclusion is about inputs, not convexity of V. -/
theorem support_input_interpolation {V : ℝ → ℝ} {a u v t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hu : ∀ x : ℝ, u * (x - a) ≤ V x - V a)
    (hv : ∀ x : ℝ, v * (x - a) ≤ V x - V a) :
    ∀ x : ℝ, ((1 - t) * u + t * v) * (x - a) ≤ V x - V a := by
  intro x
  calc
    ((1 - t) * u + t * v) * (x - a) =
        (1 - t) * (u * (x - a)) + t * (v * (x - a)) := by ring
    _ ≤ (1 - t) * (V x - V a) + t * (V x - V a) :=
      add_le_add (mul_le_mul_of_nonneg_left (hu x) (sub_nonneg.mpr ht1))
        (mul_le_mul_of_nonneg_left (hv x) ht0)
    _ = V x - V a := by ring

/-- A positive weight on strict support preserves unique global minimality
through the existing strict-support criterion. The other endpoint need only
support the target non-strictly. -/
theorem unique_minimum_of_strict_support_interpolation {V : ℝ → ℝ} {a u v t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hu : ∀ x : ℝ, x ≠ a → u * (x - a) < V x - V a)
    (hv : ∀ x : ℝ, v * (x - a) ≤ V x - V a) :
    (∀ x : ℝ, energy V id ((1 - t) * u + t * v) a ≤
      energy V id ((1 - t) * u + t * v) x) ∧
    ∀ b : ℝ, (∀ x : ℝ, energy V id ((1 - t) * u + t * v) b ≤
      energy V id ((1 - t) * u + t * v) x) → b = a := by
  apply (unique_minimum_iff_strict_support V a ((1 - t) * u + t * v)).mpr
  intro x hx
  calc
    ((1 - t) * u + t * v) * (x - a) =
        (1 - t) * (u * (x - a)) + t * (v * (x - a)) := by ring
    _ < (1 - t) * (V x - V a) + t * (V x - V a) :=
      add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left (hu x hx) (sub_pos.mpr ht1))
        (mul_le_mul_of_nonneg_left (hv x) ht0)
    _ = V x - V a := by ring

/-- Two distinct inputs cannot have two distinct targets in common among
their global minimizers. The observation-pair theorem supplies the equality. -/
theorem common_support_targets_eq {V : ℝ → ℝ} {a b u v : ℝ} (huv : u ≠ v)
    (hua : ∀ x : ℝ, u * (x - a) ≤ V x - V a)
    (hub : ∀ x : ℝ, u * (x - b) ≤ V x - V b)
    (hva : ∀ x : ℝ, v * (x - a) ≤ V x - V a)
    (hvb : ∀ x : ℝ, v * (x - b) ≤ V x - V b) :
    a = b := by
  have hma := (minimum_iff_support V a u).mpr hua
  have hmb := (minimum_iff_support V b u).mpr hub
  have hna := (minimum_iff_support V a v).mpr hva
  have hnb := (minimum_iff_support V b v).mpr hvb
  have hp := (two_inputs_iff_pair V id a b u v huv).mp
    ⟨le_antisymm (hma b) (hmb a), le_antisymm (hna b) (hnb a)⟩
  exact hp.2

end LinearInputSupportComposition
