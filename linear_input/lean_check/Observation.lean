import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Linear-input observations and minimizer order

This module makes no convexity or existence assumption. Observation identities
compare the same state at two inputs. The minimizer theorem assumes that the
two displayed global minimizers have already been supplied.
-/

namespace LinearInputObservation

def energy {S : Type*} (A X : S → ℝ) (u : ℝ) (z : S) : ℝ :=
  A z - u * X z

theorem input_shift {S : Type*} (A X : S → ℝ) (u v : ℝ) (z : S) :
    energy A X v z = energy A X u z - (v - u) * X z := by
  unfold energy
  ring

theorem recover_coordinate {S : Type*} (A X : S → ℝ) (u v : ℝ)
    (huv : u ≠ v) (z : S) :
    (energy A X u z - energy A X v z) / (v - u) = X z := by
  apply (div_eq_iff (sub_ne_zero.mpr (Ne.symm huv))).2
  unfold energy
  ring

theorem recover_zero_input_energy {S : Type*} (A X : S → ℝ) (u v : ℝ)
    (huv : u ≠ v) (z : S) :
    (v * energy A X u z - u * energy A X v z) / (v - u) = A z := by
  apply (div_eq_iff (sub_ne_zero.mpr (Ne.symm huv))).2
  unfold energy
  ring

theorem pair_suffices {S : Type*} (A X : S → ℝ) (z w : S)
    (hA : A z = A w) (hX : X z = X w) (u : ℝ) :
    energy A X u z = energy A X u w := by
  simp only [energy, hA, hX]

theorem all_inputs_iff_pair {S : Type*} (A X : S → ℝ) (z w : S) :
    (∀ u : ℝ, energy A X u z = energy A X u w) ↔
      A z = A w ∧ X z = X w := by
  constructor
  · intro h
    have hA : A z = A w := by simpa [energy] using h 0
    have h1 := h 1
    simp only [energy, one_mul] at h1
    exact ⟨hA, by linarith⟩
  · rintro ⟨hA, hX⟩ u
    exact pair_suffices A X z w hA hX u

theorem two_inputs_iff_pair {S : Type*} (A X : S → ℝ) (z w : S)
    (u v : ℝ) (huv : u ≠ v) :
    (energy A X u z = energy A X u w ∧
      energy A X v z = energy A X v w) ↔
      A z = A w ∧ X z = X w := by
  constructor
  · rintro ⟨hu, hv⟩
    have hX : X z = X w := by
      rw [← recover_coordinate A X u v huv z,
        ← recover_coordinate A X u v huv w, hu, hv]
    have hA : A z = A w := by
      rw [← recover_zero_input_energy A X u v huv z,
        ← recover_zero_input_energy A X u v huv w, hu, hv]
    exact ⟨hA, hX⟩
  · rintro ⟨hA, hX⟩
    exact ⟨pair_suffices A X z w hA hX u,
      pair_suffices A X z w hA hX v⟩

/- Any summary that permits every energy observation also permits the pair.
This is a factorization statement, not a claim about dimension or bit count. -/
theorem summary_decodes_pair {S T : Type*} (A X : S → ℝ) (summary : S → T)
    (decode : ℝ → T → ℝ)
    (hdecode : ∀ u z, decode u (summary z) = energy A X u z) :
    ∃ pairDecode : T → ℝ × ℝ,
      ∀ z, pairDecode (summary z) = (A z, X z) := by
  refine ⟨fun t => (decode 0 t, decode 0 t - decode 1 t), ?_⟩
  intro z
  simp [hdecode, energy]

theorem pair_decodes_all {S T : Type*} (A X : S → ℝ) (summary : S → T)
    (pairDecode : T → ℝ × ℝ)
    (hdecode : ∀ z, pairDecode (summary z) = (A z, X z)) :
    ∃ decode : ℝ → T → ℝ,
      ∀ u z, decode u (summary z) = energy A X u z := by
  refine ⟨fun u t => (pairDecode t).1 - u * (pairDecode t).2, ?_⟩
  intro u z
  simp only [hdecode, energy]

theorem recovery_error_identity {S : Type*} (A X : S → ℝ) (u v : ℝ)
    (huv : u ≠ v) (z : S) (errorU errorV : ℝ) :
    ((energy A X u z + errorU) - (energy A X v z + errorV)) / (v - u)
      - X z = (errorU - errorV) / (v - u) := by
  have hden : v - u ≠ 0 := sub_ne_zero.mpr (Ne.symm huv)
  unfold energy
  field_simp
  ring

theorem recovery_error_bound {S : Type*} (A X : S → ℝ) (u v : ℝ)
    (huv : u ≠ v) (z : S) (errorU errorV epsU epsV : ℝ)
    (hU : |errorU| ≤ epsU) (hV : |errorV| ≤ epsV) :
    |((energy A X u z + errorU) - (energy A X v z + errorV)) / (v - u)
      - X z| ≤ (epsU + epsV) / |v - u| := by
  rw [recovery_error_identity A X u v huv z errorU errorV, abs_div]
  apply div_le_div_of_nonneg_right _ (abs_nonneg (v - u))
  exact (abs_sub errorU errorV).trans (add_le_add hU hV)

theorem minimizer_monotone (V : ℝ → ℝ) (u v xu xv : ℝ) (huv : u < v)
    (hu : ∀ x, V xu - u * xu ≤ V x - u * x)
    (hv : ∀ x, V xv - v * xv ≤ V x - v * x) :
    xu ≤ xv := by
  have h1 := hu xv
  have h2 := hv xu
  have hprod : 0 ≤ (v - u) * (xv - xu) := by nlinarith
  by_contra h
  have hneg : xv - xu < 0 := sub_neg.mpr (lt_of_not_ge h)
  have : (v - u) * (xv - xu) < 0 :=
    mul_neg_of_pos_of_neg (sub_pos.mpr huv) hneg
  linarith

end LinearInputObservation
