/-!
Finite-temperature partition functions for a nonempty finite set of real energies.
The minimum is defined by the finite infimum, not assumed. Zero temperature here
means beta tending to infinity for one fixed finite family; no long-word or
spectral-radius limit is asserted.
-/

noncomputable section

namespace LinearInputCurveWordThermodynamics

open scoped BigOperators
open Filter

variable {ι : Type*}

def minimum (S : Finset ι) (hS : S.Nonempty) (E : ι → ℝ) : ℝ :=
  S.inf' hS E

def partition (S : Finset ι) (E : ι → ℝ) (β : ℝ) : ℝ :=
  ∑ w ∈ S, Real.exp (-β * E w)

def freeEnergy (S : Finset ι) (E : ι → ℝ) (β : ℝ) : ℝ :=
  -Real.log (partition S E β) / β

theorem minimum_le (S : Finset ι) (hS : S.Nonempty) (E : ι → ℝ)
    {w : ι} (hw : w ∈ S) : minimum S hS E ≤ E w := by
  exact Finset.inf'_le E hw

theorem minimum_attained (S : Finset ι) (hS : S.Nonempty) (E : ι → ℝ) :
    ∃ w ∈ S, E w = minimum S hS E := by
  obtain ⟨w, hw, he⟩ := (Finset.inf'_le_iff hS).mp (le_refl (S.inf' hS E))
  exact ⟨w, hw, le_antisymm he (minimum_le S hS E hw)⟩

theorem partition_positive (S : Finset ι) (hS : S.Nonempty) (E : ι → ℝ) (β : ℝ) :
    0 < partition S E β := by
  apply Finset.sum_pos
  · intro w _
    exact Real.exp_pos _
  · exact hS

theorem minimum_weight_le_partition (S : Finset ι) (hS : S.Nonempty)
    (E : ι → ℝ) (β : ℝ) :
    Real.exp (-β * minimum S hS E) ≤ partition S E β := by
  obtain ⟨w, hw, he⟩ := minimum_attained S hS E
  rw [← he]
  exact Finset.single_le_sum (fun i _ => (Real.exp_pos (-β * E i)).le) hw

theorem partition_le_card_minimum_weight (S : Finset ι) (hS : S.Nonempty)
    (E : ι → ℝ) {β : ℝ} (hβ : 0 ≤ β) :
    partition S E β ≤ (S.card : ℝ) * Real.exp (-β * minimum S hS E) := by
  calc
    partition S E β ≤ ∑ _w ∈ S, Real.exp (-β * minimum S hS E) := by
      apply Finset.sum_le_sum
      intro w hw
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left (minimum_le S hS E hw) (neg_nonpos.mpr hβ)
    _ = (S.card : ℝ) * Real.exp (-β * minimum S hS E) := by simp

theorem freeEnergy_le_minimum (S : Finset ι) (hS : S.Nonempty)
    (E : ι → ℝ) {β : ℝ} (hβ : 0 < β) :
    freeEnergy S E β ≤ minimum S hS E := by
  have hh := Real.log_le_log (Real.exp_pos (-β * minimum S hS E))
    (minimum_weight_le_partition S hS E β)
  rw [Real.log_exp] at hh
  apply (div_le_iff₀ hβ).mpr
  nlinarith

theorem minimum_sub_entropy_le_freeEnergy (S : Finset ι) (hS : S.Nonempty)
    (E : ι → ℝ) {β : ℝ} (hβ : 0 < β) :
    minimum S hS E - Real.log (S.card : ℝ) / β ≤ freeEnergy S E β := by
  have hc : 0 < (S.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hS)
  have hh := Real.log_le_log (partition_positive S hS E β)
    (partition_le_card_minimum_weight S hS E hβ.le)
  rw [Real.log_mul hc.ne' (Real.exp_ne_zero _), Real.log_exp] at hh
  dsimp [freeEnergy]
  apply (le_div_iff₀ hβ).mpr
  have hβ0 := hβ.ne'
  field_simp
  nlinarith

theorem freeEnergy_bounds (S : Finset ι) (hS : S.Nonempty)
    (E : ι → ℝ) {β : ℝ} (hβ : 0 < β) :
    minimum S hS E - Real.log (S.card : ℝ) / β ≤ freeEnergy S E β ∧
      freeEnergy S E β ≤ minimum S hS E :=
  ⟨minimum_sub_entropy_le_freeEnergy S hS E hβ,
    freeEnergy_le_minimum S hS E hβ⟩

theorem freeEnergy_tendsto_minimum (S : Finset ι) (hS : S.Nonempty) (E : ι → ℝ) :
    Tendsto (freeEnergy S E) atTop (nhds (minimum S hS E)) := by
  have ht : Tendsto (fun β : ℝ => Real.log (S.card : ℝ) / β) atTop (nhds 0) :=
    tendsto_id.const_div_atTop _
  have hl : Tendsto (fun β : ℝ => minimum S hS E - Real.log (S.card : ℝ) / β)
      atTop (nhds (minimum S hS E)) := by
    simpa using tendsto_const_nhds.sub ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with β hβ
    exact minimum_sub_entropy_le_freeEnergy S hS E hβ
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with β hβ
    exact freeEnergy_le_minimum S hS E hβ


theorem freeEnergy_error_bound (S : Finset ι) (hS : S.Nonempty)
    (E : ι → ℝ) {β : ℝ} (hβ : 0 < β) :
    |freeEnergy S E β - minimum S hS E| ≤ Real.log (S.card : ℝ) / β := by
  rw [abs_of_nonpos (sub_nonpos.mpr (freeEnergy_le_minimum S hS E hβ))]
  linarith [minimum_sub_entropy_le_freeEnergy S hS E hβ]

/-- Rescaling every energy is exactly an inverse rescaling of beta. -/
theorem partition_scaled_energy (S : Finset ι) (E : ι → ℝ) (β σ : ℝ) :
    partition S (fun w => E w / σ) β = partition S E (β / σ) := by
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  ring

theorem freeEnergy_scaled_energy (S : Finset ι) (E : ι → ℝ) (β σ : ℝ)
    (hβ : β ≠ 0) (hσ : σ ≠ 0) :
    freeEnergy S (fun w => E w / σ) β = freeEnergy S E (β / σ) / σ := by
  dsimp only [freeEnergy]
  rw [partition_scaled_energy]
  field_simp

/-- Apply the proved state-energy similarity law without identifying states with curves. -/
theorem partition_scale_states (S : Finset ι)
    (s : ι → LinearInputCurveWordAlgebra.State) (u : ℝ × ℝ) (β σ : ℝ)
    (hσ : σ ≠ 0) :
    partition S
      (fun w => LinearInputCurveWordAlgebra.linearEnergy u
        (LinearInputCurveWordAlgebra.scale σ (s w))) β =
    partition S
      (fun w => LinearInputCurveWordAlgebra.linearEnergy (σ ^ 2 * u.1, σ ^ 2 * u.2)
        (s w)) (β / σ) := by
  simp_rw [LinearInputCurveWordAlgebra.linearEnergy_scale σ hσ]
  exact partition_scaled_energy S _ β σ

theorem freeEnergy_scale_states (S : Finset ι)
    (s : ι → LinearInputCurveWordAlgebra.State) (u : ℝ × ℝ) (β σ : ℝ)
    (hβ : β ≠ 0) (hσ : σ ≠ 0) :
    freeEnergy S
      (fun w => LinearInputCurveWordAlgebra.linearEnergy u
        (LinearInputCurveWordAlgebra.scale σ (s w))) β =
    freeEnergy S
      (fun w => LinearInputCurveWordAlgebra.linearEnergy (σ ^ 2 * u.1, σ ^ 2 * u.2)
        (s w)) (β / σ) / σ := by
  simp_rw [LinearInputCurveWordAlgebra.linearEnergy_scale σ hσ]
  exact freeEnergy_scaled_energy S _ β σ hβ hσ

/-- The mass at an observed endpoint sums the Boltzmann weights of its full fiber. -/
def endpointMass {Y : Type*} [DecidableEq Y] (S : Finset ι) (z : ι → Y)
    (F : ι → ℝ) (β : ℝ) (y : Y) : ℝ :=
  ∑ w ∈ S.filter (fun w => z w = y), Real.exp (-β * F w)

theorem endpointMass_nonneg {Y : Type*} [DecidableEq Y] (S : Finset ι)
    (z : ι → Y) (F : ι → ℝ) (β : ℝ) (y : Y) :
    0 ≤ endpointMass S z F β y := by
  exact Finset.sum_nonneg (fun w _ => (Real.exp_pos (-β * F w)).le)

/-- Multiplicity is available when the common cost is specified and known. -/
theorem endpointMass_common_cost {Y : Type*} [DecidableEq Y] (S : Finset ι)
    (z : ι → Y) (F : ι → ℝ) (β c : ℝ) (y : Y)
    (hF : ∀ w ∈ S, F w = c) :
    endpointMass S z F β y =
      ((S.filter (fun w => z w = y)).card : ℝ) * Real.exp (-β * c) := by
  calc
    endpointMass S z F β y =
        ∑ _w ∈ S.filter (fun w => z w = y), Real.exp (-β * c) := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [hF w (Finset.mem_filter.mp hw).1]
    _ = _ := by simp

theorem multiplicity_from_common_cost_mass {Y : Type*} [DecidableEq Y] (S : Finset ι)
    (z : ι → Y) (F : ι → ℝ) (β c : ℝ) (y : Y)
    (hF : ∀ w ∈ S, F w = c) :
    ((S.filter (fun w => z w = y)).card : ℝ) =
      Real.exp (β * c) * endpointMass S z F β y := by
  rw [endpointMass_common_cost S z F β c y hF]
  symm
  calc
    Real.exp (β * c) *
        (((S.filter (fun w => z w = y)).card : ℝ) * Real.exp (-β * c)) =
      ((S.filter (fun w => z w = y)).card : ℝ) *
        (Real.exp (β * c) * Real.exp (-β * c)) := by ring
    _ = _ := by rw [← Real.exp_add]; simp

end LinearInputCurveWordThermodynamics
