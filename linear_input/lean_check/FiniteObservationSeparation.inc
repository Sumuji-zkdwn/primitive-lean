/-!
Finite observation separation: the transition or evaluation operator can remain
unchanged while adding a probe strictly refines distinguishability.

This module uses the independently verified TernaryZeroCesaro.inc definitions.
It connects:
(1) observational kernel/refinement;
(2) a finite idempotent F0-style retraction and the minimal *permitted*
    number of probes on Fin 3 (two, not one);
(3) a six-state parity/ternary coordinate system;
(4) equal zero-deleted values and final sums but different Cesaro observations.

The probe library is explicitly restricted. No unrestricted information-
theoretic lower bound or computational complexity bound is asserted.
-/

namespace LinearInputFiniteObservation

/-- Add one observation without changing the underlying state or operation. -/
def joint {α β γ : Type*} (K : α → β) (P : α → γ) (x : α) : β × γ :=
  (K x, P x)

/-- The exact observational kernel of a combined probe. -/
theorem joint_eq_iff {α β γ : Type*} (K : α → β) (P : α → γ)
    (x y : α) :
    joint K P x = joint K P y ↔ K x = K y ∧ P x = P y := by
  constructor
  · intro h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  · rintro ⟨hK, hP⟩
    exact Prod.ext hK hP

/-- The combined observation is injective exactly when its two probes
jointly separate all pairs of states. -/
theorem joint_injective_iff {α β γ : Type*} (K : α → β) (P : α → γ) :
    Function.Injective (joint K P) ↔
      ∀ x y, K x = K y → P x = P y → x = y := by
  constructor
  · intro h x y hk hp
    exact h ((joint_eq_iff K P x y).2 ⟨hk, hp⟩)
  · intro h x y hxy
    have hh := (joint_eq_iff K P x y).1 hxy
    exact h x y hh.1 hh.2

/-- A new probe separates a pair that the old probe has identified. -/
theorem strict_refinement_witness {α β γ : Type*}
    (K : α → β) (P : α → γ) (x y : α)
    (hK : K x = K y) (hP : P x ≠ P y) :
    K x = K y ∧ joint K P x ≠ joint K P y := by
  refine ⟨hK, ?_⟩
  intro h
  exact hP ((joint_eq_iff K P x y).1 h).2

/-- A probe that distinguishes an old fiber cannot be recovered from
the old observation alone: no postprocessing map can reconstruct it. -/
theorem no_factor_of_separation {α β γ : Type*}
    (K : α → β) (P : α → γ) (x y : α)
    (hK : K x = K y) (hP : P x ≠ P y) :
    ¬ ∃ f : β → γ, ∀ z, P z = f (K z) := by
  rintro ⟨f, hf⟩
  apply hP
  calc
    P x = f (K x) := hf x
    _ = f (K y) := congrArg f hK
    _ = P y := (hf y).symm

/-- A probe able to recover a distinction discarded by K cannot descend
through K by the compatibility equation P(K x)=P x. -/
theorem strict_probe_not_invariant {α γ : Type*}
    (K : α → α) (P : α → γ) (x y : α)
    (hK : K x = K y) (hP : P x ≠ P y) :
    ¬ ∀ z, P (K z) = P z := by
  intro h
  apply hP
  calc
    P x = P (K x) := (h x).symm
    _ = P (K y) := congrArg P hK
    _ = P y := h y

/-- An explicit three-state idempotent coarse-graining. -/
def coarse (x : Fin 3) : Fin 3 :=
  if x.val = 2 then 0 else x

/-- A second permitted probe reports whether the forgotten third state occurred. -/
def marker (x : Fin 3) : Fin 3 :=
  if x.val = 2 then 1 else 0

theorem coarse_idempotent (x : Fin 3) :
    coarse (coarse x) = coarse x := by
  fin_cases x <;> decide

theorem coarse_not_injective : ¬ Function.Injective coarse := by
  intro h
  have h02 : coarse (0 : Fin 3) = coarse (2 : Fin 3) := by decide
  have hbad : (0 : Fin 3) = 2 := h h02
  exact (by decide : (0 : Fin 3) ≠ 2) hbad

theorem marker_not_injective : ¬ Function.Injective marker := by
  intro h
  have h01 : marker (0 : Fin 3) = marker (1 : Fin 3) := by decide
  have hbad : (0 : Fin 3) = 1 := h h01
  exact (by decide : (0 : Fin 3) ≠ 1) hbad

/-- Neither probe alone is sufficient, but jointly they identify every state. -/
theorem coarse_marker_joint_injective :
    Function.Injective (joint coarse marker) := by
  intro x y h
  fin_cases x <;> fin_cases y <;> simp_all [joint, coarse, marker]

/-- Exactly two probes are available in this explicitly restricted library. -/
def allowedProbe (i : Fin 2) : Fin 3 → Fin 3 :=
  if i.val = 0 then coarse else marker

theorem no_single_allowed_probe (i : Fin 2) :
    ¬ Function.Injective (allowedProbe i) := by
  fin_cases i
  · simpa [allowedProbe] using coarse_not_injective
  · simpa [allowedProbe] using marker_not_injective

theorem both_allowed_probes_identify :
    Function.Injective (fun x : Fin 3 =>
      (allowedProbe 0 x, allowedProbe 1 x)) := by
  simpa [allowedProbe, joint] using coarse_marker_joint_injective

/-- Same F0 coarse state, separable by the marker but not by processing K. -/
theorem f0_strict_observation :
    coarse (0 : Fin 3) = coarse 2 ∧
    joint coarse marker (0 : Fin 3) ≠ joint coarse marker 2 ∧
    ¬ ∃ f : Fin 3 → Fin 3, ∀ z, marker z = f (coarse z) := by
  have hK : coarse (0 : Fin 3) = coarse 2 := by decide
  have hP : marker (0 : Fin 3) ≠ marker 2 := by decide
  exact ⟨(strict_refinement_witness coarse marker 0 2 hK hP).1,
    (strict_refinement_witness coarse marker 0 2 hK hP).2,
    no_factor_of_separation coarse marker 0 2 hK hP⟩

/-- On the six parity/ternary states, neither coordinate identifies
the entire state but the ordered pair does. -/
theorem parity_not_injective :
    ¬ Function.Injective (fun x : Fin 2 × Fin 3 => x.1) := by
  intro h
  have he : ((0, 0) : Fin 2 × Fin 3) = (0, 1) := h rfl
  exact (by decide : ((0, 0) : Fin 2 × Fin 3) ≠ (0, 1)) he

theorem ternary_not_injective :
    ¬ Function.Injective (fun x : Fin 2 × Fin 3 => x.2) := by
  intro h
  have he : ((0, 0) : Fin 2 × Fin 3) = (1, 0) := h rfl
  exact (by decide : ((0, 0) : Fin 2 × Fin 3) ≠ (1, 0)) he

theorem six_coordinate_joint_injective :
    Function.Injective
      (joint (fun x : Fin 2 × Fin 3 => x.1)
        (fun x : Fin 2 × Fin 3 => x.2)) := by
  intro x y h
  exact h

theorem six_state_count :
    Fintype.card (Fin 2 × Fin 3) = 6 := by
  simp

/-- Evaluation of a two-block signed sequence. -/
def ternaryFinal (pq : Fin 3 × Fin 3) : ℤ :=
  (LinearInputTernaryZero.twoBlocks pq.1 pq.2).sum

/-- Forget the positions of zeros while preserving all ordered nonzero terms. -/
def ternaryNonzero (pq : Fin 3 × Fin 3) : List ℤ :=
  (LinearInputTernaryZero.twoBlocks pq.1 pq.2).filter (fun x => x ≠ 0)

/-- Keep the time-sensitive Cesaro observation. -/
def ternaryCesaro (pq : Fin 3 × Fin 3) : ℚ :=
  LinearInputTernaryZero.sixCesaro pq.1 pq.2

theorem ternary_final_constant (pq : Fin 3 × Fin 3) :
    ternaryFinal pq = 0 := by
  simp [ternaryFinal, LinearInputTernaryZero.twoBlocks,
    LinearInputTernaryZero.ternary_block_sum, List.sum_append]

theorem ternary_same_nonzero :
    ternaryNonzero (0, 2) = ternaryNonzero (2, 0) :=
  LinearInputTernaryZero.zero_placement_counterexample.1

theorem ternary_cesaro_distinct :
    ternaryCesaro (0, 2) ≠ ternaryCesaro (2, 0) := by
  have h := LinearInputTernaryZero.zero_placement_counterexample
  change LinearInputTernaryZero.sixCesaro 0 2 ≠
    LinearInputTernaryZero.sixCesaro 2 0
  rw [h.2.1, h.2.2]
  norm_num

/-- The original final-sum operation and the ordered nonzero data are
unchanged, yet the added time-sensitive probe strictly distinguishes. -/
theorem ternary_same_evaluation_more_observation :
    ternaryFinal (0, 2) = ternaryFinal (2, 0) ∧
    ternaryNonzero (0, 2) = ternaryNonzero (2, 0) ∧
    joint ternaryNonzero ternaryCesaro (0, 2) ≠
      joint ternaryNonzero ternaryCesaro (2, 0) := by
  refine ⟨?_, ternary_same_nonzero, ?_⟩
  · rw [ternary_final_constant, ternary_final_constant]
  · exact (strict_refinement_witness ternaryNonzero ternaryCesaro
      (0, 2) (2, 0) ternary_same_nonzero ternary_cesaro_distinct).2

/-- The Cesaro observation is impossible to reconstruct from the
zero-deleted sequence alone, despite identical final evaluations. -/
theorem ternary_cesaro_not_factor :
    ¬ ∃ f : List ℤ → ℚ, ∀ z,
      ternaryCesaro z = f (ternaryNonzero z) :=
  no_factor_of_separation ternaryNonzero ternaryCesaro (0, 2) (2, 0)
    ternary_same_nonzero ternary_cesaro_distinct

end LinearInputFiniteObservation
