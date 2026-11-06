import TwoWavelengthPhase

/-!
# Exact aliases and finite observation separation

An intensity channel observes a cosine, so each channel independently permits
both a full-period shift and a sign reversal.  The integer criteria below keep
all four combinations; a common synthetic period alone is insufficient.

The noise result is deterministic and conditional on a bound in normalized
output units.  It assumes neither a detector distribution nor physical memory
stability.  A finite set of tested heights is not a claim of additional stable
wells in the PR #92 energy.
-/

noncomputable section
namespace TwoWavelengthSeparation

open TwoWavelengthPhase FluidPrismPhaseMemory

/-- The two possible cosine aliases, expressed without trigonometric functions.
    The integer may be different for each optical channel. -/
def HeightAlias (r h k : ℝ) : Prop :=
  ∃ m : ℤ, r * (h - k) = 4 * (m : ℝ) ∨
    r * (h + k + 2) = 4 * (m : ℝ)

/-- Exact real-height criterion for equality of one scaled cosine. -/
theorem scaled_cos_eq_iff (r h k : ℝ) :
    Real.cos (ratioPhase r h) = Real.cos (ratioPhase r k) ↔
      HeightAlias r h k := by
  constructor
  · intro hc
    rcases Real.cos_eq_cos_iff.mp hc.symm with ⟨m, hsame | hflip⟩
    · refine ⟨m, Or.inl ?_⟩
      have hz : Real.pi * (r * (h-k) - 4 * (m : ℝ)) = 0 := by
        dsimp [ratioPhase, phase] at hsame
        linear_combination 2 * hsame
      have hz' := (mul_eq_zero.mp hz).resolve_left Real.pi_ne_zero
      linarith
    · refine ⟨m, Or.inr ?_⟩
      have hz : Real.pi * (r * (h+k+2) - 4 * (m : ℝ)) = 0 := by
        dsimp [ratioPhase, phase] at hflip
        linear_combination 2 * hflip
      have hz' := (mul_eq_zero.mp hz).resolve_left Real.pi_ne_zero
      linarith
  · rintro ⟨m, hsame | hflip⟩
    · apply Eq.symm
      apply Real.cos_eq_cos_iff.mpr
      refine ⟨m, Or.inl ?_⟩
      dsimp [ratioPhase, phase]
      linear_combination (Real.pi / 2) * hsame
    · apply Eq.symm
      apply Real.cos_eq_cos_iff.mpr
      refine ⟨m, Or.inr ?_⟩
      dsimp [ratioPhase, phase]
      linear_combination (Real.pi / 2) * hflip

theorem ratio_port_eq_iff (r h k : ℝ) :
    ratioPort r h = ratioPort r k ↔ HeightAlias r h k := by
  constructor
  · intro he
    apply (scaled_cos_eq_iff r h k).mp
    dsimp [ratioPort] at he
    linarith
  · intro ha
    have hc := (scaled_cos_eq_iff r h k).mpr ha
    dsimp [ratioPort]
    rw [hc]

theorem first_port_eq_iff (h k : ℝ) :
    firstPort h = firstPort k ↔ HeightAlias 1 h k := by
  simpa only [ratioPort, ratioPhase, one_mul, firstPort, port]
    using ratio_port_eq_iff 1 h k

/-- Necessary and sufficient collision condition.  Each of the two disjunctions
    chooses its sign independently, including mixed-sign collisions. -/
theorem observation_eq_iff (r h k : ℝ) :
    observation r h = observation r k ↔
      HeightAlias 1 h k ∧ HeightAlias r h k := by
  constructor
  · intro he
    exact ⟨(first_port_eq_iff h k).mp (congrArg Prod.fst he),
      (ratio_port_eq_iff r h k).mp (congrArg Prod.snd he)⟩
  · rintro ⟨hfirst, hsecond⟩
    exact Prod.ext ((first_port_eq_iff h k).mpr hfirst)
      ((ratio_port_eq_iff r h k).mpr hsecond)

/-- For any chosen state set, avoiding simultaneous integer aliases is exactly
    the condition for injectivity.  No finiteness assumption is needed. -/
theorem observation_injOn_iff (r : ℝ) (S : Set ℝ) :
    Set.InjOn (observation r) S ↔
      ∀ h ∈ S, ∀ k ∈ S, h ≠ k →
        ¬ (HeightAlias 1 h k ∧ HeightAlias r h k) := by
  constructor
  · intro hinj h hh k hk hne ha
    exact hne (hinj hh hk ((observation_eq_iff r h k).mpr ha))
  · intro hsep h hh k hk he
    by_contra hne
    exact hsep h hh k hk hne ((observation_eq_iff r h k).mp he)

/-- A finite height alphabet can be checked by the preceding integer criterion
    for every pair; its subtype observation is then injective. -/
theorem finite_alphabet_injective (r : ℝ) (S : Finset ℝ)
    (hsep : ∀ h ∈ S, ∀ k ∈ S, h ≠ k →
      ¬ (HeightAlias 1 h k ∧ HeightAlias r h k)) :
    Function.Injective (fun x : {h : ℝ // h ∈ S} => observation r x.val) := by
  intro x y he
  apply Subtype.ext
  by_contra hne
  exact hsep x.val x.property y.val y.property hne
    ((observation_eq_iff r x.val y.val).mp he)

/-- A mixed-sign collision inside a single common period.  It is neither an
    eight-unit translation nor a global reflection about h=-1. -/
theorem mixed_sign_alias :
    idealObservation (-1/3) = idealObservation (7/3) := by
  change observation (3/2) (-1/3) = observation (3/2) (7/3)
  apply (observation_eq_iff (3/2) (-1/3) (7/3)).mpr
  constructor
  · exact ⟨1, Or.inr (by norm_num)⟩
  · exact ⟨-1, Or.inl (by norm_num)⟩

theorem mixed_sign_heights_distinct : (-1/3 : ℝ) ≠ 7/3 := by norm_num

/-- Consequently even this four-unit continuous height interval is ambiguous.
    This does not contradict injectivity of a selected finite alphabet. -/
theorem not_injective_on_four_unit_interval :
    ¬ Set.InjOn idealObservation (Set.Icc (-1) 3) := by
  intro hinj
  apply mixed_sign_heights_distinct
  exact hinj (by constructor <;> norm_num)
    (by constructor <;> norm_num) mixed_sign_alias

/-- The ideal output separation in the coordinatewise bounded-error norm. -/
def outputGap (r h k : ℝ) : ℝ :=
  max (|firstPort h - firstPort k|) (|ratioPort r h - ratioPort r k|)

/-- A measured pair with at most epsilon error in each normalized channel. -/
def BoundedReadout (r epsilon h : ℝ) (y : ℝ × ℝ) : Prop :=
  |y.1 - firstPort h| ≤ epsilon ∧ |y.2 - ratioPort r h| ≤ epsilon

/-- A single measured pair cannot be compatible with two states whose ideal
    output gap is strictly greater than twice the per-channel error bound. -/
theorem bounded_noise_disjoint (r epsilon h k : ℝ)
    (hgap : 2 * epsilon < outputGap r h k) (y : ℝ × ℝ) :
    ¬ (BoundedReadout r epsilon h y ∧ BoundedReadout r epsilon k y) := by
  rintro ⟨hyh, hyk⟩
  have hfirst : |firstPort h - firstPort k| ≤ 2 * epsilon := by
    calc
      |firstPort h - firstPort k| =
          |(firstPort h - y.1) + (y.1 - firstPort k)| := by congr 1; ring
      _ ≤ |firstPort h - y.1| + |y.1 - firstPort k| := abs_add _ _
      _ = |y.1 - firstPort h| + |y.1 - firstPort k| := by
        rw [abs_sub_comm (firstPort h) y.1]
      _ ≤ epsilon + epsilon := add_le_add hyh.1 hyk.1
      _ = 2 * epsilon := by ring
  have hsecond : |ratioPort r h - ratioPort r k| ≤ 2 * epsilon := by
    calc
      |ratioPort r h - ratioPort r k| =
          |(ratioPort r h - y.2) + (y.2 - ratioPort r k)| := by congr 1; ring
      _ ≤ |ratioPort r h - y.2| + |y.2 - ratioPort r k| := abs_add _ _
      _ = |y.2 - ratioPort r h| + |y.2 - ratioPort r k| := by
        rw [abs_sub_comm (ratioPort r h) y.2]
      _ ≤ epsilon + epsilon := add_le_add hyh.2 hyk.2
      _ = 2 * epsilon := by ring
  have hle : outputGap r h k ≤ 2 * epsilon := max_le hfirst hsecond
  linarith

end TwoWavelengthSeparation
