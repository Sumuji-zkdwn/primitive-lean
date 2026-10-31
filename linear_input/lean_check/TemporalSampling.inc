/-!
Temporal sampling, future equivalence, and the polynomial E rotation.

A "time" model is an explicit observation schedule sigma : Nat -> Nat.
Sampling at stride m observes the *same* deterministic U at times m*n;
it must not be confused with changing the underlying physical update.

General results:
* unrestricted future equivalence implies equivalence under any schedule;
* a surjective schedule loses no predictive information;
* all m observation phases together reconstruct every time for m>0;
* fixed-stride sampling is future-exact iff its equivalence is stable under
  one physical U step (a necessary AND sufficient condition).

Concrete E(x,u) gradient map: at zero parameters H(x,u)=(-u,x).
Reading x every step identifies the entire state; sampling only even
steps identifies just the initial x, forgetting u. The same distinction
persists under a strictly positive exp(x) intensity and WFS p=2 gauge.

No probability, topology, or continuous-time interpolation is assumed.
-/

noncomputable section

namespace LinearInputTemporalSampling

open LinearInputFutureObservation
open LinearInputEWFSDual
open LinearInputEWFSFuture

/-- Observational equality at a specified schedule of physical times. -/
def ScheduledEq {α ω : Type*} (K : α → ω) (U : α → α)
    (sigma : ℕ → ℕ) (x y : α) : Prop :=
  ∀ n : ℕ, K (U^[sigma n] x) = K (U^[sigma n] y)

/-- Equality at every time implies equality under arbitrary subsampling. -/
theorem full_implies_scheduled {α ω : Type*} (K : α → ω)
    (U : α → α) (sigma : ℕ → ℕ) {x y : α}
    (h : FutureEq K U x y) : ScheduledEq K U sigma x y := by
  intro n
  exact h (sigma n)

/-- A schedule covering every natural time preserves the entire future. -/
theorem scheduled_iff_full_of_surjective {α ω : Type*}
    (K : α → ω) (U : α → α) (sigma : ℕ → ℕ)
    (hs : Function.Surjective sigma) (x y : α) :
    ScheduledEq K U sigma x y ↔ FutureEq K U x y := by
  constructor
  · intro h t
    obtain ⟨n, hn⟩ := hs t
    rw [← hn]
    exact h n
  · exact full_implies_scheduled K U sigma

/-- Observe time indices 0,m,2m,..., retaining the original dynamics U. -/
def SampledEq {α ω : Type*} (K : α → ω) (U : α → α)
    (m : ℕ) (x y : α) : Prop :=
  ScheduledEq K U (fun n => m * n) x y

theorem full_implies_sampled {α ω : Type*}
    (K : α → ω) (U : α → α) (m : ℕ) {x y : α}
    (h : FutureEq K U x y) : SampledEq K U m x y := by
  exact full_implies_scheduled K U (fun n => m * n) h

theorem sampled_zero {α ω : Type*} {K : α → ω} {U : α → α}
    {m : ℕ} {x y : α} (h : SampledEq K U m x y) : K x = K y := by
  have h0 := h 0
  simpa only [SampledEq, ScheduledEq, Nat.mul_zero,
    Function.iterate_zero, id_eq] using h0

/-- Compatibility means any pair identified by the sampling schedule
remains identified after *one* physical update. -/
def SampleCompatible {α ω : Type*} (K : α → ω)
    (U : α → α) (m : ℕ) : Prop :=
  ∀ x y, SampledEq K U m x y →
    SampledEq K U m (U x) (U y)

/-- If this congruence holds, the apparently coarser sampled future
actually contains enough information for the entire physical future. -/
theorem sampled_complete_of_compatible {α ω : Type*}
    (K : α → ω) (U : α → α) (m : ℕ)
    (hcompatible : SampleCompatible K U m) {x y : α}
    (hxy : SampledEq K U m x y) : FutureEq K U x y := by
  have hiter : ∀ t : ℕ,
      SampledEq K U m (U^[t] x) (U^[t] y) := by
    intro t
    induction t with
    | zero =>
        simpa only [Function.iterate_zero, id_eq] using hxy
    | succ t ih =>
        simpa only [Function.iterate_succ_apply'] using
          hcompatible _ _ ih
  intro t
  exact sampled_zero (hiter t)

/-- Necessary and sufficient condition for a fixed sampling period
to be a lossless predictor of all intervening observation times. -/
theorem compatible_iff_sampled_exact {α ω : Type*}
    (K : α → ω) (U : α → α) (m : ℕ) :
    SampleCompatible K U m ↔
      ∀ x y, SampledEq K U m x y ↔ FutureEq K U x y := by
  constructor
  · intro hc x y
    exact ⟨sampled_complete_of_compatible K U m hc,
      full_implies_sampled K U m⟩
  · intro hexact x y hxy
    have hfull : FutureEq K U x y := (hexact x y).mp hxy
    exact full_implies_sampled K U m (future_step hfull)

/-- Sampling at every step is just the original future relation. -/
theorem stride_one_exact {α ω : Type*}
    (K : α → ω) (U : α → α) (x y : α) :
    SampledEq K U 1 x y ↔ FutureEq K U x y := by
  constructor
  · intro h t
    simpa only [SampledEq, ScheduledEq, one_mul] using h t
  · exact full_implies_sampled K U 1

/-- Even if a single phase loses information, all m phases together
are sufficient to reconstruct the full future for positive stride. -/
theorem every_phase_iff_full {α ω : Type*}
    (K : α → ω) (U : α → α) (m : ℕ) (hm : 0 < m)
    (x y : α) :
    (∀ j : ℕ, j < m →
      ∀ n : ℕ, K (U^[m * n + j] x) = K (U^[m * n + j] y))
      ↔ FutureEq K U x y := by
  constructor
  · intro h t
    have hj : t % m < m := Nat.mod_lt t hm
    have he := h (t % m) hj (t / m)
    have hdiv : m * (t / m) + t % m = t := by
      have hmod := Nat.mod_add_div t m
      omega
    simpa only [hdiv] using he
  · intro h j hj n
    exact h (m * n + j)

/-- A standard iteration identity connecting physical time m*n to
n applications of the block transition U^m. -/
theorem block_iterate {α : Type*} (U : α → α)
    (m n : ℕ) (x : α) :
    (U^[m])^[n] x = U^[m * n] x := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        (U^[m])^[n + 1] x = U^[m] ((U^[m])^[n] x) := by
          rw [Function.iterate_succ_apply']
        _ = U^[m] (U^[m * n] x) := by rw [ih]
        _ = U^[m + m * n] x := by rw [Function.iterate_add_apply]
        _ = U^[m * (n + 1)] x := by
          congr 1
          omega

theorem sampled_iff_block_future {α ω : Type*}
    (K : α → ω) (U : α → α) (m : ℕ) (x y : α) :
    SampledEq K U m x y ↔ FutureEq K (U^[m]) x y := by
  constructor
  · intro h n
    change K ((U^[m])^[n] x) = K ((U^[m])^[n] y)
    rw [block_iterate U m n x, block_iterate U m n y]
    exact h n
  · intro h n
    have hn := h n
    change K ((U^[m])^[n] x) = K ((U^[m])^[n] y) at hn
    rw [block_iterate U m n x, block_iterate U m n y] at hn
    exact hn

/-- Any observation that evolves autonomously under a fixed update is
predictively equivalent to its own current value (the observed dynamics
may be non-injective and need not be constant). -/
theorem factored_observation_future_iff {α ω : Type*}
    (K : α → ω) (U : α → α) (phi : ω → ω)
    (hphi : ∀ x, K (U x) = phi (K x)) (x y : α) :
    FutureEq K U x y ↔ K x = K y := by
  constructor
  · intro h
    simpa only [Function.iterate_zero, id_eq] using h 0
  · intro h n
    induction n with
    | zero =>
        simpa only [Function.iterate_zero, id_eq] using h
    | succ n ih =>
        calc
          K (U^[n + 1] x) = phi (K (U^[n] x)) := by
            rw [Function.iterate_succ_apply', hphi]
          _ = phi (K (U^[n] y)) := congrArg phi ih
          _ = K (U^[n + 1] y) := by
            rw [Function.iterate_succ_apply', hphi]

/-- For the original polynomial E at zero parameters, H is a
quarter rotation and two physical updates are central inversion. -/
def spin : (ℝ × ℝ) → (ℝ × ℝ) := H 0 0 0 0
def spinTwo : (ℝ × ℝ) → (ℝ × ℝ) := spin^[2]

theorem spinTwo_formula (z : ℝ × ℝ) :
    spinTwo z = (-z.1, -z.2) := by
  simp [spinTwo, spin, H, Function.iterate_succ_apply']

theorem spinTwo_observe (z : ℝ × ℝ) :
    observeX (spinTwo z) = -observeX z := by
  rw [spinTwo_formula]
  rfl

/-- Sampling only even physical times identifies precisely those
states with the same original x, regardless of their u values. -/
theorem spin_even_iff_same_x (z w : ℝ × ℝ) :
    SampledEq observeX spin 2 z w ↔ observeX z = observeX w := by
  have hblock := sampled_iff_block_future observeX spin 2 z w
  have hfact := factored_observation_future_iff
    observeX spinTwo (fun a : ℝ => -a) spinTwo_observe z w
  exact hblock.trans hfact

/-- Every-step observations of this SAME physical system distinguish
every original state, due to the hidden u becoming visible at time 1. -/
theorem spin_full_iff_equal (z w : ℝ × ℝ) :
    FutureEq observeX spin z w ↔ z = w := by
  exact E_x_future_iff_eq 0 0 0 0 z w

/-- A concrete witness: x-only subsampling at 2 steps loses predictive
information that is available by observing every physical step. -/
theorem spin_even_merges_but_full_distinguishes :
    SampledEq observeX spin 2 ((0 : ℝ), 0) (0, 1) ∧
      ¬ FutureEq observeX spin ((0 : ℝ), 0) (0, 1) := by
  constructor
  · exact (spin_even_iff_same_x _ _).2 rfl
  · intro h
    have he : ((0 : ℝ), 0) = (0, 1) :=
      (spin_full_iff_equal _ _).1 h
    have hu := congrArg Prod.snd he
    norm_num at hu

/-- Hence the stride-2 observational equivalence is not a congruence
for one physical update. This is the exact obstruction characterized above. -/
theorem spin_even_not_step_compatible :
    ¬ SampleCompatible observeX spin 2 := by
  intro hc
  have hs := spin_even_merges_but_full_distinguishes.1
  have hf := sampled_complete_of_compatible observeX spin 2 hc hs
  exact spin_even_merges_but_full_distinguishes.2 hf

/-- Injective observation coordinates preserve every sampled equivalence,
not just the full future relation. -/
theorem sampled_injective_gauge {α ω β : Type*}
    (K : α → ω) (U : α → α) (m : ℕ)
    (g : ω → β) (hg : Function.Injective g) (x y : α) :
    SampledEq (fun z => g (K z)) U m x y ↔ SampledEq K U m x y := by
  constructor
  · intro h n
    exact hg (h n)
  · intro h n
    exact congrArg g (h n)

/-- The WFS p=2 coordinate of the strictly positive intensity exp(x)
does NOT restore the missing odd-time u distinctions. -/
theorem spin_even_wfs_iff_same_x (z w : ℝ × ℝ) :
    SampledEq perceptualObservation spin 2 z w ↔
      observeX z = observeX w := by
  have hg : Function.Injective
      (fun r : ℝ => wfs2 (Real.exp r)) := by
    intro a b h
    exact Real.exp_injective
      (wfs2_inj_pos (Real.exp_pos a) (Real.exp_pos b) h)
  have he := sampled_injective_gauge observeX spin 2
    (fun r : ℝ => wfs2 (Real.exp r)) hg z w
  change SampledEq (fun a => wfs2 (Real.exp (observeX a)))
      spin 2 z w ↔ observeX z = observeX w
  exact he.trans (spin_even_iff_same_x z w)

/-- The exact same pair differs under every-step WFS-gauged observations
but agrees under stride-2 WFS-gauged observations. -/
theorem spin_even_wfs_merges_but_full_distinguishes :
    SampledEq perceptualObservation spin 2 ((0 : ℝ), 0) (0, 1) ∧
      ¬ FutureEq perceptualObservation spin ((0 : ℝ), 0) (0, 1) := by
  constructor
  · exact (spin_even_wfs_iff_same_x _ _).2 rfl
  · intro h
    have he := (E_wfs_future_iff_eq 0 0 0 0 _ _).1 h
    have hu := congrArg Prod.snd he
    norm_num at hu

end LinearInputTemporalSampling
