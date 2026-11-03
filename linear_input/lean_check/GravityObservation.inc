/-!
# Gravity observability, F0 fibers and exact finite multipole expansions

This supplements GravityCocycle.inc, not a substitute for its chosen Newton
kernel. The field here is the positive one-dimensional inverse-distance sum,
without -G; multiply it by -G to obtain Newton's scalar potential.

No infinite expansion or inverse-square characterization is assumed.
The finite Taylor identity has an exact remainder and requires R != 0 and
no sample location at R. No theorem here recovers arbitrary source labels
from a finite number of moments.
-/

noncomputable section

namespace LinearInputGravityObservation

open Finset

/-- A family of observations can be read using a reduced state K(s). -/
def ObservableThrough {S Q : Type*} (K : S → S) (O : S → Q → ℝ) : Prop :=
  ∃ decoded : S → Q → ℝ, ∀ s q, O s q = decoded (K s) q

/-- Exact necessary and sufficient criterion for observational descent along
an idempotent forgetting map. This is the same F0 hypothesis in the existing
primitive-lean source. -/
theorem observable_through_iff_fibers {S Q : Type*}
    (K : S → S) (O : S → Q → ℝ)
    (hK : ∀ s, K (K s) = K s) :
    ObservableThrough K O ↔
      ∀ s t, K s = K t → ∀ q, O s q = O t q := by
  constructor
  · rintro ⟨decoded, hd⟩ s t heq q
    rw [hd s q, hd t q, heq]
  · intro h
    refine ⟨O, ?_⟩
    intro s q
    exact h s (K s) (hK s).symm q

/-- Inverse-distance scalar observation on the positive orientation of the
line, before multiplying by the gravitational constant and its minus sign. -/
def externalObservation {ι : Type*} (mass pos : ι → ℝ)
    (A : Finset ι) (R : ℝ) : ℝ :=
  ∑ i ∈ A, mass i / (R - pos i)

/-- Mass-weighted raw moment about coordinate origin 0. -/
def moment {ι : Type*} (mass pos : ι → ℝ)
    (A : Finset ι) (n : ℕ) : ℝ :=
  ∑ i ∈ A, mass i * (pos i) ^ n

theorem moment_zero {ι : Type*} (mass pos : ι → ℝ)
    (A : Finset ι) :
    moment mass pos A 0 = ∑ i ∈ A, mass i := by
  simp [moment]

theorem moment_one {ι : Type*} (mass pos : ι → ℝ)
    (A : Finset ι) :
    moment mass pos A 1 = ∑ i ∈ A, mass i * pos i := by
  simp [moment]

theorem moment_two {ι : Type*} (mass pos : ι → ℝ)
    (A : Finset ι) :
    moment mass pos A 2 = ∑ i ∈ A, mass i * (pos i) ^ 2 := by
  rfl

/-- The exact third-order finite expansion, not an asymptotic statement. -/
theorem inverse_distance_exact_three
    (R x : ℝ) (hR : R ≠ 0) (hx : R - x ≠ 0) :
    1 / (R - x) =
      1 / R + x / R ^ 2 + x ^ 2 / R ^ 3 +
        x ^ 3 / (R ^ 3 * (R - x)) := by
  field_simp [hR, hx]
  ring

/-- Exact finite multipole hierarchy, with a remainder at every source. -/
theorem external_observation_moments_three {ι : Type*}
    (mass pos : ι → ℝ) (A : Finset ι) (R : ℝ)
    (hR : R ≠ 0) (hsep : ∀ i ∈ A, R - pos i ≠ 0) :
    externalObservation mass pos A R =
      moment mass pos A 0 / R +
      moment mass pos A 1 / R ^ 2 +
      moment mass pos A 2 / R ^ 3 +
      (∑ i ∈ A, mass i * (pos i) ^ 3 /
        (R ^ 3 * (R - pos i))) := by
  unfold externalObservation
  have hterms :
      (∑ i ∈ A, mass i / (R - pos i)) =
        ∑ i ∈ A, (mass i / R +
          mass i * pos i / R ^ 2 +
          mass i * (pos i) ^ 2 / R ^ 3 +
          mass i * (pos i) ^ 3 / (R ^ 3 * (R - pos i))) := by
    apply Finset.sum_congr rfl
    intro i hi
    field_simp [hR, hsep i hi]
    ring
  rw [hterms]
  simp only [moment, pow_zero, pow_one, mul_one,
    Finset.sum_add_distrib, Finset.sum_div]

/-- If the first three moments agree, the exact field difference is solely
the difference of third-order remainders. No infinite-series limits are used. -/
theorem matching_moments_leave_remainder {ι : Type*}
    (mass pos : ι → ℝ) (A B : Finset ι) (R : ℝ)
    (hR : R ≠ 0)
    (hA : ∀ i ∈ A, R - pos i ≠ 0)
    (hB : ∀ i ∈ B, R - pos i ≠ 0)
    (hm : ∀ k : ℕ, k < 3 → moment mass pos A k = moment mass pos B k) :
    externalObservation mass pos A R -
      externalObservation mass pos B R =
        (∑ i ∈ A, mass i * (pos i) ^ 3 /
          (R ^ 3 * (R - pos i))) -
        (∑ i ∈ B, mass i * (pos i) ^ 3 /
          (R ^ 3 * (R - pos i))) := by
  rw [external_observation_moments_three mass pos A R hR hA,
      external_observation_moments_three mass pos B R hR hB,
      hm 0 (by norm_num), hm 1 (by norm_num), hm 2 (by norm_num)]
  ring

/-- A symmetric pair has the same total mass and center as its merged
representation, but retains its nonzero quadratic moment. -/
def symmetricPairMoment (m a : ℝ) (n : ℕ) : ℝ :=
  m * (-a) ^ n + m * a ^ n

theorem symmetric_pair_moment_zero (m a : ℝ) :
    symmetricPairMoment m a 0 = 2 * m := by
  simp [symmetricPairMoment]
  ring

theorem symmetric_pair_moment_one (m a : ℝ) :
    symmetricPairMoment m a 1 = 0 := by
  simp [symmetricPairMoment]

theorem symmetric_pair_moment_two (m a : ℝ) :
    symmetricPairMoment m a 2 = 2 * m * a ^ 2 := by
  simp [symmetricPairMoment]
  ring

/-- Exact field difference between the symmetric pair at ±a and a single
mass 2m at 0. The leading large-R behavior is proportional to R^-3. -/
theorem symmetric_pair_field_difference (m a R : ℝ)
    (ha : 0 < a) (hR : a < R) :
    m / (R - a) + m / (R + a) - 2 * m / R =
      2 * m * a ^ 2 / (R * (R ^ 2 - a ^ 2)) := by
  have hr0 : R ≠ 0 := ne_of_gt (lt_trans ha hR)
  have hleft : R - a ≠ 0 := ne_of_gt (sub_pos.mpr hR)
  have hright : R + a ≠ 0 :=
    ne_of_gt (add_pos (lt_trans ha hR) ha)
  have hquad : R ^ 2 - a ^ 2 ≠ 0 := by
    have hp : 0 < (R - a) * (R + a) :=
      mul_pos (sub_pos.mpr hR) (add_pos (lt_trans ha hR) ha)
    apply ne_of_gt
    nlinarith
  field_simp [hr0, hleft, hright, hquad]
  ring

theorem symmetric_pair_field_strictly_larger
    (m a R : ℝ) (hm : 0 < m)
    (ha : 0 < a) (hR : a < R) :
    2 * m / R < m / (R - a) + m / (R + a) := by
  have hquad : 0 < R ^ 2 - a ^ 2 := by
    have hp : 0 < (R - a) * (R + a) :=
      mul_pos (sub_pos.mpr hR) (add_pos (lt_trans ha hR) ha)
    nlinarith
  have hdiff := symmetric_pair_field_difference m a R ha hR
  have hpos : 0 < 2 * m * a ^ 2 / (R * (R ^ 2 - a ^ 2)) :=
    div_pos (by positivity) (mul_pos (lt_trans ha hR) hquad)
  linarith

/-- F0 forgets the pair-separation parameter, retaining only a single label. -/
def forgetSeparation (_ : ℝ) : ℝ := 0

theorem forget_separation_idempotent (a : ℝ) :
    forgetSeparation (forgetSeparation a) = forgetSeparation a := by
  rfl

/-- The external gravitational observation cannot factor through the
mass-only, constant F0 quotient. Reuses the previously verified exact
noncoincidence theorem from GravityCocycle.inc. -/
theorem gravity_observation_not_mass_only
    (a R : ℝ) (ha : 0 < a) (hR : a < R) :
    ¬ ObservableThrough forgetSeparation
      (fun sep (_ : PUnit) =>
        (1 : ℝ) / (R - sep) + (1 : ℝ) / (R + sep)) := by
  rintro ⟨decoded, h⟩
  have hpair :
      (1 : ℝ) / (R - a) + (1 : ℝ) / (R + a) =
        decoded 0 PUnit.unit := h a PUnit.unit
  have hmerged :
      (1 : ℝ) / R + (1 : ℝ) / R =
        decoded 0 PUnit.unit := by
    simpa using h 0 PUnit.unit
  have hbad :
      (1 : ℝ) / (R - a) + (1 : ℝ) / (R + a) = 2 / R := by
    calc
      _ = decoded 0 PUnit.unit := hpair
      _ = (1 : ℝ) / R + 1 / R := hmerged.symm
      _ = 2 / R := by ring
  exact LinearInputGravityCocycle.mass_only_merger_loses_external_potential
    a R ha hR hbad

end LinearInputGravityObservation
