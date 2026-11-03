/-!
# Gravitational observation kernels and minimal F0 forgetting

This supplement uses the previously proved Newton pair cocycle and the
existing F0 idempotence predicate.  We restrict the physical interpretation
to symmetric, equal-mass pairs at positions -a and +a in one dimension and
an external observer at R > |a|.

Key distinction:
* mass-only forgetting merges separations with different external potentials;
* the reflection quotient a -> |a| preserves this observer exactly;
* on the permitted domain, one observer is injective on |a|, so the reflection
  quotient is the exact observational kernel for this narrow family.

The 1/r potential is an explicit choice, not a consequence of cocycle
associativity. No arbitrary 3D inverse problem or general multipole
completeness result is claimed.
-/

noncomputable section

namespace LinearInputGravityObserver

open LinearInputGravityCocycle

/-- Potential at R from two unit masses at symmetric positions -a and +a.
This expression is algebraically defined at poles in Lean because real division
by zero is totalized; physical conclusions assume |a| < R. -/
def pairProbe (R a : ℝ) : ℝ :=
  1 / (R - a) + 1 / (R + a)

/-- Discard separation information, corresponding to keeping only total mass. -/
def massOnly (_ : ℝ) : ℝ := 0

/-- Discard only the orientation of the symmetric configuration. -/
def reflectionForget (a : ℝ) : ℝ := |a|

theorem massOnly_idempotent : LinearInputF0.Idempotent massOnly := by
  intro a
  rfl

theorem reflectionForget_idempotent :
    LinearInputF0.Idempotent reflectionForget := by
  intro a
  simp [reflectionForget]

/-- Reversing the labels/axis of a symmetric pair does not affect the probe. -/
theorem pairProbe_even (R a : ℝ) :
    pairProbe R (-a) = pairProbe R a := by
  simp only [pairProbe, sub_neg_eq_add, add_neg_eq_sub]
  ring

/-- The chosen gravity observer is compatible with the F0 reflection quotient. -/
theorem pairProbe_reflection (R a : ℝ) :
    pairProbe R (reflectionForget a) = pairProbe R a := by
  unfold reflectionForget
  rcases le_total 0 a with ha | ha
  · rw [abs_of_nonneg ha]
  · rw [abs_of_nonpos ha, pairProbe_even]

theorem pairProbe_respects_reflection (R a b : ℝ)
    (h : reflectionForget a = reflectionForget b) :
    pairProbe R a = pairProbe R b := by
  calc
    pairProbe R a = pairProbe R (reflectionForget a) :=
      (pairProbe_reflection R a).symm
    _ = pairProbe R (reflectionForget b) := by rw [h]
    _ = pairProbe R b := pairProbe_reflection R b

theorem pairProbe_zero (R : ℝ) : pairProbe R 0 = 2 / R := by
  unfold pairProbe
  ring

/-- Positivity of both denominators implies positivity of the product. -/
theorem pairProbe_denom_pos (R a : ℝ)
    (ha : 0 ≤ a) (hR : a < R) :
    0 < R ^ 2 - a ^ 2 := by
  have hleft : 0 < R - a := sub_pos.mpr hR
  have hright : 0 < R + a :=
    add_pos_of_pos_of_nonneg (lt_of_le_of_lt ha hR) ha
  nlinarith [mul_pos hleft hright]

/-- Exact rational normal form of a symmetric two-source gravity probe. -/
theorem pairProbe_rational (R a : ℝ)
    (ha : 0 ≤ a) (hR : a < R) :
    pairProbe R a = 2 * R / (R ^ 2 - a ^ 2) := by
  have hleft : R - a ≠ 0 := ne_of_gt (sub_pos.mpr hR)
  have hright : R + a ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg (lt_of_le_of_lt ha hR) ha)
  have hden : R ^ 2 - a ^ 2 ≠ 0 :=
    ne_of_gt (pairProbe_denom_pos R a ha hR)
  unfold pairProbe
  field_simp [hleft, hright, hden]
  ring

/-- A single external probe determines the nonnegative separation exactly. -/
theorem pairProbe_injective_nonneg (R a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hRa : a < R) (hRb : b < R)
    (h : pairProbe R a = pairProbe R b) : a = b := by
  rw [pairProbe_rational R a ha hRa,
      pairProbe_rational R b hb hRb] at h
  have hDa : R ^ 2 - a ^ 2 ≠ 0 :=
    ne_of_gt (pairProbe_denom_pos R a ha hRa)
  have hDb : R ^ 2 - b ^ 2 ≠ 0 :=
    ne_of_gt (pairProbe_denom_pos R b hb hRb)
  have hRpos : 0 < R := lt_of_le_of_lt ha hRa
  have hcross : (2 * R) * (R ^ 2 - b ^ 2) =
      (2 * R) * (R ^ 2 - a ^ 2) :=
    (div_eq_div_iff hDa hDb).mp h
  have hfactor : (2 * R) ≠ 0 :=
    mul_ne_zero (by norm_num) (ne_of_gt hRpos)
  have hsquares : a ^ 2 = b ^ 2 := by
    have heq : R ^ 2 - b ^ 2 = R ^ 2 - a ^ 2 :=
      (mul_left_cancel₀ hfactor hcross)
    linarith
  have hprod : (a - b) * (a + b) = 0 := by nlinarith [hsquares]
  rcases mul_eq_zero.mp hprod with hab | hab
  · linarith
  · linarith

/-- Exact kernel classification on the collision-free symmetric-pair domain. -/
theorem pairProbe_eq_iff_reflection (R a b : ℝ)
    (ha : |a| < R) (hb : |b| < R) :
    pairProbe R a = pairProbe R b ↔
      reflectionForget a = reflectionForget b := by
  constructor
  · intro h
    change |a| = |b|
    apply pairProbe_injective_nonneg R |a| |b|
      (abs_nonneg a) (abs_nonneg b) ha hb
    calc
      pairProbe R |a| = pairProbe R a := pairProbe_reflection R a
      _ = pairProbe R b := h
      _ = pairProbe R |b| := (pairProbe_reflection R b).symm
  · exact pairProbe_respects_reflection R a b

/-- The earlier mass-only counterexample is literally a probe collision
between a separated pair and its zero-separation representative. -/
theorem pairProbe_massOnly_counterexample (R a : ℝ)
    (ha : 0 < a) (hR : a < R) :
    pairProbe R a ≠ pairProbe R 0 := by
  intro h
  rw [pairProbe_zero R] at h
  exact (mass_only_merger_loses_external_potential a R ha hR) h

/-- No real-valued decoder of the mass-only F0 state can reproduce every
physical probe in the family 0 <= a < R. -/
theorem no_massOnly_factorization (R : ℝ) (hR : 0 < R) :
    ¬ ∃ f : ℝ → ℝ, ∀ a : ℝ, 0 ≤ a → a < R →
      pairProbe R a = f (massOnly a) := by
  rintro ⟨f, hf⟩
  have hhalfpos : 0 < R / 2 := by linarith
  have hhalfR : R / 2 < R := by linarith
  have hzero := hf 0 (by norm_num) hR
  have hhalf := hf (R / 2) (le_of_lt hhalfpos) hhalfR
  have hfalse : pairProbe R (R / 2) = pairProbe R 0 := by
    calc
      pairProbe R (R / 2) = f (massOnly (R / 2)) := hhalf
      _ = f (massOnly 0) := rfl
      _ = pairProbe R 0 := hzero.symm
  exact (pairProbe_massOnly_counterexample R (R / 2) hhalfpos hhalfR) hfalse

/-- Exact leading correction beyond the total-mass (monopole) observer. -/
theorem pairProbe_quadrupole_identity (R a : ℝ)
    (ha : 0 ≤ a) (hR : a < R) :
    pairProbe R a - 2 / R =
      2 * a ^ 2 / (R * (R ^ 2 - a ^ 2)) := by
  rw [pairProbe_rational R a ha hR]
  have hRpos : 0 < R := lt_of_le_of_lt ha hR
  have hRne : R ≠ 0 := ne_of_gt hRpos
  have hden : R ^ 2 - a ^ 2 ≠ 0 :=
    ne_of_gt (pairProbe_denom_pos R a ha hR)
  field_simp [hRne, hden]
  ring

theorem pairProbe_quadrupole_positive (R a : ℝ)
    (ha : 0 < a) (hR : a < R) :
    0 < pairProbe R a - pairProbe R 0 := by
  rw [pairProbe_zero, pairProbe_quadrupole_identity R a (le_of_lt ha) hR]
  have hRpos : 0 < R := lt_trans ha hR
  have hden : 0 < R ^ 2 - a ^ 2 :=
    pairProbe_denom_pos R a (le_of_lt ha) hR
  exact div_pos (mul_pos (by norm_num : (0 : ℝ) < 2) (sq_pos_of_pos ha))
    (mul_pos hRpos hden)

/-- Exact first two nonzero multipole terms and a rational remainder.
This is an identity, not a proof of an arbitrary-source multipole series. -/
theorem pairProbe_two_term_expansion (R a : ℝ)
    (ha : 0 ≤ a) (hR : a < R) :
    pairProbe R a =
      2 / R + 2 * a ^ 2 / R ^ 3 +
        2 * a ^ 4 / (R ^ 3 * (R ^ 2 - a ^ 2)) := by
  rw [pairProbe_rational R a ha hR]
  have hRne : R ≠ 0 :=
    ne_of_gt (lt_of_le_of_lt ha hR)
  have hden : R ^ 2 - a ^ 2 ≠ 0 :=
    ne_of_gt (pairProbe_denom_pos R a ha hR)
  field_simp [hRne, hden]
  ring

end LinearInputGravityObserver
